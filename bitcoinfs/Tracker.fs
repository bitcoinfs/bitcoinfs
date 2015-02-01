(*** hide ***)
(* Copyright 2015 Hanh Huynh Huu

This file is part of F# Bitcoin.

F# Bitcoin is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation version 3 of the License.

F# Bitcoin is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
You should have received a copy of the GNU General Public License
along with F# Bitcoin; if not, write to the Free Software
Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
*)

(**
# The Tracker
*)
module Tracker

(*** hide ***)
open System
open System.Net
open System.Net.Sockets
open System.Collections.Generic
open System.IO
open System.Text
open System.Threading
open System.Reactive.Linq
open System.Reactive.Subjects
open System.Reactive.Disposables
open System.Reactive.Concurrency
open System.Threading.Tasks
open FSharpx.Option
open FSharpx.Validation
open Protocol
open Peer

(**
## State
Tom the Tracker keeps a dictionary of Peers as his active workers. Every worker is identified by a
unique id that he assigns himself. A peer is never reused. Even if he is reconnecting to the same
remote node, a new peer will be used.
*)
type PeerSlot = {
    Id: int
    Peer: Peer
    mutable State: TrackerPeerState
    }

let maxSlots = settings.MaxPeers

let mutable connectionCount = 0 // how many peers are in the connected state
let mutable seqId = 0 // current sequence id
(*** hide ***)
let disposable = new CompositeDisposable()
let scheduler = new EventLoopScheduler()

(**
## The queues

- incoming requests
- messages to send to every peer
- requests that were received but couldn't be assigned to a peer because they were all busy at the time
*)
let incomingMessage = new Subject<BitcoinMessage>()
let broadcastToPeers = new Subject<BitcoinMessage>()
let pendingMessages = new Queue<TrackerCommand>()

(** A crude unique sequence generator *)
let nextId() = 
    seqId <- seqId + 1
    seqId

(** The employee directory. The Map is persistent and thread-safe and the reassignment to `peerSlots` only happens
in a handler.
*)
let mutable peerSlots = Map.empty<int, PeerSlot>

exception InvalidTransition of TrackerPeerState * TrackerPeerState

(**
Check that the transition is valid. This should never raise an exception. It is
an assertion.
*)
let checkTransition oldState newState = 
    match (oldState, newState) with
    | (Allocated, Ready) |
        (_, Free) |
        (Ready, Busy) |
        (Busy, Ready) -> ignore()
    | other -> 
        logger.ErrorF "Invalid transition from %A to %A" oldState newState
        raise (InvalidTransition other)

let changeState id newState =
    let oldState = peerSlots.[id].State
    let peer: IPeer = peerSlots.[id].Peer :> IPeer
    logger.DebugF "State transition of peer(%d %A): %A->%A" id peer.Target oldState newState
    checkTransition oldState newState
    peerSlots.[id].State <- newState
    oldState

(** Once a peer becomes available, call this to grab a message that was put on the back burner*)
let dequeuePendingMessage() = 
    logger.DebugF "Dequeue Msgs"
    if pendingMessages.Count <> 0 then
        trackerIncoming.OnNext(pendingMessages.Dequeue())
    else
        logger.DebugF "Empty Queue"

(**
## Route a message

Every command besides `GetHeader` is treated the same way. Tom looks for an available peer and assigns
the work to him. `GetHeader` is the exception because it should stick to a given peer because Bob who initiated
the call, wants to catchup from a given node. 
*)
let assign message ps = 
    let peer = ps.Peer :> IPeer
    logger.DebugF "Assigning %A to %A" message peer.Target
    changeState ps.Id Busy |> ignore
    peer.Receive(message)

let forward (command: TrackerCommand) (message: PeerCommand) =
    match message with
        | PeerCommand.GetHeaders(_, ts, peer) -> 
            peerSlots |> Map.tryFind peer.Id
            |> Option.bind (fun ps -> Option.conditional (ps.State = Ready) ps) |> Option.map (fun ps -> assign message ps)
            |> getOrElseF (fun () -> ts.SetResult(Observable.Throw(ArgumentException("Peer busy - cannot handle command"))))
        | _ -> 
            peerSlots |> Map.tryPick(fun _ ps -> if ps.State = Ready then Some(ps) else None)
            |> Option.map (fun ps -> assign message ps)
            |> getOrElseF (fun () ->
                let freePeers = peerSlots |> Seq.filter(fun ps -> ps.Value.State = Free) |> Seq.length
                logger.DebugF "No peer available - %d dead peers" freePeers
                pendingMessages.Enqueue command // park the command for now
                )

(**
## Employment cycle of a Peer

When Tom hires a new peer, he gives a unique id and a position in his directory.
When Tom fires a peer, Tom removes the peer from his directory and looks for a replacement. 
*)
let newPeer() = 
    let openSlotId = nextId()
    peerSlots <- peerSlots.Add(openSlotId, { Id = openSlotId; Peer = new Peer(openSlotId); State = Allocated })
    let peer = peerSlots.[openSlotId].Peer
    connectionCount <- connectionCount + 1
    peer

let freePeer (id: int) =
    peerSlots |> Map.tryFind id |> Option.iter (fun ps -> 
        logger.DebugF "Freeing %A" (peerSlots.[id].Peer :> IPeer).Target
        changeState id Free |> ignore
        let peer =  ps.Peer
        connectionCount <- connectionCount - 1
        if connectionCount < maxSlots then
            Db.updateState((peer :> IPeer).Target, -1) // blackball this peer
            let newPeer = Db.getPeer() // find a new peer
            newPeer |> Option.iter (fun p -> 
                Db.updateState(p, 1)
                trackerIncoming.OnNext(Connect p))
        peerSlots <- peerSlots.Remove id
        (peer :> IPeer).Receive Closed // tell the old peer to take a hike
    )

(**
## Handling a command

`processCommand` handles 3 types of commands:

- connection requests. Either outgoing from this application or incoming
- related to the state of the peer like SetReady, Close
- commands. The last category is forwarded to a peer based on the 'amazing' routing algorithm - 
pick the first one who can do it
*)
let mutable tip = Db.readHeader (Db.readTip())
let processCommand(command: TrackerCommand) =
    logger.DebugF "TrackerCommand> %A" command
    match command with
    | SetTip t -> tip <- t
    | GetPeers -> 
        let peers = Db.getPeers()
        let cFreeSlots = maxSlots - peerSlots.Count
        for peer in peers |> Seq.truncate cFreeSlots do
            Db.updateState(peer, 1)
            trackerIncoming.OnNext(Connect peer)
    | Connect target ->
        let peer = newPeer() :> IPeer
        peer.Receive(Open(target, tip))
    | IncomingConnection (stream, target) ->
        let peer = newPeer() :> IPeer
        peer.Receive(OpenStream(stream, target, tip))
    | SetReady id ->
        peerSlots.TryFind id |> Option.iter(fun ps ->
            let peer = ps.Peer
            let oldState = changeState id Ready
            if oldState = Allocated then 
                logger.InfoF "Connected to %A" peer
                blockchainIncoming.OnNext(Catchup(peer, null)) // Disable if you want no catchup on connect
            dequeuePendingMessage()
            )
    | Close id -> 
        freePeer id
        logger.DebugF "Connection count = %d" connectionCount
    | BitcoinMessage message -> forward command (Execute message)
    | Command peerCommand -> forward command peerCommand

let processAddr (addr: Addr) =
    for a in addr.Addrs do Db.updateAddr(a)

(**
Helper functions that are called by other components. They are thread-safe and will
enqueue messages for Tom
*)
let getHeaders(gh: GetHeaders, peer: IPeer): Task<IObservable<Headers>> = 
    let ts = new TaskCompletionSource<IObservable<Headers>>()
    trackerIncoming.OnNext(Command (PeerCommand.GetHeaders (gh, ts, peer)))
    ts.Task

let getBlocks(blockHashes: seq<byte[]>): Task<IPeer * IObservable<Block * byte[]>> =
    let invHashes = 
        seq { 
            for h in blockHashes do
                yield new InvEntry(blockInvType, h) }
        |> Seq.toList
    let gd = new GetData(invHashes)
    let ts = new TaskCompletionSource<IPeer * IObservable<Block * byte[]>>()
    trackerIncoming.OnNext(Command (PeerCommand.DownloadBlocks (gd, ts)))
    ts.Task

(** Send a message to every peer that is not busy
*)
let processBroadcast (m: BitcoinMessage) = 
    for peerSlot in peerSlots do
        (peerSlot.Value.Peer :> IPeer).Receive(Execute m)

(*** hide ***)
let startTracker() =
    disposable.Add(trackerIncoming.ObserveOn(scheduler).Subscribe(processCommand))
    disposable.Add(incomingMessage.Select(fun m -> BitcoinMessage m).Subscribe(trackerIncoming))
    disposable.Add(Peer.addrTopic.ObserveOn(scheduler).Subscribe(processAddr))
    disposable.Add(broadcastToPeers.ObserveOn(scheduler).Subscribe(processBroadcast))

(** 
# Server
The server binds to the port configured in the app.config file and listens to incoming connection.
On a connection, it sends a message to Tom. At this time, there is no limit to the number of incoming connections
*)
let port = defaultPort
let ipAddress = IPAddress.Any
let endpoint = IPEndPoint(ipAddress, port)
let cts = new CancellationTokenSource()
let listener = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp)
listener.Bind(endpoint)
listener.Listen(int SocketOptionName.MaxConnections)

let rec connectLoop() = 
    async {
      let! socket = Async.FromBeginEnd(listener.BeginAccept, listener.EndAccept)
      let stream = new NetworkStream(socket)
      trackerIncoming.OnNext(TrackerCommand.IncomingConnection(stream, socket.RemoteEndPoint :?> IPEndPoint))
      return! connectLoop()
    }

let startServer() = 
    logger.InfoF "Started listening on port %d" port
    Async.Start(connectLoop(), cts.Token)

