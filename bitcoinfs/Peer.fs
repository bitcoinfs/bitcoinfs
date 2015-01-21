(**
# Peers

This is the first of the tree modules that form the Peer-to-peer layer. It is also the lowest, i.e. the closest to
the network layer and the farthest from the business logic.

A peer is our side of the communication channel with a remote node of the Bitcoin network. It is responsible for
handling the encoding/decoding and the transmission of messages with a single remote node. A peer is constructed 
with a unique id and bound to single node. If the other side is not responsive or disconnects, the peer gets evicted.
The tracker Tom fires Peter. Even if Peter comes back with a response later, Tom will disregard it.

*)
module Peer

(*** hide ***)
open System
open System.Collections.Generic
open System.Net
open System.Net.Sockets
open System.Reactive.Subjects
open System.Reactive.Linq
open System.Reactive.Disposables
open System.Reactive.Concurrency
open System.Reactive.Threading.Tasks
open System.Threading
open System.Threading.Tasks
open FSharp.Control.Observable
open Org.BouncyCastle.Utilities.Encoders
open FSharpx.Choice
open FSharpx.Validation
open NodaTime
open Protocol

let defaultPort = settings.ServerPort

(**
## The state machines

A Peer goes through several steps as indicated by `PeerState`. `Closed` is its initial and final state.
`Connected` means that it has connected to a remote node but hasn't gone through the handshake (where nodes exchange
version information). A Peer is `Ready` when it can accept a command from Tom because it is not working already. Peers only
work on one thing at a time and when they work they switch to `Busy`.
![peer-states](uml/peer-state.png)
*)
type PeerState = Connected | Ready | Busy | Closed

(**
Tom keeps track of the peers as well but its view is somewhat different. It doesn't care about the details of the inner workings
of Peter, whether he has shaken hands or not. For Tom, a peer is `Allocated` when he has hired him, `Ready` or `Busy` for the same
reasons and `Free` when Tom has decided that he no longer needs Peter's services.

![tracker-peer-states](uml/tracker-peer-state.png)
*)
type TrackerPeerState = Allocated | Ready | Busy |  Free

(**
Busy/Ready states control the allocation of resources. Tom does not know exactly how much work is done by Peter. Neither does he know
the nature of the work. It is controlled by whoever requested the work. Tom's responsibility is limited to finding a peer for Bob after that
Peter and Bob talk directly. The Busy and Ready state are present in both Tom and Peter. Because they are different actors, there is no guarantee
that these states will be synchronized. If Tom marks Peter as busy and then sends a message to Peter, Peter is not yet busy since he hasn't 
received the message yet. It is normal but when Peter finishes his work and becomes available again, the reverse must happen. He must set his
state to ready before he notifies Tom otherwise Tom could send him work before he becomes ready. Essentially, because work comes from Tom, it is ok
if Tom thinks that Peter is busy when he is not, but it is bad if Tom thinks Peter is available when he is not.

![tracker-peer-seq](uml/tracker-peer-seq.png)
*)

(*** hide ***)
type GetResult<'a> = Choice<'a, exn>
let addrTopic = new Subject<Addr>()

(**
A holder for the incoming and outgoing channels from and to the remote node
*)
type PeerQueues(stream: NetworkStream) = 
    let fromPeer = new Subject<BitcoinMessage>()
    let toPeer = new Subject<BitcoinMessage>()

    interface IDisposable with
        override x.Dispose() = 
            fromPeer.Dispose()
            toPeer.Dispose()
            stream.Close()

    member x.From with get() = fromPeer
    member x.To with get() = toPeer

type IPeer =
    abstract Id: int // the unique peer id
    abstract Ready: unit -> unit // call this to mark this peer ready. Used by Bob
    abstract Bad: unit -> unit // this peer behaved badly
    abstract Target: IPEndPoint // the address of the remote node

(**
## Commands
The communication queues have to be set up before they are used and their types must be provided.
Because F# does not have forward declarations all the commands are listed here even if they are used only later. 
*)
// Commands that the Peer can receive
type PeerCommand = 
    | Open of target: IPEndPoint * tip: BlockHeader
    | OpenStream of stream: NetworkStream * remote: IPEndPoint * tip: BlockHeader
    | Handshaked
    | Execute of message: BitcoinMessage
    | GetHeaders of gh: GetHeaders * task: TaskCompletionSource<IObservable<Headers>> * IPeer
    | GetBlocks of gd: GetData * task: TaskCompletionSource<IPeer * IObservable<Block * byte[]>>
    | GetData of gd: GetData
    | SetReady
    | Close
    | Closed
    | UpdateScore of score: int

// Commands that the Tracker (Tom) can receive
type TrackerCommand = 
    | GetPeers
    | Connect of target: IPEndPoint
    | IncomingConnection of stream: NetworkStream * target: IPEndPoint
    | SetReady of id: int
    | Close of int
    | BitcoinMessage of message: BitcoinMessage
    | Command of command: PeerCommand
    | SetTip of tip: BlockHeader

// Commands for Bob
type BlockchainCommand =
    | GetBlock of InvEntry list * Subject<BitcoinMessage>
    | GetHeaders of GetHeaders * Subject<BitcoinMessage>
    | Catchup of IPeer * byte[]
    | Ping of Ping * Subject<BitcoinMessage>

// Commands for the memory pool - the transactions that haven't been confirmed yet
type MempoolCommand =
    | Revalidate of int * seq<Tx[]>
    | Tx of Tx
    | Inv of InvVector * Subject<PeerCommand>
    | GetTx of InvEntry list * Subject<BitcoinMessage>
    | Mempool of Subject<BitcoinMessage>

(**
Finally the queues themselves
*)
let blockchainIncoming = new Subject<BlockchainCommand>()
let trackerIncoming = new Subject<TrackerCommand>()
let mempoolIncoming = new Subject<MempoolCommand>()


(**
## The Peer implementation
 
### The peer's internal state 

The peer changes its command handler as it changes state. Though a common pattern in actor frameworks, I have
to emulate it because RX is not an actor framework. When an actor receives a message, a handler processes it and modifies
the actor's internal state. Optionally, the handler can change for the subsequent messages.

In the case of the peer, the command handler changes between the setup phase and the running phase, and once again during
the running phase and the teardown phase. During the first and final phases, the peer will not process user requests.
*)
type PeerData = {
    Queues: PeerQueues option
    State: PeerState
    Score: int
    CommandHandler: PeerData -> PeerCommand -> PeerData
    }

type Peer(id: int) as self = 
    let disposable = new CompositeDisposable()
    
    let mutable target: IPEndPoint = null
    let scheduler = new EventLoopScheduler() // A dedicated thread per peer but peers could share threads too

(** Peers take input from 3 distinct sources

- commands from the Tracker
- header messages from the remote node
- block messages from the remote node
*)
    let incoming = new Subject<PeerCommand>()
    let headersIncoming = new Subject<Headers>()
    let blockIncoming = new Subject<Block * byte[]>()

(** The workloop takes a network stream and continually grabs data from it and delivers them
to the Observable.
*)
    let workLoop(stream: NetworkStream) = 
        let buffer: byte[] = Array.zeroCreate 1000000 // network buffer
        let tf = new TaskFactory()
        let task() = 
            let t = 
                tf.FromAsync<byte []>(
                    (fun cb (state: obj) -> stream.BeginRead(buffer, 0, buffer.Length, cb, state)), 
                    (fun res -> 
                        let c = stream.EndRead(res)
                        if c = 0 then // When the stream is closed, the read returns 0 byte
                            raise (new SocketException())
                        buffer.[0..c-1]), 
                    null)
            t.ToObservable() // a task that grabs one read asynchronously
        Observable.Repeat<byte[]>(Observable.Defer(task)) // Keep doing the same task until the stream closes

(** Helper functions to change the state of the peer. These functions work asynchronously and can be called from
any thread.
*)
    let readyPeer() =
        incoming.OnNext(PeerCommand.SetReady)

    let closePeer() =
        incoming.OnNext(PeerCommand.Close)

    let badPeer() =
        incoming.OnNext(UpdateScore -100) // lose 100 points - the banscore is not implemented yet

(** Another helper function that sends a message out and return an empty observable. By having it as
an observable, the sending is part of the time out.
*)
    let sendMessageObs (peerQueues: PeerQueues) (message: BitcoinMessage) = 
        Observable.Defer(
            fun () -> 
                peerQueues.To.OnNext(message)
                Observable.Empty()
            )
(**
Send the message out and catch any exception due to a communication problem with the remote node.
It could have closed. The network stream has a WriteTimeOut set and will throw an exception if the message
couldn't be sent during the allocated time. At this point, if an exception is raised I close the peer because
there isn't much chance of making progress later.
*)
    let sendMessage (stream: NetworkStream) (message: BitcoinMessage)= 
        let messageBytes = message.ToByteArray()
        try
            stream.Write(messageBytes, 0, messageBytes.Length)
        with
        | e -> 
            logger.DebugF "Cannot send message to peer"
            closePeer()

(**
`processMessage` handles messages incoming from the remote node. Generally speaking, it parses the payload of the message
and routes it to the appropriate queue. 
*)
    let processMessage (peerQueues: PeerQueues) (message: BitcoinMessage) = 
        let command = message.Command
        match command with
        | "version" 
        | "verack" ->
            peerQueues.From.OnNext(message)
        | "getaddr" -> ignore()
        | "getdata" ->
            let gd = message.ParsePayload() :?> GetData
            mempoolIncoming.OnNext(GetTx (gd.Invs |> List.filter (fun inv -> inv.Type = txInvType), peerQueues.To))
            blockchainIncoming.OnNext(GetBlock (gd.Invs |> List.filter (fun inv -> inv.Type = blockInvType), peerQueues.To))
        | "getheaders" ->
            let gh = message.ParsePayload() :?> GetHeaders
            blockchainIncoming.OnNext(GetHeaders (gh, peerQueues.To))
        | "addr" -> 
            let addr = message.ParsePayload() :?> Addr
            addrTopic.OnNext(addr)
        | "headers" ->
            let headers = message.ParsePayload() :?> Headers
            headersIncoming.OnNext headers
        | "block" ->
            let block = message.ParsePayload() :?> Block
            blockIncoming.OnNext (block, message.Payload)
        | "inv" ->
            let inv = message.ParsePayload() :?> InvVector
            if inv.Invs.IsEmpty then ignore() // empty inv
            elif inv.Invs.Length > 1 || inv.Invs.[0].Type <> blockInvType then // many invs or not a block inv
                mempoolIncoming.OnNext(Inv(inv, incoming)) // send to mempool
            elif inv.Invs.Length = 1 && inv.Invs.[0].Type = blockInvType then // a block inv, send to blockchain
                logger.DebugF "Catchup requested for %d %s" id (hashToHex inv.Invs.[0].Hash)
                blockchainIncoming.OnNext(Catchup(self, inv.Invs.[0].Hash))
        | "tx" ->
            let tx = message.ParsePayload() :?> Tx
            mempoolIncoming.OnNext(Tx tx)
        | "ping" ->
            let ping = message.ParsePayload() :?> Ping // send to blockchain because tests use pings to sync with catchup
            blockchainIncoming.OnNext(BlockchainCommand.Ping(ping, peerQueues.To))
        | "mempool" ->
            let mempool = message.ParsePayload() :?> Mempool
            mempoolIncoming.OnNext(MempoolCommand.Mempool peerQueues.To)
        | _ -> ignore()

(**
`processConnection` is the handler active during connection. It replies to `Open`, `OpenStream`, `Handshake` and `Closing`.
Every handler needs to support `Closing` because it may happen at any time. The other messages are specific to the state of the peer.
*)
    let rec processConnection (data: PeerData) (command: PeerCommand): PeerData = 
        match command with
        | Open (t, tip) -> // Got a outgoing connection request
            target <- t
            logger.DebugF "Connect to %s" (target.ToString())
            let connect = 
                async {
                    let client = new Sockets.TcpClient()
                    do! Async.FromBeginEnd(
                            target, 
                            (fun (target, cb, state) -> client.BeginConnect(target.Address, target.Port, cb, state)),
                            client.EndConnect)
                    let stream = client.GetStream()
                    return OpenStream (stream, target, tip)
                    }

            // Connect to the node and bail out if it fails or the timeout expires
            Observable.Timeout(Async.AsObservable connect, connectTimeout).ObserveOn(scheduler).Subscribe(
                onNext = (fun c -> incoming.OnNext c), // If connected, grab the stream
                onError = (fun ex -> 
                    logger.DebugF "Connect failed> %A %s" t (ex.ToString())
                    closePeer())
            ) |> ignore
            data
        | OpenStream (stream, t, tip) -> // Got a stream from a successful connection (in or out)
            logger.DebugF "OpenStream %A" t
            target <- t
            stream.WriteTimeout <- int(commandTimeout.Ticks / TimeSpan.TicksPerMillisecond)
            // Setup the queues and the network to bitcoin message parser
            // Observables are created but not subscribed to, so in fact nothing is consumed from the stream yet
            let peerQueues = new PeerQueues(stream)
            let parser = new BitcoinMessageParser(workLoop(stream))
            // Subscribe the outgoing queue, it's ready to send out messages
            disposable.Add(peerQueues.To.Subscribe(onNext = (fun m -> sendMessage stream m), onError = (fun e -> closePeer())))
            disposable.Add(peerQueues)
            disposable.Add(stream)

            // Prepare and send out my version message
            let version = Version.Create(SystemClock.Instance.Now, target, NetworkAddr.MyAddress, int64(random.Next()), "Satoshi YOLO 1.0", tip.Height, 1uy)
            peerQueues.To.OnNext(new BitcoinMessage("version", version.ToByteArray()))

            // The handshake observable waits for the verack and the version response from the other side. When both parties have
            // exchanged their version/verack, it will deliver a single event "Handshaked"
            let handshakeObs = 
                peerQueues.From.ObserveOn(scheduler)
                    .Scan((false, false), fun (versionReceived: bool, verackReceived: bool) (m: BitcoinMessage) ->
                    logger.DebugF "HS> %A" m
                    match m.Command with
                    | "version" -> 
                        peerQueues.To.OnNext(new BitcoinMessage("verack", Array.empty))
                        (true, verackReceived)
                    | "verack" -> (versionReceived, true)
                    | _ -> (versionReceived, verackReceived))
                    .SkipWhile(fun (versionReceived, verackReceived) -> not versionReceived || not verackReceived)
                    .Take(1)
                    .Select(fun _ -> Handshaked)

            // Give that observable a certain time to finish
            Observable.Timeout(handshakeObs, handshakeTimeout).Subscribe(
                onNext = (fun c -> 
                    logger.DebugF "%A Handshaked" t
                    incoming.OnNext c),
                onError = (fun ex -> 
                    logger.DebugF "Handshake failed> %A %s" target (ex.ToString())
                    closePeer())
            ) |> ignore

            // Finally subscribe and start consuming the responses from the remote side
            // Any exception closes the peer
            disposable.Add(parser.BitcoinMessages.Subscribe(onNext = (fun m -> processMessage peerQueues m), onError = (fun e -> closePeer())))
            // But if it goes well, 
            { data with Queues = Some(peerQueues) }
        | Handshaked ->
            // Got the handshake, the peer is ready
            trackerIncoming.OnNext (TrackerCommand.SetReady id)
            { data with State = Connected; CommandHandler = processCommand }
        | PeerCommand.Close -> 
            logger.DebugF "Closing %A" target
            // Tell the Tracker that the peer is finished but don't leave yet. Tom will do the paperwork and 
            // give the severance package
            trackerIncoming.OnNext(TrackerCommand.Close id)
            { data with CommandHandler = processClosing }
        | _ -> 
            logger.DebugF "Ignoring %A because the peer is not connected" command
            data
(**
`processCommand is the handler for normal state. The request can be either

- For the remote node. In which case, it's simply forwarded.
- A getheader/getblock. These come from Bob and Bob wants the response directly. The message came with a `TaskCompletionSource` for
an observable. The peer creates the observable and notifies Bob of its availability.
- A request for the remote node like getdata. They come from the memory pool.
- or some state management message
*)
    and processCommand (data: PeerData) (command: PeerCommand): PeerData = 
        let peerQueues = data.Queues.Value
        match command with
        | Execute message -> 
            peerQueues.To.OnNext(message)
            data
        | PeerCommand.GetHeaders (gh, ts, _) ->
            let sendObs = sendMessageObs peerQueues (new BitcoinMessage("getheaders", gh.ToByteArray()))
            let obs = 
                Observable
                    .Timeout(sendObs.Concat(headersIncoming), commandTimeout)
            ts.SetResult(obs)
            { data with State = PeerState.Busy }
        | GetBlocks (gd, ts) ->
            let blocksPending = new HashSet<byte[]>(gd.Invs |> Seq.map(fun inv -> inv.Hash), new HashCompare())
            let sendObs = sendMessageObs peerQueues (new BitcoinMessage("getdata", gd.ToByteArray()))
            let count = blocksPending.Count
            let obs = 
                Observable
                    .Timeout(sendObs.Concat(blockIncoming), commandTimeout)
                    .Where(fun (b, _) -> blocksPending.Contains b.Header.Hash)
                    .Take(count)
            ts.SetResult(self :> IPeer, obs)
            { data with State = PeerState.Busy }
        | PeerCommand.SetReady -> 
            if data.State <> PeerState.Ready then
                trackerIncoming.OnNext (TrackerCommand.SetReady id)
            { data with State = PeerState.Ready }
        | GetData (gd) -> 
            let sendObs = sendMessageObs peerQueues (new BitcoinMessage("getdata", gd.ToByteArray()))
            Observable.Timeout(sendObs, commandTimeout).Subscribe(onNext = (fun _ -> ignore()), onError = (fun _ -> badPeer())) |> ignore
            data
        | UpdateScore score -> 
            let newData = { data with Score = data.Score + score }
            if newData.Score <= 0 then incoming.OnNext(PeerCommand.Close)
            newData
        | PeerCommand.Close -> 
            logger.DebugF "Closing %A" target
            trackerIncoming.OnNext(TrackerCommand.Close id)
            { data with CommandHandler = processClosing }
(**
Finally, `processClosing` handles the cleanup. Tom will not send further requests to this peer but there still may be 
outstanding message in the pipeline. They must be cleared gracefully otherwise someone could end up waiting for their 
result forever.
*)
    and processClosing (data: PeerData) (command: PeerCommand): PeerData =
        match command with
        | Closed -> 
            (self :> IDisposable).Dispose() // Dispose completes the queues
            { data with State = PeerState.Closed; Queues = None; CommandHandler = processConnection }
        | PeerCommand.GetHeaders (gh, ts, _) ->
            ts.SetResult(Observable.Empty())
            data
        | GetBlocks (gd, ts) ->
            ts.SetResult(self :> IPeer, Observable.Empty())
            data
        | _ -> data

    let initialState = { State = PeerState.Closed; Score = 100; Queues = None; CommandHandler = processConnection }
    let runHandler (data: PeerData) (command: PeerCommand) = 
        // logger.DebugF "PeerCommand> %A" command
        data.CommandHandler data command

    do
        disposable.Add(
            incoming
                .ObserveOn(scheduler)
                .Scan(initialState, new Func<PeerData, PeerCommand, PeerData>(runHandler))
                .Subscribe(onNext = (fun _ -> ()), onCompleted = (fun () -> 
                    scheduler.Dispose() // On completion, dispose of the final resources
                    disposable.Dispose()
                    )))

    interface IDisposable with
        member x.Dispose() = 
            incoming.OnCompleted()

    interface IPeer with
        member x.Ready() = readyPeer()
        member val Id = id with get
        member x.Target with get() = target // For diagnostics only
        member x.Bad() = ignore() // TODO: Renable badPeer()

    override x.ToString() = sprintf "Peer(%d, %A)" id target
    member x.Incoming with get() = incoming

(**
### Bootstrap from DNS

Clear peers that are older than 3h and do a DNS request to the known seed nodes if the database has less than 1000 peers
*)

let dropOldPeers() =
    let dts = DateTime.UtcNow.AddHours(-3.0)
    Db.dropOldPeers dts
    Db.resetState()

let bootstrapPeers() =
    async {
        let now = NodaTime.Instant.FromDateTimeUtc(DateTime.UtcNow)
        
        let! entry = Async.AwaitTask(Dns.GetHostEntryAsync("seed.bitnodes.io"))
        for peer in entry.AddressList do
            let addr = { Timestamp = int (now.Ticks / NodaConstants.TicksPerSecond); Address = new NetworkAddr(new IPEndPoint(peer.MapToIPv4(), defaultPort)) }
            Db.updateAddr addr
        trackerIncoming.OnNext(GetPeers)
        } |> Async.StartImmediate

let initPeers() =
    dropOldPeers()
    let peers = Db.getPeers()
    if peers.Length < 1000 then
        bootstrapPeers()
