(*** hide ***)
(* Copyright 2015 Hanh Huynh Huu

This file is part of F# Bitcoin.

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files 
(the "Software"), to deal in the Software without restriction, including without limitation the rights to use, 
copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, 
and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF 
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE 
FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, 
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)

(**
# Peers

This is the first of the two modules that form the Peer-to-peer layer. It is also the lowest, i.e. the closest to
the network layer and the farthest from the business logic.

A peer is our side of the communication channel with a remote node of the Bitcoin network. It is responsible for
encoding/decoding and the transmission of messages with a single remote node. A peer is constructed 
with a unique id and bound to single node. If the other side is not responsive or disconnects, the peer gets evicted.
The tracker Tom fires Peter. Even if Peter comes back with a response later, Tom will disregard it.

*)
module Peer

(*** hide ***)
open System
open System.IO
open System.Collections
open System.Collections.Generic
open System.Linq
open MoreLinq
open System.Net
open System.Net.Sockets
open System.Reactive.Subjects
open System.Reactive.Linq
open System.Reactive.Disposables
open System.Reactive.Concurrency
open System.Reactive.Threading.Tasks
open System.Threading
open System.Threading.Tasks
open FSharp.Control
open Org.BouncyCastle.Utilities.Encoders
open FSharpx.Choice
open FSharpx.Validation
open NodaTime
open Protocol
open Db

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
reasons as the Peter and `Free` when Tom has decided that he no longer needs Peter's services.

![tracker-peer-states](uml/tracker-peer-state.png)
*)
type TrackerPeerState = Allocated | Ready | Busy |  Free

(**
Busy/Ready states control the allocation of resources. Tom does not know exactly how much work is done by Peter. Neither does he know
the nature of the work. It is controlled by whoever requested the work, usually Bob. Tom's responsibility is limited to finding a peer for Bob after that,
Peter and Bob talk directly. 

The Busy and Ready state are present in both Tom and Peter. Because they are different actors, there is no guarantee
that these states will be synchronized. If Tom marks Peter as busy and then sends a message to Peter, Peter is not busy yet since he hasn't 
received the message yet. It is normal but when Peter finishes his work and becomes available again, the reverse must happen. He must set his
state to ready before he notifies Tom otherwise Tom could send him work before he becomes ready. Essentially, because work comes from Tom, it is ok
if Tom thinks that Peter is busy when he is not, but it is bad if Tom thinks Peter is available when he is not.

The interactions between Bob, Tom and Peter can be described by the following sequence diagram.

![tracker-peer-seq](uml/tracker-peer-seq.png)
*)

(*** hide ***)
type GetResult<'a> = Choice<'a, exn>
let addrTopic = new Subject<Addr>()

type BloomFilterUpdate =
    | UpdateNone
    | UpdateAll
    | UpdateP2PubKeyOnly

(**
A holder for the incoming and outgoing channels from and to the remote node
*)
type IPeerSend =
    abstract Receive: BitcoinMessage -> unit
    abstract Send: BitcoinMessage -> unit

type PeerQueues (stream: NetworkStream, target: IPEndPoint) = 
    let fromPeer = new Event<BitcoinMessage>()
    let toPeer = new Event<BitcoinMessage>()
    let mutable disposed = false

    interface IDisposable with
        override x.Dispose() = 
            logger.InfoF "Closing stream %A" target
            stream.Dispose()
            disposed <- true

    [<CLIEvent>]
    member x.From = fromPeer.Publish
    [<CLIEvent>]
    member x.To = toPeer.Publish

    interface IPeerSend with
        member x.Receive(message: BitcoinMessage) = if not disposed then fromPeer.Trigger message
        member x.Send(message: BitcoinMessage) = if not disposed then toPeer.Trigger message

type IPeer =
    abstract Id: int // the unique peer id
    abstract Ready: unit -> unit // call this to mark this peer ready. Used by Bob
    abstract Bad: unit -> unit // this peer behaved badly
    abstract Target: IPEndPoint // the address of the remote node
    abstract Receive: PeerCommand -> unit

(**
## Commands
The communication queues have to be set up before they are used and their types must be provided.
Because F# does not have forward declarations all the commands are listed here even if they are used only later. 
*)
// Commands that the Peer can receive
and PeerCommand = 
    | Open of target: IPEndPoint * tip: BlockHeader
    | OpenStream of stream: NetworkStream * remote: IPEndPoint * tip: BlockHeader
    | Handshaked
    | Execute of message: BitcoinMessage
    | GetHeaders of gh: GetHeaders * task: TaskCompletionSource<IObservable<Headers>> * IPeer
    | GetBlocks of gb: GetBlocks * task: TaskCompletionSource<IPeer * IObservable<InvVector>> * IPeer
    | DownloadBlocks of gd: GetData * task: TaskCompletionSource<IPeer * IObservable<Block * byte[]>>
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
    | SetVersion of id: int * version: Version

// Commands for Bob
type BlockchainCommand =
    | DownloadBlocks of InvEntry list * IPeerSend
    | GetHeaders of GetHeaders * IPeerSend
    | GetBlocks of GetBlocks * IPeerSend
    | Catchup of IPeer * byte[]
    | Ping of Ping * IPeerSend

// Commands for the memory pool - the transactions that haven't been confirmed yet
type MempoolCommand =
    | Revalidate of int * seq<Tx[]>
    | Tx of Tx
    | Inv of InvVector * IPeer
    | GetTx of InvEntry list * IPeerSend
    | Mempool of IPeerSend

(**
Finally the queues themselves
*)
let blockchainIncoming = new Subject<BlockchainCommand>()
let trackerIncoming = new Subject<TrackerCommand>()
let mempoolIncoming = new Subject<MempoolCommand>()

(**
## Support for BIP-37 (Bloom Filter)
A Bloom Filter greater helps SPV clients who want to download or synchronize with a full node but don't
want to spend bandwidth getting data unrelated to their wallets.

A client can define a filter so that the full node filters messages that are irrelevant and only
transmits transactions that match the given filter. Please refer to [BIP-37][1] for more details on this
enhancement.

Originally, I didn't plan on supporting this feature because it doesn't quite fit with the requirements of the full node.
It is more of an optimization. However, it is an important one and it is now part of the protocol standard. Pre-version 70001 full
nodes don't have to do it but later versions do.

Fortunately, I had some code related to bloom filters in the wallet part that I can reuse here.

[1]: https://en.bitcoin.it/wiki/BIP_0037
*)

// A node in the partial merkle tree
type PartialMerkleTreeNode = 
    {
    Hash: byte[]
    Include: bool // whether any descendant matches the filter
    Left: PartialMerkleTreeNode option // children are present if Include is true
    Right: PartialMerkleTreeNode option
    }
    override x.ToString() = sprintf "Hash(%s), Include=%b" (hashToHex x.Hash) x.Include

let scriptRuntime = new Script.ScriptRuntime(fun x _ -> x)
(**
Check a transaction against the bloom filter
*)
let checkTxAgainstBloomFilter (bloomFilter: BloomFilter) (updateMode: BloomFilterUpdate) (tx: Tx) =
    let matchScript (script: byte[]) = // Try to match a script with the filter
        let data = scriptRuntime.GetData script // The filter matches only on the data part of the script
        data |> Array.exists (fun d -> bloomFilter.Check d) // Match is any data item is a match
    let addOutpoint (txHash: byte[]) (iTxOut: int) = // Update the filter by adding the txOut outpoint
        let outpoint = new OutPoint(txHash, iTxOut)
        bloomFilter.Add (outpoint.ToByteArray())

    let matchTxHash = bloomFilter.Check tx.Hash
    let matchInput = // Check if there is a match among the txInputs
        seq {
            for txIn in tx.TxIns do
                let matchTxInOutpoint = bloomFilter.Check (txIn.PrevOutPoint.ToByteArray())
                let matchTxInScript = matchScript txIn.Script
                yield matchTxInOutpoint || matchTxInScript
            } |> Seq.exists id
    let matchOutput = // Check if there is a match among the txOutputs
        tx.TxOuts |> Seq.mapi (fun iTxOut txOut ->
            let script = txOut.Script
            let matchTxOut = matchScript script
            if matchTxOut then // If match, update the filter according to the updateMode
                match updateMode with
                | UpdateAll -> addOutpoint tx.Hash iTxOut // always add the outpoint
                | UpdateP2PubKeyOnly -> // add the outpoint if it's a pay2Pub or pay2Multisig. It's ok to add more than necessarily because false
                    // positives are acceptable
                    if Script.isPay2PubKey script || Script.isPay2MultiSig script then addOutpoint tx.Hash iTxOut 
                | UpdateNone -> ignore() // don't update
            matchTxOut
            ) |> Seq.exists id
    matchTxHash || matchInput || matchOutput

(**
Build a merkleblock from a given block
*)
let buildMerkleBlock (bloomFilter: BloomFilter) (updateMode: BloomFilterUpdate) (block: Block) =
    let (txs, merkletreeLeaves) = // Build the leaves of the tree
        block.Txs |> Seq.map(fun tx -> // Each leaf is a transaction
            let txMatch = checkTxAgainstBloomFilter bloomFilter updateMode tx
            (Option.conditional txMatch tx, { Hash = tx.Hash; Include = txMatch; Left = None; Right = None })
        ) |> Seq.toList |> List.unzip

    let rec makeTree (merkletreeNodes: PartialMerkleTreeNode list) = // Build the tree by merging level by level
        match merkletreeNodes with
        | [root] -> root // If single node, I am at the root
        | _ -> 
            let len = merkletreeNodes.Length
            let nodes = // Make the level contain an even number of nodes
                if len % 2 = 0 
                then merkletreeNodes
                else merkletreeNodes @ [merkletreeNodes.Last()] // duplicate the last node if uneven
            let parentNodes = // Merge nodes two by two
                (nodes |> Seq.ofList).Batch(2) |> Seq.map (fun x ->
                    let [left; right] = x |> Seq.toList
                    let includeChildren = left.Include || right.Include
                    { 
                        Hash = dsha ([left.Hash; right.Hash] |> Array.concat) // DSHA on the concat of each hash
                        Include = includeChildren
                        Left = if includeChildren then Some(left) else None // Trim the branch if both children have no match
                        Right = if includeChildren && left <> right then Some(right) else None
                    }
                ) |> Seq.toList
            makeTree parentNodes
            
    // Build the tree
    let merkleTree = makeTree merkletreeLeaves

    // Convert to MerkleBlock format
    let hashes = new List<byte[]>()
    let flags = new List<bool>()

    let rec depthFirstTraversal (node: PartialMerkleTreeNode) = // Traverse the tree down
        flags.Add(node.Include)
        if node.Left = None && node.Right = None then 
            hashes.Add(node.Hash) // Write the contents of the leaves to the output buffers
        node.Left |> Option.iter depthFirstTraversal
        node.Right |> Option.iter depthFirstTraversal

    depthFirstTraversal merkleTree
    let txHashes = hashes |> List.ofSeq
    let flags = new BitArray(flags.ToArray()) // Pack the flags into a bitarray
    let flagsBytes: byte[] = Array.zeroCreate ((flags.Length-1)/8+1)
    flags.CopyTo(flagsBytes, 0)
    (txs |> List.choose id, new MerkleBlock(block.Header, txHashes, flagsBytes))

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
    
    let mutable target: IPEndPoint = null // For logging only
    let mutable versionMessage: Version option = None // For logging only
    let mutable bloomFilterUpdateMode = BloomFilterUpdate.UpdateNone
    let mutable bloomFilter: BloomFilter option = None
    let mutable relay = 1uy

(** Peers take input from 3 distinct sources

- commands from the Tracker
- header messages from the remote node
- block messages from the remote node
*)
    let incoming = new Event<PeerCommand>()
    let headersIncoming = new Subject<Headers>()
    let blockIncoming = new Subject<Block * byte[]>()

    let incomingEvent = incoming.Publish

(** The workloop takes a network stream and continually grabs data from it and delivers them
to the Observable.
*)
    let workLoop(stream: NetworkStream) = 
        let buffer: byte[] = Array.zeroCreate 1000000 // network buffer
        let task() = stream.AsyncRead(buffer) |> Async.AsObservable
        let hasData = ref true
        Observable
            .While((fun () -> !hasData), Observable.Defer(task))
            .Do(fun c -> hasData := c > 0)
            .Where(fun c -> c > 0)
            .Select(fun c -> buffer.[0..c-1]) // Keep doing the same task until the stream closes
        
(** Helper functions to change the state of the peer. These functions work asynchronously and can be called from
any thread.
*)
    let readyPeer() =
        incoming.Trigger(PeerCommand.SetReady)

    let closePeer() =
        incoming.Trigger(PeerCommand.Close)

    let badPeer() =
        incoming.Trigger(UpdateScore -100) // lose 100 points - the banscore is not implemented yet

(** Another helper function that sends a message out and return an empty observable. By having it as
an observable, the sending is part of the time out.
*)
    let sendMessageObs (peerQueues: PeerQueues) (message: BitcoinMessage) = 
        Observable.Defer(
            fun () -> 
                (peerQueues :> IPeerSend).Send(message)
                Observable.Empty()
            )
(**
Send the message out and catch any exception due to a communication problem with the remote node.
It could have closed. The network stream has a WriteTimeOut set and will throw an exception if the message
couldn't be sent during the allocated time. At this point, if an exception is raised I close the peer because
there isn't much chance of making progress later.
*)
    let sendMessage (stream: NetworkStream) (message: BitcoinMessage) = 
        let messageBytes = message.ToByteArray()
        try
            stream.Write(messageBytes, 0, messageBytes.Length)
        with
        | e -> 
            logger.DebugF "Cannot send message to peer"
            closePeer()

(**
Applies the bloom filter to the outgoing message
*)
    let filterMessage (message: BitcoinMessage): BitcoinMessage list =
        if relay = 1uy then
            match message.Command with
            | "tx" -> 
                let emit = 
                    bloomFilter |> Option.map (fun bf ->
                        let tx = message.ParsePayload() :?> Tx 
                        let txMatch = checkTxAgainstBloomFilter bf bloomFilterUpdateMode tx
                        if txMatch then logger.DebugF "Filtered TX %s" (hashToHex tx.Hash)
                        txMatch
                    ) |?| true
                if emit then [message] else []
            | "block" -> 
                bloomFilter |> Option.map (fun bf ->
                        let block = message.ParsePayload() :?> Block
                        let (txs, merkleBlock) = buildMerkleBlock bf bloomFilterUpdateMode block
                        let txMessages = txs |> List.map(fun tx -> new BitcoinMessage("tx", tx.ToByteArray()))
                        txs |> Seq.iter (fun tx -> logger.DebugF "Filtered TX %s" (hashToHex tx.Hash))
                        txMessages @ [new BitcoinMessage("merkleblock", merkleBlock.ToByteArray())]
                    ) |?| [message]
            | _ -> [message]
        else 
            match message.Command with
            | "tx" | "block" -> []
            | _ -> [message]

(**
`processMessage` handles messages incoming from the remote node. Generally speaking, it parses the payload of the message
and routes it to the appropriate queue. 
*)
    let processMessage (peerQueues: PeerQueues) (message: BitcoinMessage) = 
        let command = message.Command
        match command with
        | "version" 
        | "verack" ->
            (peerQueues :> IPeerSend).Receive(message)
        | "getaddr" -> 
            let now = Instant.FromDateTimeUtc(DateTime.UtcNow)
            let addr = new Addr([|{ Timestamp = int32(now.Ticks / NodaConstants.TicksPerSecond); Address = NetworkAddr.MyAddress }|])
            (peerQueues :> IPeerSend).Send(new BitcoinMessage("addr", addr.ToByteArray()))
        | "getdata" ->
            let gd = message.ParsePayload() :?> GetData
            mempoolIncoming.OnNext(GetTx (gd.Invs |> List.filter (fun inv -> inv.Type = txInvType), peerQueues))
            blockchainIncoming.OnNext(DownloadBlocks (gd.Invs |> List.filter (fun inv -> inv.Type = blockInvType || inv.Type = filteredBlockInvType), peerQueues))
        | "getheaders" ->
            let gh = message.ParsePayload() :?> GetHeaders
            blockchainIncoming.OnNext(GetHeaders (gh, peerQueues))
        | "getblocks" ->
            let gb = message.ParsePayload() :?> GetBlocks
            blockchainIncoming.OnNext(GetBlocks (gb, peerQueues))
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
                mempoolIncoming.OnNext(Inv(inv, self)) // send to mempool
            elif inv.Invs.Length = 1 && inv.Invs.[0].Type = blockInvType then // a block inv, send to blockchain
                logger.DebugF "Catchup requested by %d %A %s" id self (hashToHex inv.Invs.[0].Hash)
                blockchainIncoming.OnNext(Catchup(self, inv.Invs.[0].Hash))
        | "tx" ->
            let tx = message.ParsePayload() :?> Tx
            mempoolIncoming.OnNext(Tx tx)
        | "ping" ->
            let ping = message.ParsePayload() :?> Ping // send to blockchain because tests use pings to sync with catchup
            blockchainIncoming.OnNext(BlockchainCommand.Ping(ping, peerQueues))
        | "mempool" ->
            let mempool = message.ParsePayload() :?> Mempool
            mempoolIncoming.OnNext(MempoolCommand.Mempool peerQueues)
        | "filteradd" ->
            let filterAdd = message.ParsePayload() :?> FilterAdd
            bloomFilter |> Option.iter (fun bloomFilter -> bloomFilter.Add filterAdd.Data)
            relay <- 1uy
        | "filterload" ->
            let filterLoad = message.ParsePayload() :?> FilterLoad
            let bf = new BloomFilter(filterLoad.Filter, filterLoad.NHash, filterLoad.NTweak)
            bloomFilter <- Some(bf)
            relay <- 1uy
        | "filterclear" -> 
            bloomFilter <- None
            relay <- 1uy
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
            let client = new Sockets.TcpClient()
            let connect = 
                async {
                    let! stream = Protocol.connect(target.Address) (target.Port)
                    return OpenStream (stream, target, tip)
                    }

            // Connect to the node and bail out if it fails or the timeout expires
            Observable.Timeout(Async.AsObservable connect, connectTimeout).Subscribe(
                onNext = (fun c -> incoming.Trigger c), // If connected, grab the stream
                onError = (fun ex -> 
                    logger.DebugF "Connect failed> %A %s" t (ex.ToString())
                    (client :> IDisposable).Dispose()
                    closePeer())
            ) |> ignore
            data
        | OpenStream (stream, t, tip) -> // Got a stream from a successful connection (in or out)
            logger.DebugF "OpenStream %A" t
            target <- t
            stream.ReadTimeout <- settings.ReadTimeout
            stream.WriteTimeout <- int(commandTimeout.Ticks / TimeSpan.TicksPerMillisecond)
            // Setup the queues and the network to bitcoin message parser
            // Observables are created but not subscribed to, so in fact nothing is consumed from the stream yet
            let peerQueues = new PeerQueues(stream, target)
            let parser = new BitcoinMessageParser(workLoop(stream))

            // Subscribe the outgoing queue, it's ready to send out messages
            // Subscriptions are not added to the disposable object unless they should be removed when the event loop finishes
            peerQueues.To.SelectMany(fun m -> filterMessage m |> List.toSeq).Subscribe(onNext = (fun m -> sendMessage stream m), onError = (fun e -> closePeer())) |> ignore
            disposable.Add(peerQueues)

            // Prepare and send out my version message
            let version = Version.Create(SystemClock.Instance.Now, target, NetworkAddr.MyAddress.EndPoint, int64(random.Next()), "Satoshi YOLO 1.0", tip.Height, 1uy)
            (peerQueues :> IPeerSend).Send(new BitcoinMessage("version", version.ToByteArray()))

            // The handshake observable waits for the verack and the version response from the other side. When both parties have
            // exchanged their version/verack, it will deliver a single event "Handshaked"
            let handshakeObs = 
                peerQueues.From
                    .Scan((false, false), fun (versionReceived: bool, verackReceived: bool) (m: BitcoinMessage) ->
                    logger.DebugF "HS> %A" m
                    match m.Command with
                    | "version" -> 
                        let version = m.ParsePayload() :?> Version
                        versionMessage <- Some(version)
                        relay <- version.Relay
                        (peerQueues :> IPeerSend).Send(new BitcoinMessage("verack", Array.empty))
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
                    incoming.Trigger c),
                onError = (fun ex -> 
                    logger.DebugF "Handshake failed> %A %s" target (ex.ToString())
                    closePeer())
            ) |> ignore

            (** Subscription have to be made *after* the listeners are set up otherwise messages can be lost. 
            For instance, I had a bug because the following `Subscribe` was made before `handshakeObs`.
            In some cases an incoming connection would post a `version`. It would go to `processMessage` and 
            be sent to the `peerQueues.From` observable. But since `handshakeObs` occurs later, there would
            be nothing to handle this message and it would be lost.
            *)

            // Finally subscribe and start consuming the responses from the remote side
            // Any exception closes the peer
            logger.DebugF "Before Subscription"
            disposable.Add(
                parser.BitcoinMessages.Subscribe(
                    onNext = (fun m -> processMessage peerQueues m), 
                    onCompleted = (fun () -> closePeer()),
                    onError = (fun e -> 
                        logger.DebugF "Exception %A" e
                        closePeer())))
            logger.DebugF "Subscription made"

            { data with Queues = Some(peerQueues) }
        | Handshaked ->
            // Got the handshake, the peer is ready
            trackerIncoming.OnNext (TrackerCommand.SetReady id)
            trackerIncoming.OnNext (TrackerCommand.SetVersion (id, versionMessage.Value))
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
`processCommand` is the handler for normal state. The request can be either

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
            (peerQueues :> IPeerSend).Send(message)
            data
        | PeerCommand.GetHeaders (gh, ts, _) ->
            let sendObs = sendMessageObs peerQueues (new BitcoinMessage("getheaders", gh.ToByteArray()))
            let obs = 
                Observable
                    .Timeout(sendObs.Concat(headersIncoming), commandTimeout)
            ts.SetResult(obs)
            { data with State = PeerState.Busy }
        | PeerCommand.DownloadBlocks (gd, ts) ->
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
            if newData.Score <= 0 then incoming.Trigger(PeerCommand.Close)
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
        | PeerCommand.DownloadBlocks (gd, ts) ->
            ts.SetResult(self :> IPeer, Observable.Empty())
            data
        | _ -> data

    let initialState = { State = PeerState.Closed; Score = 100; Queues = None; CommandHandler = processConnection }
    let runHandler (data: PeerData) (command: PeerCommand) = 
        // logger.DebugF "PeerCommand> %A" command
        data.CommandHandler data command

    do
        disposable.Add(
            incomingEvent
                .ObserveOn(ThreadPoolScheduler.Instance)
                .Scan(initialState, new Func<PeerData, PeerCommand, PeerData>(runHandler))
                .Subscribe())

    interface IDisposable with
        member x.Dispose() = 
            disposable.Dispose()

    interface IPeer with
        member x.Ready() = readyPeer()
        member val Id = id with get
        member x.Target with get() = target // For diagnostics only
        member x.Bad() = badPeer()
        member x.Receive m = incoming.Trigger m

    override x.ToString() = sprintf "Peer(%d, %A, %A)" id target versionMessage

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
        let port = if settings.TestNet then 18444 else 8333

        let! entry = Async.AwaitTask(Dns.GetHostEntryAsync("seed.bitnodes.io"))
        for peer in entry.AddressList do
            let addr = { Timestamp = int (now.Ticks / NodaConstants.TicksPerSecond); Address = new NetworkAddr(new IPEndPoint(peer.MapToIPv4(), defaultPort)) }
            Db.updateAddr addr
        } |> Async.StartImmediate

let initPeers() =
    dropOldPeers()
    let peers = Db.getPeers()
    if peers.Length < 1000 then
        bootstrapPeers()

