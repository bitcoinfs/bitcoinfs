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
# Bob the Blockchain

This is now close to the end of the code and it is the highest component in the data model. Bob's job is to identify the best *valid* blockchain
and keep the UTXO set synchronized to it. Working with the other actors, Bob knows when a peer has a block hash that he doesn't know about and
can request the recent headers from this peer. Also, once his satisfied with the block headers, Bob can request for the actual block contents.

Bob is a very cautious man and he will check everything that people tell him, but he's also a forgiving man and he will accept all the blocks that
are valid even if a peer tries to sneak in a few invalid block here and there.

When he synchronizes (catches up) with a peer, Bob follows the checklist:

- get headers (async). Bob gives his most recent block header (the tip) and asks the peer if he has any blocks after that one.
If the peer says no, Bob is done. If he gets some blocks, Bob will connect them with the ones he knows already. If they can't be connected because he
never heard the block that supposedly precedes the chain that he received, Bob concludes that the chain is orphaned and not of concern to him. If that chain 
eventually gets connected, he will be made aware of it when he get the connecting block.
- extend the new chain if possible. Bob consults his database to see if he has received headers that follows the new chain because, at times, blocks are given out of order
- compute heights. Now that the block connects somewhere to a known block, Bob can update the heights of all the blocks that he received. Starting from the previous block
that he knows about, Bob increments the height and assigns the result to the first block of the new chain and so on so forth.
- store headers into db. Bob takes these headers and writes them to his database. They will never be removed from there.
- compare POW (Proof of Work). First he finds out the lowest common ancestor between his best chain and the chain he received. If the chain he received extends his current chain, it's the best case because the LCA will be his tip 
but it doesn't matter to Bob. It works the same either way.
He compares the work from both chains. Knowing that both chains are equal from the LCA to the genesis block, Bob only has to compare the POW between the LCA and both tips. If the new chain
is no better than the old one, there is no need to continue.
- download blocks (async). Bob looks at the blocks he already has downloaded and ignores the one he has downloaded already. Bob splits the rest evenly in several groups
and asks his peers to download them for him. This task is done in parallel while he sits patiently. During that time, if a download fails the blocks get reassigned to a different peer. 
So, eventually Bob gets his blocks or the retry limit got reached. In the later case, Bob gives up and will try another time. The catchup fails. 
- rollback utxo to LCA beween main and new fork. However, if Bob got his blocks he now has to determine how many of these blocks are good. He creates a new in memory UTXO set on top of the existing db
and rolls back all the blocks back to the LCA. Then he dilligently checks the blocks of the new chain and applies their transactions until the end or the first failure. If he made it to the end, the new chain
was all good. If not, he has a partially good new chain.
- compare POW between current chain and new chain. Bob trims the new chain down to the first failure if there was one and compares the POW of the revised chain with his own chain. The new chain was trimmed so
even if it was better earlier, it may not be good enough anymore.
- if better, commit tempdb, update tip. Finally, if the new chain is still better than his chain, Bob commits the in memory UTXO to the database and updates his tip. Otherwise, he simply drops the in memory UTXO and
everything is forgotten.

Here's a big flowchart

![blockchain](uml/blockchain.png)
*)
module Blockchain

(*** hide ***)
open System
open System.Net
open System.Net.Sockets
open System.Collections.Generic
open System.Linq
open System.IO
open System.Text
open System.Reactive
open System.Reactive.Linq
open System.Reactive.Subjects
open System.Reactive.Disposables
open System.Reactive.Threading.Tasks
open System.Reactive.Concurrency
open System.Threading.Tasks
open FSharp.Control
open FSharpx
open FSharpx.Collections
open FSharpx.Choice
open FSharpx.Validation
open FSharpx.Option
open ExtCore.Control
open Org.BouncyCastle.Utilities.Encoders
open NodaTime
open MoreLinq
open Protocol
open Tracker
open Db
open Peer
open Checks
open Mempool

let disposable = new CompositeDisposable()
let mutable tip = Db.readHeader (Db.readTip())
Peer.trackerIncoming.OnNext(SetTip tip)

let fnBlockchain = fun () -> chainFromTip tip

(**
And in code:
*)
let calculateChainHeights(newHeaders: BlockHeaderList): BlockChainFragment option = 
    newHeaders |> Seq.windowed 2 |> Seq.iter (fun pair ->
        let [prev; cur] = pair |> Seq.toList
        prev.NextHash <- cur.Hash
    ) // Link header to next - headers are already linked by prev hash
    let blockchain = fnBlockchain()
    let hashOfPrevNewHeader = Seq.tryPick Some newHeaders |> Option.map (fun bh -> bh.PrevHash) |?| tip.Hash
    let prevNewHeader = Db.readHeader hashOfPrevNewHeader
    if prevNewHeader.Hash = zeroHash
    then 
        logger.DebugF "Orphaned branch %A" newHeaders
        None
    else 
        newHeaders |> Seq.iteri (fun i newHeader -> newHeader.Height <- prevNewHeader.Height + i + 1)
        (prevNewHeader :: newHeaders ) |> List.rev |> Some

(**
To calculate the lowest common ancestor, I use the fact that I know the height of the nodes. It makes
the determination much simpler. I find the minimum height between the two nodes and move from the deeper
node up until I reach a node that has the same height. Now I'm working with two nodes that are at the same height
but potentially in different branches of the tree. I compare the two nodes and move up from both nodes simultaneously 
until I reach the same ancestor.
*)
let calculateLowestCommonAncestor (newChain: BlockChainFragment) =
    let blockchain = fnBlockchain()
    let newTip = newChain |> List.head
    let minHeight = min tip.Height newTip.Height
    let trimBlockchain = blockchain |> Seq.skip (tip.Height - minHeight)
    let trimNewHeaders = newChain |> Seq.skip (newTip.Height - minHeight)

    (Seq.zip trimBlockchain trimNewHeaders |> Seq.tryFind (fun (a, b) -> hashCompare.Equals(a.Hash, b.Hash)) |> Option.map fst)

(**
Compares the POW of one chain against the current chain starting from the given node
*)
let isBetter (oldChain: BlockChainFragment) (newChain: BlockChainFragment) = getWork oldChain < getWork newChain

(**
Fetch a set of nodes asynchrounously from the current set of peers. The function retries until it reaches the maximum
number of attempts. Between retries, only the failed downloads are retried. For instance, if a peer provides 9/10 blocks
only the 1/10 missing block is retried. Furthermore, after a failure the peer gets a malus (`Bad`) and can end up being removed.
In that case, the application will use a different peer. In the background, the tracker will eventually replace the bad peer too. 
That takes place independently from Bob.
*)
type BlockMap = Map<byte[], BlockHeader>
// Get a list of blocks
let rec asyncGetBlocks (headers: BlockHeader list) (attempsRemaining: int) = 
    // After a block is received, check that it's among the blocks we are waiting for
    // If so, update the height and store it on file
    // Then remove it from the list of pending blocks
    let updatePendingBlocks (pendingBlocks: BlockMap) (block: Block, payload: byte[]) = 
        logger.DebugF "Block received -> %s" (hashToHex block.Header.Hash)
        pendingBlocks.TryFind(block.Header.Hash) |> Option.iter(fun header ->
            block.Header.Height <- header.Height
            storeBlock block payload
            )
        pendingBlocks.Remove(block.Header.Hash)

    async {
        // If we haven't reached the max number of attempts
        if attempsRemaining > 0 then
            let pendingBlocks = headers |> List.map(fun bh -> (bh.Hash, bh)) |> Map.ofList
            let! (peer, obs) = Async.AwaitTask(Tracker.getBlocks(pendingBlocks |> Map.keys)) // Send a getdata request and park until we get an observable of blocks

            let! failedBlocks = (
                use d = Disposable.Create(fun () -> peer.Ready())
                Async.AwaitTask(
                    Observable.Return(pendingBlocks)
                        .Concat(obs // Unlike F# scan, RX scan doesn't emit the first element (pendingBlocks) and we must manually add it
                            .Scan(pendingBlocks, Func<BlockMap, Block * byte[], BlockMap> updatePendingBlocks) // update pending block list as we get blocks
                            .OnErrorResumeNext(Observable.Empty())) // If we get an exception quit without error
                        .LastOrDefaultAsync() // Fetch the last pending block list
                        .ToTask()) // Park until we finished
            )
            if not failedBlocks.IsEmpty then // Some blocks remaining, it was a failure
                peer.Bad()
                logger.DebugF "Failed blocks %A" (failedBlocks |> Map.values)
                return! asyncGetBlocks (failedBlocks |> Map.valueList) (attempsRemaining-1) // Retry with 1 attempt fewer
            else
                logger.DebugF "GetBlocks completed"
                return ()
        else
            raise (new IOException "GetBlocks failed") // TODO: Delete block files
    }

let downloadBlocks (newChain: BlockChainFragment) = 
    // Fetching blocks from peers
    let h = newChain |> List.filter(fun bh -> not (hasBlock bh)) // Filter the blocks that we already have
    // Spread blocks around 'evenly' accross connected peers
    let c = max Tracker.connectionCount 1 
    let batchSize = h.Count() / c
    let getdataBatchSize = max (min batchSize maxGetdataBatchSize) minGetdataBatchSize

    // Create an array of async work to fetch blocks
    let hashes = h |> List.toArray
    let getblocks = 
        seq { 
        for batch in hashes.Batch(getdataBatchSize) do
            yield asyncGetBlocks(batch |> Seq.toList) settings.MaxGetblockRetry }
        |> Seq.toArray
    Async.Parallel getblocks |> Async.Ignore // execute fetch blocks in parallel - park until finished
        

(**
Undo the blockchain up to a certain point
*)
let rollbackTo (accessor: IUTXOAccessor) (targetBlock: BlockHeader) =
    let blockchain = fnBlockchain()
    blockchain |> Seq.takeWhile(fun bh -> bh.Hash <> targetBlock.Hash) |> Seq.map(undoBlock accessor) |> Seq.toList

(**
The function that drives all the checks and chains them together. Checks were discussed in the previous section.
*)
let checkBlock (utxoAccessor: IUTXOAccessor) (p: BlockHeader) (blocks: BlockHeader[]): Choice<BlockHeader, BlockHeader * BlockHeader> =
    let prevBlock = blocks.[0]
    let currentBlock = blocks.[1]
    let tempUTXO = new MempoolUTXOAccessor(utxoAccessor)
    maybe {
        do! currentBlock.PrevHash = prevBlock.Hash |> errorIfFalse "prev blockhash field does not match hash of previous block"
        do! checkBlockHeader currentBlock
        let blockContent = loadBlock currentBlock
        let blockContentSerialized = blockContent.ToByteArray()
        let blockSize = blockContentSerialized.Length // Length has to be based on serialized block and not original block
        do! (blockSize <= maxBlockSize) |> errorIfFalse "blocksize exceeds limit"
        do! checkBlockTxs tempUTXO blockContent
        do! updateBlockUTXO tempUTXO blockContent
        tempUTXO.Commit()
        return ()
    } |> Option.map(fun () -> Choice1Of2 currentBlock) |?| Choice2Of2 (p, currentBlock)

let chainTo (blockchain: seq<BlockHeader>) (stop: BlockHeader) = blockchain |> Seq.takeWhile (fun bh -> bh.Height <> stop.Height) |> Seq.toList

let updateIsMain (fragment: BlockChainFragment) (isMain: bool) = 
    fragment |> List.iter (fun bh ->
        bh.IsMain <- isMain
        Db.writeHeaders bh
    )

(**
## The catchup workflow
*)
let catchup (peer: IPeer) = 
    let getHeaders(): Async<Headers> = 
        async {
            use d = Disposable.Create(fun () -> peer.Ready())
            let blockchain = fnBlockchain() // Get current blockchain
            let gh = new GetHeaders(blockchain |> Seq.truncate 10 |> Seq.map(fun bh -> bh.Hash) |> Seq.toList, Array.zeroCreate 32) // Prepare GetHeaders request
            let! headers = Async.AwaitTask(Tracker.getHeaders(gh, peer)) // Send request - park until request is processed
            let! getHeadersResult = Async.AwaitTask(headers.FirstOrDefaultAsync().ToTask()) // Pick Headers or exception
            logger.DebugF "GetHeaders Results> %A %A" (peer.Target) (getHeadersResult)
            return getHeadersResult
        }

    let rec catchupImpl() = 
        try
            let headersMessage = getHeaders() |> Async.RunSynchronously
            let currentHeight = tip.Height

            if headersMessage <> null && not headersMessage.Headers.IsEmpty then
                let headers = headersMessage.Headers
                let newBlockchainOpt = calculateChainHeights headers
                newBlockchainOpt |> Option.filter (fun f -> f.Head.Height > currentHeight-10000) |> Option.iter (fun newBlockchainFrag -> // limit the size of a fork to 10000 blocks
                    newBlockchainFrag |> List.iter Db.writeHeaders
                    let headersAfter = newBlockchainFrag |> List.head |> iterate (fun bh -> Db.getNextHeader bh.Hash) |> Seq.takeWhile (fun bh -> bh.Hash <> zeroHash) |> Seq.skip 1 |> Seq.toList |> List.rev
                    let connectedNewBlockchain = (headersAfter @ newBlockchainFrag) |> List.rev |> Seq.truncate 100 |> Seq.toList |> List.rev
                    let downloadBlocksAsync = connectedNewBlockchain |> List.rev |> List.tail |> downloadBlocks
                    downloadBlocksAsync |> Async.RunSynchronously
                    let tempUTXO = new MempoolUTXOAccessor(utxoAccessor)
                    let lca = calculateLowestCommonAncestor connectedNewBlockchain
                    lca |> Option.iter(fun lca ->
                        let mainChain = chainTo (fnBlockchain()) lca
                        let newBlockchain = connectedNewBlockchain |> List.takeWhile(fun bh -> bh.Hash <> lca.Hash)
                        if isBetter mainChain newBlockchain then
                            let undoTxs = rollbackTo tempUTXO lca
                            let newBlockList = lca :: (newBlockchain |> List.rev)

                            let lastValidBlockChoice = newBlockList |> Seq.windowed 2 |> Choice.foldM (checkBlock tempUTXO) lca
                            let lastValidBlock =
                                match lastValidBlockChoice with
                                | Choice1Of2 bh -> bh
                                | Choice2Of2 (bh, invalidBlock) -> 
                                    deleteBlock invalidBlock
                                    bh
                            let validNewBlockchain = newBlockchain |> List.skipWhile(fun bh -> bh.Hash <> lastValidBlock.Hash)
                            if isBetter mainChain validNewBlockchain then
                                logger.InfoF "New chain is better %A" headers
                                tempUTXO.Commit()
                                lca.NextHash <- newBlockchain.Last().Hash // Attach to LCA
                                Db.writeHeaders lca
                                updateIsMain mainChain false
                                updateIsMain validNewBlockchain true
                                tip <- lastValidBlock
                                Db.writeTip tip.Hash
                                mempoolIncoming.OnNext(Revalidate (tip.Height, (undoTxs |> List.rev)))
                                let invBlock = InvVector([InvEntry(blockInvType, tip.Hash)])
                                broadcastToPeers.OnNext(new BitcoinMessage("inv", invBlock.ToByteArray()))
                                trackerIncoming.OnNext(SetTip tip)
                                catchupImpl()
                        )
                )
            with 
            | ex -> logger.DebugF "%A" ex

    catchupImpl()

let getBlockchainUpTo (hashes: byte[] list) (hashStop: byte[]) (count: int) = 
    let startHeader =
        hashes 
        |> Seq.map (fun hash -> Db.readHeader hash)
        |> Seq.tryFind (fun bh -> bh.IsMain
        ) |?| genesisHeader

    iterate (fun bh -> Db.readHeader bh.NextHash) startHeader |> Seq.truncate (count+1) |> Seq.takeWhile (fun bh -> bh.Hash <> hashStop) |> Seq.tail |> Seq.toList 

(**
## Command handler

Bob's commands are:

- `Catchup` from a given peer
- `GetBlock`. A remote node wants to get a block from this client
- `GetHeaders`. A remote node wants to get the headers from this client
- `Ping`. Ping is here only because it helps with acceptance testing. The system works asynchronously and that makes it
difficult to know when catchup completes for an external component. The test driver probes the client node by sending
pings and then waits for the pong. Originally, ping/pong was directly handled by the peer but then the response was too fast
and the test driver would proceed before catchup even started. By putting ping here, the request gets queued until Bob is
finished with catchup.
*)
let processCommand command = 
    match command with
    | Catchup (peer, hash) -> 
        logger.DebugF "Catchup started for peer %A" peer
        let blockchain = fnBlockchain()
        if hash = null || (Db.readHeader hash).Hash = zeroHash || not (hasBlock (Db.readHeader hash)) then
            catchup peer
        logger.DebugF "Catchup completed for peer %A" peer
    | DownloadBlocks (invs, peer) ->
        let downloadResults = 
            invs |> List.map (fun inv ->
                let bh = Db.readHeader inv.Hash
                let block = Choice.protect loadBlock bh
                block |> Choice.mapError (fun _ -> inv)
            )
        downloadResults |> List.filter (fun x -> Choice.isResult x) |> List.iter (fun block -> peer.Send(new BitcoinMessage("block", block.Value().ToByteArray())))
        let failedInv = downloadResults |> List.filter (fun x -> Choice.isError x) |> List.map (fun inv -> Choice.getError inv)
        let notfound = new NotFound(failedInv)
        if not failedInv.IsEmpty then peer.Send(new BitcoinMessage("notfound", notfound.ToByteArray()))
    | GetHeaders (gh, peer) ->
        try
            let reqBlockchain = getBlockchainUpTo gh.Hashes gh.HashStop 2000
            logger.DebugF "Headers sent> %A" reqBlockchain
            let headers = new Headers(reqBlockchain)
            peer.Send(new BitcoinMessage("headers", headers.ToByteArray()))
        with
            | e -> logger.DebugF "Exception %A" e
    | GetBlocks (gb, peer) ->
        try
            let reqBlockchain = getBlockchainUpTo gb.Hashes gb.HashStop 500
            let inv = new InvVector(reqBlockchain |> List.map (fun bh -> InvEntry(blockInvType, bh.Hash)))
            peer.Send(new BitcoinMessage("inv", inv.ToByteArray()))
        with
            | e -> logger.DebugF "Exception %A" e
    | Ping (ping, peer) ->
        let pong = new Pong(ping.Nonce)
        peer.Send(new BitcoinMessage("pong", pong.ToByteArray()))

let blockchainStart() =
    disposable.Add(blockchainIncoming.ObserveOn(NewThreadScheduler.Default).Subscribe(processCommand))

