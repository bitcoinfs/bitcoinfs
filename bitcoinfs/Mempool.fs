(** 
# The Memory Pool 

Where unconfirmed transactions go 
*)
module Mempool

(*** hide ***)
open System
open System.Linq
open System.Collections.Generic
open System.Reactive.Linq
open System.Reactive.Concurrency
open FSharpx
open FSharpx.Collections
open FSharpx.Choice
open FSharpx.Validation
open Protocol
open Db
open Peer
open Tracker

let mutable listTx = new List<byte[]>()
let mutable mempool = new Dictionary<byte[], Tx>(new HashCompare())
let mutable mempoolHeight = 0

type NopUndoWriter() =
    interface IUTXOWriter with
        member x.Write(_: TxOperation, _: OutPoint, _: UTXO) = ignore()

type OutpointCompare() =
    interface IEqualityComparer<OutPoint> with
        member x.Equals(left: OutPoint, right: OutPoint) =
            if obj.ReferenceEquals(left, right) then true
            else
                hashCompare.Equals(left.Hash, right.Hash) && left.Index = right.Index

        member x.GetHashCode(outpoint: OutPoint) = hashCompare.GetHashCode(outpoint.Hash)

(**
A UTXO accessor that stores UTXO operations in memory. Deletes are stored as tombstones and adds
are stored as key value pairs. The accessor methods first checks the in-memory table (a dictionary) for
a match before going to the base/lower UTXO accessor. Basically, this is an addendum to the base UTXO set.
Instead of modifying the base set, it keeps track of the recent differences.

If they become permanent, `Commit` writes them to the base UTXO set otherwise the accessor is simply discarded.
*)

type MempoolUTXOAccessor(baseUTXO: IUTXOAccessor) =
    let table = new Dictionary<OutPoint, UTXO>(new OutpointCompare())
    // With LevelDB, I had iterators. A dictionary does not have a sorted iterator so I need to keep track
    // of the counts separately
    let counts = new Dictionary<byte[], int>(new HashCompare()) 

    let getOrDefault (hash: byte[]) = 
        let (f, count) = counts.TryGetValue(hash) // I wish there was a GetOrDefault instead of a TryGetValue
        if f then count else 0
    let deleteUTXO (outpoint: OutPoint) = 
        table.[outpoint] <- null
        let count = getOrDefault outpoint.Hash
        counts.[outpoint.Hash] <- count-1
    let addUTXO (outpoint: OutPoint) (utxo: UTXO) = 
        table.[outpoint] <- utxo
        let count = getOrDefault outpoint.Hash
        counts.[outpoint.Hash] <- count+1
        
    let getUTXO (outpoint: OutPoint) =
        let (f, utxo) = table.TryGetValue(outpoint)
        if f
        then 
            if utxo <> null 
            then Some(utxo)
            else 
                logger.DebugF "Cannot find outpoint %A" outpoint
                None
        else
            baseUTXO.GetUTXO outpoint
    let getCount (txHash: byte[]) =
        let (f, count) = counts.TryGetValue(txHash)
        if f 
        then count + baseUTXO.GetCount(txHash)
        else baseUTXO.GetCount(txHash)

    let commit() = // Write them for good
        table |> Seq.iter(fun kv ->
            let outpoint = kv.Key
            let utxo = kv.Value
            if utxo <> null 
            then baseUTXO.AddUTXO(outpoint, utxo)
            else baseUTXO.DeleteUTXO(outpoint)
        )
        table.Clear()
        counts.Clear()

    member x.Clear() = table.Clear()
    member x.Commit() = commit()

    interface IUTXOAccessor with
        member x.DeleteUTXO(outpoint) = deleteUTXO outpoint
        member x.AddUTXO(outpoint, txOut) = addUTXO outpoint txOut
        member x.GetUTXO(outpoint) = getUTXO outpoint
        member x.GetCount(txHash) = getCount txHash
        member x.Dispose() = table.Clear()

(** 
The memory pool receives transactions from the all the connected nodes. Many of them turn out to be invalid, most of the time
because the output is already spent (double-spend). Sometimes though, the signatures are invalid altogether. In any case,
it's important to check the transactions before they are accepted into the pool. When the application receives a new block,
the memory pool gets revalidated and every invalid transaction gets booted out. In this case, it is because of a double-spend between
the transactions in the block and the same one from the pool.
*)
let txHash = hashFromHex "6affa593d2c14cf9dbc79e33b1eb79746154dbbfcb25b00908dc4855011660d6"
let checkScript (utxoAccessor: IUTXOAccessor) (tx: Tx): Option<unit> = 
    if tx.Hash = txHash then printfn "STOP"
    let x = 
        tx.TxIns 
            |> Seq.mapi (fun i txIn ->
                let scriptEval = new Script.ScriptRuntime(Script.computeTxHash tx i)
                let outpoint = txIn.PrevOutPoint
                let utxo = utxoAccessor.GetUTXO outpoint
                utxo |> Option.map (fun utxo -> scriptEval.Verify(txIn.Script, utxo.TxOut.Script))
                ) 
            |> Seq.toList |> Option.sequence 
            |> Option.map(fun x -> x.All(fun x -> x)) // tx succeeds if all scripts succeed
    (x.IsSome && x.Value) |> errorIfFalse "script failure"

let mempoolAccessor = new MempoolUTXOAccessor(utxoAccessor)
let nopWriter = new NopUndoWriter()

(**
Validating a tx in the pool will update the mempool UTXO set that is built on top of the confirmed UTXO. But for
the mempool, there is nothing to undo and therefore no need for an undo writer.
*)
let validate (tx: Tx) =
    maybe {
        do! checkScript mempoolAccessor tx
        processUTXO mempoolAccessor nopWriter false mempoolHeight tx |> ignore
        return ()
    }

(**
Revalidate builds a new pool and then flips the old one with the new one.
*)
let revalidate () =
    mempoolAccessor.Clear()
    let newListTx = new List<byte[]>()
    let newMempool = new Dictionary<byte[], Tx>(new HashCompare())
    listTx <- listTx.Where(fun hash ->
        let tx = mempool.[hash]
        (validate tx).IsSome
        ).ToList()
    mempool <- listTx.Select(fun hash -> mempool.[hash]).ToDictionary(fun tx -> tx.Hash)
    logger.InfoF "Mempool has %d transactions" mempool.Count

let addTx tx = 
    try
        validate tx |> Option.iter(fun () ->
            listTx.Add(tx.Hash)
            mempool.Item(tx.Hash) <- tx
            let invVector = InvVector([InvEntry(txInvType, tx.Hash)])
            broadcastToPeers.OnNext(new BitcoinMessage("inv", invVector.ToByteArray()))
            logger.DebugF "Unconfirmed TX -> %s" (hashToHex tx.Hash)
            )
    with
    | ValidationException e -> ignore() // printfn "Invalid tx: %s" (hashToHex tx.Hash)

(** 
## Message loop

The main message loop picks up 

- new `inv` messages. If the mempool doesn't have it, it will request for the tx data using `getdata`
- `tx` data. It gets validated and then put into the pool
- `getdata`. When another node ask for the details of a tx it doesn't have
- `mempool`. The mempool message that triggers a full dump of the mempool as inv messages
- revalidate
*)
let processCommand (command: MempoolCommand) = 
    try
        match command with
        | Revalidate (currentHeight, undoTxs) ->
            mempoolHeight <- currentHeight
            for txBlock in undoTxs do
            for tx in txBlock do
                listTx.Add(tx.Hash)
                mempool.Item(tx.Hash) <- tx
            revalidate()
        | Tx tx -> addTx tx
        | Inv (invVector, peerIncoming) -> 
            let newInvs = invVector.Invs |> List.filter(fun inv -> not (mempool.ContainsKey inv.Hash))
            newInvs |> List.iter (fun inv -> mempool.Add(inv.Hash, null))
            let gd = new GetData(newInvs)
            if not gd.Invs.IsEmpty then
                peerIncoming.OnNext(GetData gd)
        | GetTx (invs, peer) ->
            for inv in invs do
                let (f, tx) = mempool.TryGetValue(inv.Hash)
                if f then
                    peer.OnNext(new BitcoinMessage("tx", tx.ToByteArray()))
        | Mempool peer -> 
            let inv = mempool.Keys |> Seq.map (fun txHash -> InvEntry(txInvType, txHash)) |> Seq.toList
            logger.DebugF "MemoryPool %A" inv
            if not inv.IsEmpty then
                let invVec = InvVector(inv)
                peer.OnNext(new BitcoinMessage("inv", invVec.ToByteArray()))
    with
    | :? ObjectDisposedException -> ignore()

let startMempool() =
    mempoolIncoming.ObserveOn(NewThreadScheduler.Default).Subscribe(processCommand) |> ignore
