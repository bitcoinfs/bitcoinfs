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
# Checks

Some of the validation checks are cheap and some are expensive to perform. A block or a transaction passes if it passes all the checks. 
For performance reasons, it's better to fail fast, i.e if the block fails a cheap test and an expensive one, it is better to check the
fast one first and avoid doing the expensive check. But alas, it is not always possible to do so. Checks are of several categories:

- parsing checks. If the block got here, it already passed these. 
- single metadata checks. For instance, the hash must be below the target. It's a check that doesn't involve other blocks
- multi metadata checks. These checks are more expensive because more than one block participate. For example, the previous block hash must
match, or the timestamp must be no sooner than the median of the previous 11 blocks
- the most expensive of all are the checks that require analyzing the content of a block: double spends, signature checks, scripts, merkle tree root hash, etc.

*)
module Checks

(*** hide ***)
open System
open System.Collections.Generic
open System.Linq
open System.IO
open System.Text
open System.Reactive
open System.Reactive.Linq
open System.Reactive.Disposables
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
open Mempool

type BlockHeaderList = BlockHeader list // Sequence of block headers from oldest to most recent
type BlockChainFragment = BlockHeader list // List of block headers from most recent to oldest

let minTimestampBlocks = 11
let difficultyReadjustmentInterval = 2016
let targetElapsed = 600u * uint32 difficultyReadjustmentInterval
let maxCheckSigOpsCount = 20000

(** 
## Misc functions 

Create a lazy sequence of block headers backwards from the one given to the genesis block. Because it
is lazily evaluated, it is very rarely read all the way.
*)
let chainFromTip (tip: BlockHeader): seq<BlockHeader> =
    Seq.unfold (
        fun (header: BlockHeader) -> 
            if header.Hash = zeroHash then
                None
            else
                let prevHeader = Db.readHeader(header.PrevHash)
                Some(header, prevHeader))
        (tip)

(** Convert between bits compact representation and target difficulty *)
let target (bits: int) =
    let b = BitConverter.GetBytes(bits)
    let exp = int b.[3]
    let mantissa = b.[0..2]
    (bigint mantissa) <<< (8*(exp-3))

let bits (target: bigint) =
    let targetBytes = target.ToByteArray()
    let mantissa = targetBytes.TakeLast 4 |> Seq.toArray
    let exp = targetBytes.Length
    let p1 = BitConverter.ToInt32(mantissa, 0) 
    (p1 >>> 8) ||| (exp <<< 24)

let maxTarget = target 0x207fFFFF // This is the max target on the main net

(** The reward halving schedule *)
let reward (height: int) =
    let range = height / 210000
    let era = min range 33
    5000000000L / (1L <<< era)

let maxHash = 1I <<< 256
let getWork (fork: BlockHeader seq) = fork |> Seq.map (fun bh -> maxHash / target bh.Bits) |> Seq.sum

// The coinbase follow a particular format
let isCoinBase (tx: Tx) =
    tx.TxIns.Length = 1 && hashCompare.Equals(tx.TxIns.[0].PrevOutPoint.Hash, zeroHash) && tx.TxIns.[0].PrevOutPoint.Index = -1

(** Compute the merkle root of a bunch of hashes *)
let rec computeMerkleRoot (hashes: byte[][]) = 
    if hashes.Length = 1 
        then hashes.[0]
    else
        let hs = 
            if hashes.Length % 2 = 0 
            then hashes
            else 
                [hashes; [|hashes.Last()|]] |> Array.concat
        computeMerkleRoot
            (hs.Batch(2) |> Seq.map(fun x ->
                let h = x |> Array.concat
                dsha h
                ) |> Seq.toArray)

(** Calculate the sum of satoshis in and out of a transaction. If there is a problem, the function returns `None`.
*)
let totalIn (tx: Tx) =
    seq {
        for txIn in tx.TxIns do
            let utxo = utxoAccessor.GetUTXO txIn.PrevOutPoint
            yield utxo |> Option.map(fun utxo -> utxo.TxOut.Value)
        } |> Seq.toList
    |> Option.sequence |> Option.map Seq.sum
let totalOut (tx: Tx) = 
    seq {
        for txOut in tx.TxOuts do
            yield txOut.Value
        } |> Seq.sum

(** Check that the timestamp of the block is in the proper range *)
let checkTimestamp (header: BlockHeader) = 
    maybe {
        let prevBlockTimestamps = chainFromTip header |> Seq.skip 1 |> Seq.truncate minTimestampBlocks |> Seq.toArray |> Array.sortBy (fun h -> h.Timestamp)
        let median = prevBlockTimestamps.[prevBlockTimestamps.Length / 2]
        do! (prevBlockTimestamps.Length < minTimestampBlocks || header.Timestamp > median.Timestamp) |> errorIfFalse "timestamp is too far back"
        do! Instant.FromDateTimeUtc(DateTime.UtcNow.AddHours 2.0) >= Instant.FromSecondsSinceUnixEpoch(int64 header.Timestamp) |> errorIfFalse "timestamp is too far ahead"
    }

let between x min max = if x < min then min elif x > max then max else x
(** Check that the difficulty/target is correct. Either it's the same as the previous block or if it's time to readjust then it must be 
so that the previous 2016 blocks would have taken 10 minutes in average to produce. *)
let checkBits (header: BlockHeader) =
    let testResult = 
        if header.Height > 0 && header.Height % difficultyReadjustmentInterval = 0
        then
            let chain = chainFromTip header
            let prevBlock = chain |> Seq.skip 1 |> Seq.head
            let blockIntervalAgo = chain |> Seq.skip (difficultyReadjustmentInterval) |> Seq.head
            let timeElapsed = (prevBlock.Timestamp - blockIntervalAgo.Timestamp)
            let boundedTimeElapsed = between timeElapsed (targetElapsed/4u) (targetElapsed*4u) // don't readjust by too much
            let prevTarget = target prevBlock.Bits
            let readjustedTarget = (prevTarget*bigint boundedTimeElapsed)/(bigint targetElapsed)
            let newBits = bits readjustedTarget
            newBits = header.Bits
        else
            let prevBlock = chainFromTip header |> Seq.skip 1 |> Seq.head
            prevBlock.Bits = header.Bits
    testResult |> errorIfFalse "difficulty is invalid"

(**
Check that the content of the blockheader is valid
*)
let checkBlockHeader (header: BlockHeader) = 
    logger.InfoF "Checking block header #%d" (header.Height)
    let hashInt = header.Hash |> fun x -> bigint (Array.append x [|0uy|]) // append 0 to make sure the result is > 0
    maybe {
        let t = target header.Bits
        do! (t <= maxTarget && t >= 0I) |> errorIfFalse "target is out of range"
        do! checkBits header
        do! hashInt < (target header.Bits) |> errorIfFalse "hash is above target difficulty"
        do! checkTimestamp header
    }

(** Check that the transaction is final *)
let checkLocktime (height: int) (timestamp: uint32) (tx: Tx) =
    let sequenceFinal = tx.TxIns |> Seq.map (fun txIn -> txIn.Sequence = 0xFFFFFFFF) |> Seq.exists id
    let lockTime = tx.LockTime
    (sequenceFinal || lockTime = 0u || (lockTime < 500000000u && (uint32)height >= lockTime) || (lockTime >= 500000000u && timestamp >= lockTime))

(**
Check the transactions from a block. These are expensive but they still aren't the worst because they don't access
the database or require script evaluation.
*)
let checkBlockTxs (utxoAccessor: IUTXOAccessor) (block: Block) =
    let bh = block.Header
    logger.InfoF "Checking block tx #%d %A" (bh.Height) (bh)
    maybe {
        // checkdup
        do! block.Txs.Any() |> errorIfFalse "Must have at least one transaction"
        do! block.Txs |> Seq.mapi (fun i tx -> if i = 0 then isCoinBase tx else not (isCoinBase tx)) |> Seq.forall id |> errorIfFalse "coinbase must be the first transaction"
        do! block.Txs |> Seq.map (fun tx -> (utxoAccessor.GetCount tx.Hash) = 0) |> Seq.forall id |> errorIfFalse "duplicate tx"
        do! block.Txs |> Seq.map (checkLocktime bh.Height bh.Timestamp) |> Seq.forall id |> errorIfFalse "has non final tx"
        let coinBaseScriptlen = block.Txs.[0].TxIns.[0].Script.Length
        do! (coinBaseScriptlen >= 2 && coinBaseScriptlen <= 100) |> errorIfFalse "coinbase script must be between 2 and 100 bytes"

        let scriptRuntime = new Script.ScriptRuntime(fun a _ -> a)
        let checkSigOpsCount = 
            block.Txs |> Seq.mapi (fun i tx ->
                let inputScripts = 
                    if i <> 0 
                    then 
                        tx.TxIns |> Seq.map (fun txIn ->
                            let utxo = utxoAccessor.GetUTXO txIn.PrevOutPoint
                            utxo |> Option.bind(fun utxo ->
                                let pubScript = utxo.TxOut.Script
                                if Script.isP2SH pubScript // For P2SH, also count the signature checks from the redeem script
                                then Some(scriptRuntime.RedeemScript pubScript)
                                else None
                                ) |?| txIn.Script
                            ) |> Seq.toArray
                    else Array.empty
                let outputScripts = tx.TxOuts |> Array.map (fun x -> x.Script)
                [inputScripts; outputScripts] 
                    |> Array.concat
                    |> Seq.map (fun script -> scriptRuntime.CheckSigCount script)
                    |> Seq.sum
            ) |> Seq.sum
        logger.DebugF "CheckSig count %d" checkSigOpsCount
        do! checkSigOpsCount <= maxCheckSigOpsCount |> errorIfFalse (sprintf "checkSig ops cannot occur more than %d times" maxCheckSigOpsCount)
        let merkleRoot = block.Txs |> Array.map (fun tx -> tx.Hash) |> computeMerkleRoot
        do! block.Header.MerkleRoot = merkleRoot |> errorIfFalse "merkle root does not match with header"
    }

(** Check the tx and update the UTXO set. These are the worst and also the very last checks.

I must use a temporary UTXO accessor for this because if any transaction of the block fails then the entire 
block is rejected and all the modification of the UTXO set must be rolled back.
*)
let updateBlockUTXO (utxoAccessor: IUTXOAccessor) (block: Block) =
    logger.InfoF "Processing block #%d" block.Header.Height
    use undoWriter = storeUndoBlock block

    maybe {
        let processUTXO = processUTXO utxoAccessor undoWriter
        let! fees = 
            block.Txs |> Array.mapi (fun i tx ->
                if i <> 0 
                    then checkScript utxoAccessor tx
                    else Some()
                |> Option.bind(fun _ -> processUTXO (i=0) block.Header.Height tx)
            ) |> Seq.toList |> Option.sequence |> Option.map Seq.sum
        let coinbase = totalOut block.Txs.[0]
        let totalReward = fees + reward block.Header.Height
        do! coinbase <= totalReward |> errorIfFalse "coinbase payout exceeds fees + reward"
        }

(**
## Canonical Signature / PubKey
*)
let checkDERInt (signature: byte[]) (offset: int) (len: int) =
    maybe {
        do! (signature.[offset-2] = 0x02uy) |> errorIfFalse "Non-canonical signature: value type mismatch"
        do! (len <> 0) |> errorIfFalse "Non-canonical signature: length is zero"
        do! ((signature.[offset] &&& 0x80uy) = 0uy) |> errorIfFalse "Non-canonical signature: value negative"
        do! (len <= 1 || (signature.[offset] <> 0x00uy) || ((signature.[offset+1] &&& 0x80uy) <> 0uy)) |> errorIfFalse "Non-canonical signature: value negative"
    }

let checkLowS (sBytes: byte[]) =
    let s = bigint (sBytes |> Array.rev)
    (s >= 0I && s < Script.halfN) |> errorIfFalse "Non-canonical signature: S value is unnecessarily high"

let checkCanonicalSignature (signature: byte[]) =
    maybe {
        do! (signature.Length >= 9) |> errorIfFalse "Non-canonical signature: too short"
        do! (signature.Length <= 73) |> errorIfFalse "Non-canonical signature: too long"
        let hashType = signature.Last() &&& ~~~0x80uy
        do! (hashType >= 1uy && hashType <= 3uy) |> errorIfFalse "unknown hashtype byte"
        do! (signature.[0] = 0x30uy) |> errorIfFalse "Non-canonical signature: wrong type"
        do! (signature.[1] = byte(signature.Length-3)) |> errorIfFalse "Non-canonical signature: wrong length marker"
        let rLen = int signature.[3]
        do! (rLen+5 < signature.Length) |> errorIfFalse "Non-canonical signature: S length misplaced"
        let sLen = int signature.[rLen+5]
        do! (rLen+sLen+7 = signature.Length) |> errorIfFalse "Non-canonical signature: R+S length mismatch"

        do! checkDERInt signature 4 rLen
        do! checkDERInt signature (6+rLen) sLen

        do! checkLowS signature.[6+rLen..5+rLen+sLen]
    }
