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
# Script Interpreter

*)
module Script

(**
This module implements an interpreter for the Bitcoin [Script][1] language. The link points to a good documentation
and I will just mention the main charateristics of this language. For more details, refer to the link.

Bitcoin script is a stack based primary arithmetic language. There are operators to push data to the stack and to
perform operations on the elements of the stack. The stack is made of arbitrary long binary strings. When used for
math operations, these byte strings are considered little endian big integers.

The language has IF/THEN/ELSE but no loops. It is therefore non Turing complete and program execution time is bounded.
Besides the classic operators, it has cryptographic functions such as hashing operators and signature verification.

When a transaction produces Outputs, they mention a value and a script. The later is similar to a program split in two. To 
spend the output, one must provide the other half of the program so that the full program executes successfully.
Another way to see it is to consider the output as a challenge and the spending transaction as the answer to the challenge.

Most of the transactions use the Pay-To-PubHash script. The script has a 20 byte long hash value. The spending transaction
must provide a pub key that hashes to the given value and a signature that matches both the pub key and the transaction content.

However, many other scripts exist even though only a few are considered standard. Standard scripts have been created to 
fulfill a particular use case and are recognized by the core client. The later will not relay transactions that contain
non standard scripts. This node does not care and will relay anything that validates successfully.

This part of Bitcoin has a few special cases that are due to bugs or bug fixes. I will mention their impact as I walk through the code.

[1]: https://en.bitcoin.it/wiki/Script
*)

(*** hide ***)
open System
open System.Collections.Generic
open System.Linq
open System.IO
open MoreLinq
open FSharpx
open FSharpx.Option
open Org.BouncyCastle.Utilities.Encoders
open Org.BouncyCastle.Crypto.Digests
open Org.BouncyCastle.Crypto.Parameters
open Org.BouncyCastle.Asn1
open Secp256k1
open Org.BouncyCastle.Crypto.Signers
open Protocol

(** 
##  Bitcoin Elliptic Curve secp256k1 
*)
let halfN = 57896044618658097711785492504343953926418782139537452191302581570759080747168I // Half the order of N

(** 
## Commonly used op codes.
Other op codes are implemented but are seldom used. I left their numeric value in the code.
 *)
let OP_DUP = 118uy // duplicate the last element on the stack
let OP_1 = 81uy // push 1
let OP_16 = 96uy // push 16
let OP_HASH160 = 169uy // Replace the top of the stack by its HASH-160 value (= SHA then RIPEMD)
let OP_DATA_20 = 20uy // Push the next 20 bytes on the stack
let OP_DATA_32 = 32uy // Push the next 32 bytes on the stack
let OP_EQUAL = 135uy // Compare the top two elements
let OP_EQUALVERIFY = 136uy // Do the same as above but fail the script if they are not equal
[<Literal>] 
let OP_CHECKSIG = 172uy // Single signature check
[<Literal>] 
let OP_CHECKSIGVERIFY = 173uy // As above and fail the script if the check doesn't succeed
[<Literal>] 
let OP_CHECKMULTISIG = 174uy // Multi signature check
[<Literal>] 
let OP_CHECKMULTISIGVERIFY = 175uy // As above and fail the script if the check doesn't succeed
let OP_DATA_65 = 65uy // Push the next 65 bytes on the stack
let OP_DATA_33 = 33uy // Push the next 33 bytes on the stack

(** Limits
*)
let stackMaxDepth = 1000
let maxPushLength = 520
let maxMultiSig = 20
let maxOpCodeCount = 201
let maxSigOpCount = 201
let maxScriptSize = 10000

(*** hide ***)
let scriptToHash (script: byte[]) =
    if script.Length = 25 && script.[0] = OP_DUP && script.[1] = OP_HASH160 && script.[2] = OP_DATA_20 && script.[23] = OP_EQUALVERIFY
        && script.[24] = OP_CHECKSIG then
           Some(script.[3..22]) 
    else
        None

(** 
## P2SH 
Pay to Script Hash is specified in [BIP-16][2] and has its own address space. P2SH is quite odd. The script itself is
half the story. It is first verified normally like any other script but then if the evaluator recognizes a special script pattern and he will do
something completely different. It is as if the program said `print hello` but then starts calculating pi.

Anyway, the idea is that the signing script gives the signatures but also the pub script that it is signing. Normally, 
you would have two scripts that once stitched together form a program. P2SH has a script inside a script. That script is provided as data
pushed into the stack but then that data is then poped and evaluated. Once again BIP-16 is
strange and I just scratched the surface. For more information refer to its specification.

[2]: https://github.com/bitcoin/bips/blob/master/bip-0016.mediawiki
*)
// This test is the first of a few checks
let isP2SH (script: byte[]) = script.Length = 23 && script.[0] = OP_HASH160 && script.[1] = OP_DATA_20 && script.[22] = OP_EQUAL

(** 
## Signature verification 

Signature verification is one of the most expensive steps in verification. Bitcoin core uses the OPENSSL library but
this application uses another implementation specially written for Bitcoin. It is significantly faster. However, it may
have incompatibilities.
*)
let ECDSACheck (txHash: byte[], pub: byte[], signature: byte[]) = 
    if signature.Length > 0 && pub.Length > 0 then // 0 length signature or pub keys crash the library
        let result = Signatures.Verify(txHash, signature, pub)
        result = Signatures.VerifyResult.Verified
    else false
    (* // The Bouncy Castle way
    let signer = new ECDsaSigner()
    let pubKey = new ECPublicKeyParameters(secp256k1Curve.Curve.DecodePoint pub, ecDomain)
    signer.Init(false, pubKey)
    let parser = new Asn1StreamParser(signature)
    let sequence = parser.ReadObject().ToAsn1Object() :?> DerSequence
    let r = sequence.[0] :?> DerInteger
    let s = sequence.[1] :?> DerInteger

    signer.VerifySignature(txHash, r.Value, s.Value)
    *)

(** 
## Stack 

The stack is implemented as a .NET List, i.e. a variable size array. Its elements are native byte arrays.
I added extension methods so that I can use the array as a stack with push & pop.
*)
type List<'a> with
    member x.Push(v: 'a) = 
        x.Add(v)
    member x.Pop() = 
        let v = x.Peek()
        x.RemoveAt(x.Count-1)
        v
    member x.Peek() = x.Item(x.Count-1)

type ByteList() =
    inherit List<byte[]>()
    member x.Push(v: byte[]) = 
        // logger.DebugF "Pushing %s" (Hex.ToHexString v)
        base.Add(v)

(** 
## Compute the signature hash 

The signature is applied on a given document. Instead of signing the entire document, one first calculates
a hash of the document and signs the hash. Bitcoin has a specific way to create the hash and it depends on 
a few parameters.

- the signature type. Most of the time, it's `SIGHASH_ALL` and the complete transaction is hashed. After that, 
changing a single byte of the transaction invalidates the signature. But it can be `SIGHASH_NONE` for which all
the outputs are blanked meaning that the signature will remain valid even if the outputs are changed. It can
also be `SIGHASH_SINGLE`. In the last case, all the outputs except the one with the same index as the input signature
are blanked. It means that all the outputs can be changed except one.
- anyone can pay: Another type of signature where the inputs are blanked giving a signature that remains valid even if more
inputs are added later.

The signing process is described [here][1].

[1]: https://en.bitcoin.it/wiki/OP_CHECKSIG
*)
let computeTxHash (tx: Tx) (index: int) (subScript: byte[]) (sigType: int) = 
    let mutable returnBuggyHash = false

    let anyoneCanPay = (sigType &&& 0x80) <> 0
    let sigHashType = 
        match sigType &&& 0x1F with
        | 2 -> 2uy
        | 3 -> 3uy
        | _ -> 1uy
    use oms = new MemoryStream()
    use writer = new BinaryWriter(oms)
    writer.Write(tx.Version)

    if anyoneCanPay then // reduce to a single input
        writer.WriteVarInt(1)
        let txIn2 = new TxIn(tx.TxIns.[index].PrevOutPoint, subScript, tx.TxIns.[index].Sequence)
        writer.Write(txIn2.ToByteArray())
    else // otherwise keep the other inputs but blank their script 
        writer.WriteVarInt(tx.TxIns.Length)
        tx.TxIns |> Array.iteri (fun i txIn ->
            let script = if i = index then subScript else Array.empty
            let txIn2 = 
                if sigHashType <> 1uy && i <> index then 
                    new TxIn(txIn.PrevOutPoint, script, 0)
                else
                    new TxIn(txIn.PrevOutPoint, script, txIn.Sequence)
            writer.Write(txIn2.ToByteArray())
        )
    
    match sigHashType with
    | 1uy ->
        writer.WriteVarInt(tx.TxOuts.Length)
        for txOut in tx.TxOuts do
            writer.Write(txOut.ToByteArray())
    | 2uy ->
        writer.WriteVarInt 0
    | 3uy -> // Normally in SIGHASH_SINGLE, the number of outputs must exceed the input index but if it's not the case
    // the reference client returns a hash of 1
        if index >= tx.TxOuts.Length then
            returnBuggyHash <- true
        else
            writer.WriteVarInt (index+1)
            for i in 0..index do
                if i < index then
                    let txOut = new TxOut(-1L, Array.empty)
                    writer.Write(txOut.ToByteArray())
                else
                    writer.Write(tx.TxOuts.[i].ToByteArray())
    | _ -> ignore() // cannot happen

    writer.Write(tx.LockTime)
    writer.Write(sigType)

    if returnBuggyHash then
        let hash = Array.zeroCreate<byte> 32
        hash.[0] <- 1uy
        hash
    else
        let data = oms.ToArray()
        dsha data

(** 
### Stack element conversion 

These functions are used when integers are put into the stack. They must be converted to byte[]. It's using
variable length byte strings in 1-complement encoding. Therefore there is positive 0 and negative 0. 
*)
let bigintToBytes (i: bigint) =
    let pos = abs i
    let bi = pos.ToByteArray()
    let posTrimIdx = revFind bi (fun b -> b <> 0uy)
    let iTrimIdx = 
        if (posTrimIdx >= 0 && (bi.[posTrimIdx] &&& 0x80uy) <> 0uy)
            then posTrimIdx + 1
            else posTrimIdx
    let bytes = bi.[0..iTrimIdx]
    if i < 0I then
        bytes.[iTrimIdx] <- bytes.[iTrimIdx] ||| 0x80uy
    bytes

let intToBytes (i: int) = bigintToBytes (bigint i)
let int64ToBytes (i: int64) = bigintToBytes (bigint i)
        
let bytesToInt (bytes: byte[]) =
    let b = Array.zeroCreate<byte> bytes.Length
    Array.Copy(bytes, b, bytes.Length)
    let neg = 
        if b.Length > 0 && b.[b.Length-1] &&& 0x80uy <> 0uy then
            b.[b.Length-1] <- b.[b.Length-1] &&& 0x7Fuy
            true
        else false

    let bi = bigint b
    if neg then -bi else bi

(** 
## Interpreter 

The interpreter takes a transaction hashing function at construction. When the function is applied, the index
of the input matters and will not give the same hash.
*)
type ScriptRuntime(getTxHash: byte[] -> int -> byte[]) =
    let evalStack = new ByteList()
    let altStack = new ByteList()
    let ifStack = new List<bool>()
    let mutable skipping = false
    let mutable codeSep = 0

(** 
### Basic stack helpers *)
    let checkDepth (stack: List<'a>) minDepth = 
        if stack.Count < minDepth then raise (ValidationException "not enough stack depth")
    let checkMaxDepth () =
        if evalStack.Count + altStack.Count > stackMaxDepth then raise (ValidationException "stack too deep")
    let popAsBool() = 
        checkDepth evalStack 1
        bytesToInt(evalStack.Pop()) <> 0I
    let verify() =
        if not (popAsBool()) 
        then raise (ValidationException "verification failed")
    let fail() = 
        evalStack.Push(intToBytes(0))
        raise (ValidationException "verification failed")
    let checkOverflow (bytes: byte[]) =
        if bytes.Length > 4 then fail()
        bytes
    let checkIfStackEmpty() = 
        if ifStack.Count > 0 then fail()

    let roll m =
        let n = m+1
        checkDepth evalStack n
        let i = evalStack.Count-n
        let top = evalStack.Item i
        evalStack.RemoveAt i
        evalStack.Push top

    let dup n depth =
        checkDepth evalStack (n+depth)
        for i in 1..n do
            evalStack.Push(evalStack.Item(evalStack.Count-n-depth))
        checkMaxDepth()

(** 
### Operators on stack elements 

They pull a certain number of elements from the stack, apply a function and then
push the result back to the stack. The number of arguments and the nature of the operation
varies with the helper.
*)
    let unaryOp (f: int64 -> int64) =
        checkDepth evalStack 1
        let arg = evalStack.Pop() |> checkOverflow |> bytesToInt |> int64
        f(arg) |> int64ToBytes |> evalStack.Push

    let binaryOp (f: int64 -> int64 -> int64) = 
        checkDepth evalStack 2
        let arg2 = evalStack.Pop() |> checkOverflow |> bytesToInt |> int64
        let arg1 = evalStack.Pop() |> checkOverflow |> bytesToInt |> int64
        f arg1 arg2 |> int64ToBytes |> evalStack.Push

    let logicalOp (f: bool -> bool -> bool) = 
        checkDepth evalStack 2
        let arg2 = evalStack.Pop() |> checkOverflow |> bytesToInt |> int |> fun x -> x <> 0
        let arg1 = evalStack.Pop() |> checkOverflow |> bytesToInt |> int |> fun x -> x <> 0
        f arg1 arg2 |> (fun x -> if x then 1 else 0) |> intToBytes |> evalStack.Push

    let binaryBoolOp (f: int -> int -> bool) = 
        checkDepth evalStack 2
        let arg2 = evalStack.Pop() |> checkOverflow |> bytesToInt |> int
        let arg1 = evalStack.Pop() |> checkOverflow |> bytesToInt |> int
        f arg1 arg2 |> (fun x -> if x then 1 else 0) |> intToBytes |> evalStack.Push

    let tertiaryOp (f: int -> int -> int -> int) = 
        checkDepth evalStack 3
        let arg3 = evalStack.Pop() |> checkOverflow |> bytesToInt |> int
        let arg2 = evalStack.Pop() |> checkOverflow |> bytesToInt |> int
        let arg1 = evalStack.Pop() |> checkOverflow |> bytesToInt |> int
        f arg1 arg2 arg3 |> intToBytes |> evalStack.Push

    let hashOp (f: byte[] -> byte[]) =
        checkDepth evalStack 1
        let data = evalStack.Pop()
        data |> f |> evalStack.Push

(** 
### Remove data that matches a predicate 

This function parses the script quickly and identifies the data parts. The predicate is evaluated
on the data part and if it returns true, the data is *removed* from the script. Surprisingly, there are
a few places where the standard dictates this behavior.

It also removes any instance of OP_CODESEPARATOR
*)
    let removeData (script: byte[]) (pred: byte[] -> bool) = 
        let dataList = new List<byte[]>()
        use ms = new MemoryStream(script)
        use reader = new BinaryReader(ms)
        (
            try
                use oms = new MemoryStream()
                use writer = new BinaryWriter(oms)

                let rec removeDataInner (): byte[] =
                    if ms.Position < ms.Length then
                        let b = reader.ReadByte()
                        let c = int b
                        if c >= 1 && c <= 78 then
                            let startPos = ms.Position-1L
                            let len = 
                                match c with
                                | 76 -> int (reader.ReadByte())
                                | 77 -> int (reader.ReadInt16())
                                | 78 -> reader.ReadInt32()
                                | x -> x
                            let canonical = 
                                if len < 75 then len
                                elif len < 0xFF then 76
                                elif len < 0xFFFF then 77
                                else 78

                            let data = reader.ReadBytes(len)
                            if canonical <> c || not (pred(data)) then
                                let lenRead = int(ms.Position - startPos)
                                ms.Seek(startPos, SeekOrigin.Begin) |> ignore
                                writer.Write(reader.ReadBytes(lenRead))
                            dataList.Add(data)
                        elif b <> 171uy then
                            writer.Write(b)
                        removeDataInner()
                    else
                        oms.ToArray()

                let script = removeDataInner()
                ms.Dispose()
                (true, script, dataList.ToArray())
            with 
            | e -> 
                logger.DebugF "Invalid script %A" e
                let currentPos = int ms.Position-1
                (false, script.[0..currentPos], dataList.ToArray())
        )

(** 
### Remove the signature bytes from a script 
Because a signature cannot be signed, the algorithm always removes any occurence of the signature
before passing the script to the hashing function
*)
    let removeSignatures (script: byte[]) (signatures: HashSet<byte[]>) = 
        let subScript = 
            if codeSep <> 0
                then script.[codeSep..]
                else script
        let (success, script, _) = removeData subScript (fun data -> signatures.Contains data)
        if not success then fail() 
        script

(** 
### Calculate the number of OP_CHECKSIG 
This is to protect against scripts that have a large number of OP_CHECKSIG. They are expensive to execute
and without a limit can be used to make the node overwork. It's an anti-DoS measure but is quite painful to
check in practice as every script must be checked even if the tx output is never spent.
*)
    let scriptCheckSigCount (script: byte[]) =
        let (_, ops, _) = removeData script (fun _ -> true)
        ops.Prepend(0xFFuy).Window(2) |> Seq.map (fun x -> // Prepend a dummy byte to deal with boundary case
            match x.ToArray() with
            | [|op1; op2|] ->
                match op2 with
                | OP_CHECKSIG | OP_CHECKSIGVERIFY -> 1 // single signature check counts as 1
                | OP_CHECKMULTISIG | OP_CHECKMULTISIGVERIFY -> // if preceeded by OP_X, multi-sig counts as x, 
                    if op1 >= OP_1 && op1 <= OP_16 // otherwise counts as 20
                    then int (op1-OP_1)
                    else 20
                | _ -> 0
            | _ -> 0
            ) |> Seq.sum

(** 
### Single signature verification 
The signature hash type is the last byte of the signature and is always removed from it. Then any occurence
of the signature itself is removed from the pub script before the tx hash is calculated.
*)
    let checksigInner pubScript pub (signature: byte[]) = 
        let sigType = if signature.Length > 0 then signature.[signature.Length-1] else 0uy
        let txHash = getTxHash pubScript (int sigType)
        ECDSACheck(txHash, pub, signature)

    let checksig script pub signature = 
        let pubScript = removeSignatures script (new HashSet<byte[]>([signature], hashCompare))
        checksigInner pubScript pub signature

(** 
### Multi signature verification 

In a multi sig, every pub key is checked against the signatures and then discarded. Eventually, all the
signatures must match a pub key. Because of this order of evaluation, signatures have to be provided in the same
order as the pub keys.
*)
    let checkmultisig script (pubs: byte[][]) (sigs: byte[] list) = 
        let pubScript = removeSignatures script (new HashSet<byte[]>(sigs, hashCompare))

        let checkOneSig (pubs: byte[] list) (signature: byte[]) = 
            pubs |> List.tryFindIndex (fun pub -> checksigInner pubScript pub signature)
            |> Option.map (fun index -> pubs |> List.splitAt index |> snd |> List.tail)
                
        sigs |> Option.foldM checkOneSig (pubs |> Array.toList) |> Option.isSome

(** 
## Evaluate a script 

It's the main eval loop using tail recursion. The `eval` function reads one byte from the program and decide
if it's data or instruction. If it's data, one or more bytes are then read. If it's instruction, it's always a single
byte. It's an important trick. When the code must be skipped because it is on the wrong side of a If/then/else, 
the function can quickly jump to the next code.
*)
    let eval (pushOnly: bool) (script: byte[]) =
        codeSep <- 0
        if script.Length > maxScriptSize then fail()
        let ms = new MemoryStream(script)
        let reader = new BinaryReader(ms)

        let rec innerEval (opCount: int) =
            let mutable multiSigOps = 0
            if opCount > maxOpCodeCount then fail()
            if ms.Position < ms.Length then
                let c = int (reader.ReadByte())
                // logger.DebugF "Stack size %d op = %x opc = %d" evalStack.Count c opCount
                if c = 0 then
                    if not skipping then
                        evalStack.Push(Array.empty)
                elif c = 79 then
                    if not skipping then
                        evalStack.Push([| 0x81uy |])
(** 
### Push data 

There are different size of push data, 1, 2, or 4 bytes
*)
                elif c >= 1 && c <= 78 then
                    let len = 
                        match c with
                        | 76 -> int (reader.ReadByte())
                        | 77 -> int (reader.ReadInt16())
                        | 78 -> reader.ReadInt32()
                        | x -> x
                    let data = reader.ReadBytes(len)
                    if data.Length < len then raise (ValidationException "Not enough data to read")
                    if len > maxPushLength then raise (ValidationException "PushData exceeds 520 bytes")
                    if not skipping then
                        evalStack.Push(data)
(** 
### OP_1 etc *)

                elif c >= 81 && c <= 96 then
                    if not skipping then
                        evalStack.Push(intToBytes (c-80))
                elif pushOnly then fail()
(** 
### IF/THEN/ELSE 
Some special care must be given to if/then/else. They can nest so the 
logic must accomodate that. The parser keeps a state variable `skipping` which tells it whether instructions and push data
must be skipped or not. On a IF, the current value of `skipping` is pushed on a 'if' stack and if the parser is not currently
skipping, the top of the stack is read. In other words, the if statement is evaluated if it was not part of a dead-if branch, but
the push itself is always done in order for the parser to keep track of the if/endif nesting. Same thing happens on an else. `skipping`
is flipped only if the enclosing block isn't skipped too. The parser knows that by peeking at the top of the if-stack.
*)

                elif c = 99 || c = 100 then
                    ifStack.Push(skipping)
                    if not skipping then
                        skipping <- not (popAsBool())
                        if c = 100 then skipping <- not skipping
                elif c = 103 then
                    checkDepth ifStack 1
                    if not (ifStack.Peek()) then skipping <- not skipping
                elif c = 104 then
                    checkDepth ifStack 1
                    skipping <- ifStack.Pop()
                elif c >= 176 && c <= 185 then ignore()
                elif 
                    match c with
                    | 101 | 102 
                    | 126 | 127 | 128 | 129 | 131 | 132 | 133 | 134
                    | 141 | 142 | 149 | 150 | 151 | 152 | 153 -> true
                    | _ -> false
                    then fail()
                elif not skipping then
(** 
### Stack operators 

These do various permutations of the stack element and other simple stack manipulation. The parser also maintains a alt-stack but it
is cleared between the parts of the script evaluation.
*)
                    match c with
                    | 97 -> ignore()
                    | 105 -> verify()
                    | 106 | 80 | 98 | 137 | 138 -> fail()
                    | 107 -> 
                        checkDepth evalStack 1
                        let top = evalStack.Pop()
                        altStack.Push(top)
                    | 108 ->
                        checkDepth altStack 1
                        let top = altStack.Pop()
                        evalStack.Push(top)
                    | 109 ->
                        checkDepth evalStack 2
                        evalStack.Pop() |> ignore
                        evalStack.Pop() |> ignore
                    | 110 -> dup 2 0
                    | 111 -> dup 3 0
                    | 112 -> dup 2 2
                    | 113 -> 
                        roll 5
                        roll 5
                    | 114 ->
                        roll 3
                        roll 3
                    | 115 ->
                        checkDepth evalStack 1
                        let t = evalStack.Peek()
                        evalStack.Push t
                        if popAsBool() then evalStack.Push t
                    | 116 -> evalStack.Push(intToBytes (evalStack.Count))
                    | 117 ->
                        checkDepth evalStack 1
                        evalStack.Pop() |> ignore
                    | 118 -> 
                        checkDepth evalStack 1
                        evalStack.Push(evalStack.Peek())
                    | 119 -> 
                        checkDepth evalStack 2
                        evalStack.RemoveAt(evalStack.Count-2)
                    | 120 ->
                        checkDepth evalStack 2
                        evalStack.Push(evalStack.Item(evalStack.Count-2))
                    | 121 ->
                        let n = int(bytesToInt(evalStack.Pop()))
                        if n < 0 then fail()
                        checkDepth evalStack (n+1)
                        evalStack.Push(evalStack.Item(evalStack.Count-1-n))
                    | 122 ->
                        let n = int(bytesToInt(evalStack.Pop()))
                        if n < 0 then fail()
                        roll n
                    | 123 -> roll 2
                    | 124 ->
                        checkDepth evalStack 2
                        let a = evalStack.Pop()
                        let b = evalStack.Pop()
                        evalStack.Push a
                        evalStack.Push b
                    | 125 ->
                        checkDepth evalStack 2
                        let top = evalStack.Peek()
                        evalStack.Insert(evalStack.Count-2, top)
                    | 130 -> 
                        checkDepth evalStack 1
                        let top = evalStack.Peek()
                        evalStack.Push(intToBytes top.Length)
                    | 135 | 136 ->
                        checkDepth evalStack 2
                        let a = evalStack.Pop()
                        let b = evalStack.Pop()
                        let eq = if hashCompare.Equals(a, b) then 1 else 0
                        evalStack.Push(intToBytes eq)
                        if c = 136 then verify()
(** 
### Arithmetic operators *)
                    | 139 ->
                        unaryOp(fun x -> x+1L)
                    | 140 ->
                        unaryOp(fun x -> x-1L)
                    | 143 ->
                        unaryOp(fun x -> -x)
                    | 144 ->
                        unaryOp(fun x -> if x > 0L then x else -x)
                    | 145 ->
                        unaryOp(fun x -> if x <> 0L then 0L else 1L)
                    | 146 ->
                        unaryOp(fun x -> if x <> 0L then 1L else 0L)
                    | 147 ->
                        binaryOp(fun x y -> x+y)
                    | 148 ->
                        binaryOp(fun x y -> x-y)
(** 
### Logical operators *)
                    | 154 ->
                        logicalOp(fun x y -> x&&y)
                    | 155 ->
                        logicalOp(fun x y -> x||y)
                    | 156 ->
                        logicalOp(fun x y -> x=y)
                    | 157 ->
                        logicalOp(fun x y -> x=y)
                        verify()
                    | 158 ->
                        binaryBoolOp(fun x y -> x<>y)
                    | 159 ->
                        binaryBoolOp(fun x y -> x<y)
                    | 160 ->
                        binaryBoolOp(fun x y -> x>y)
                    | 161 ->
                        binaryBoolOp(fun x y -> x<=y)
                    | 162 ->
                        binaryBoolOp(fun x y -> x>=y)
                    | 163 ->
                        binaryOp(fun x y -> if x<y then x else y)
                    | 164 ->
                        binaryOp(fun x y -> if x>y then x else y)
                    | 165 ->
                        tertiaryOp(fun x a b -> if x>=a && x<b then 1 else 0)
(** 
### Hashing operators *)
                    | 166 ->
                        hashOp(ripe160)
                    | 167 ->
                        hashOp(sha1)
                    | 168 ->
                        hashOp(sha256)
                    | 169 ->
                        hashOp(hash160)
                    | 170 ->
                        hashOp(dsha)
                    | 171 ->
                        codeSep <- int(reader.BaseStream.Position)
(** 
### Signature verification *)
                    | 172 | 173 ->
                        checkDepth evalStack 2
                        let pub = evalStack.Pop()
                        let signature = evalStack.Pop()
                        let check = checksig script pub signature
                        evalStack.Push(intToBytes(if check then 1 else 0))
                        if c = 173 then verify()
                    | 174 | 175 ->
                        checkDepth evalStack 1
                        let nPubs = int(bytesToInt(evalStack.Pop()))
                        multiSigOps <- nPubs
                        if nPubs > maxMultiSig then fail()
                        checkDepth evalStack nPubs
                        let pubs = seq { for _ in 1..nPubs do yield evalStack.Pop() } |> Seq.toArray
                        let nSigs = int(bytesToInt(evalStack.Pop()))
                        if nSigs > nPubs then fail()
                        checkDepth evalStack nSigs
                        let sigs = seq { for _ in 1..nSigs do yield evalStack.Pop() } |> Seq.toList
                        checkDepth evalStack 1
                        let dummy = evalStack.Pop()
                        if dummy.Length > 0 then fail()
                        let check = checkmultisig script pubs sigs
                        evalStack.Push(intToBytes(if check then 1 else 0))
                        if c = 175 then verify()
                    | _ -> fail()

                innerEval ((if c < 97 then opCount else (opCount+1))+multiSigOps)

        innerEval 0
        checkIfStackEmpty()

(** 
## P2SH special case 

After the P2SH script is evaluated normally, the stack is cleared. The signature script is then reevaluated
and the last stack element poped from it. It becomes the new script to evaluate successfully.

TODO: Enforce strict BIP16 rules: No other opcode other than push data and redeem script limit
*)
    let evalP2SH (script: byte[]) =
        evalStack.Clear()
        eval true script
        checkDepth evalStack 1
        let redeemScript = evalStack.Pop()
        eval false redeemScript
        popAsBool()

    let redeemScript (script: byte[]) =
        let (_, _, data) = removeData script (fun _ -> true)
        data |> Array.last

    member x.Verify(inScript: byte[], outScript: byte[]) = 
        try
            eval false inScript
            altStack.Clear() // bitcoin core does that
            ifStack.Clear() // 
            eval false outScript
            let res = popAsBool()
            res && (not (isP2SH outScript) || evalP2SH inScript)
        with
        | :? ValidationException -> false

    member x.CheckSigCount (script: byte[]) = scriptCheckSigCount script
    member x.RedeemScript (script: byte[]) = redeemScript script
    static member IsP2SH (script: byte[]) = isP2SH script

