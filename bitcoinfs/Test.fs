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
# Unit Tests from the Core Client
*)

module Test.Script

(*** hide ***)
open System
open System.Collections.Generic
open System.IO
open System.Text
open FSharp.Data
open Org.BouncyCastle.Utilities.Encoders
open NUnit.Framework
open FsUnit
open Protocol
open Script
open Checks

let opCodes = 
    Map.ofSeq [
        ("0", 0);
        ("FALSE", 0);
        ("PUSHDATA1", 76);
        ("PUSHDATA2", 77);
        ("PUSHDATA4", 78);
        ("1NEGATE", 79);
        ("1", 81);
        ("TRUE", 81);
        ("2", 82);
        ("3", 83);
        ("4", 84);
        ("5", 85);
        ("6", 86);
        ("7", 87);
        ("8", 88);
        ("9", 89);
        ("10", 90);
        ("11", 91);
        ("12", 92);
        ("13", 93);
        ("14", 94);
        ("15", 95);
        ("16", 96);
        ("NOP", 97);
        ("IF", 99);
        ("NOTIF", 100);
        ("ELSE", 103);
        ("ENDIF", 104);
        ("VERIFY", 105);
        ("RETURN", 106);
        ("TOALTSTACK", 107);
        ("FROMALTSTACK", 108);
        ("IFDUP", 115);
        ("DEPTH", 116);
        ("DROP", 117);
        ("DUP", 118);
        ("NIP", 119);
        ("OVER", 120);
        ("PICK", 121);
        ("ROLL", 122);
        ("ROT", 123);
        ("SWAP", 124);
        ("TUCK", 125);
        ("2DROP", 109);
        ("2DUP", 110);
        ("3DUP", 111);
        ("2OVER", 112);
        ("2ROT", 113);
        ("2SWAP", 114);
        ("CAT", 126);
        ("SUBSTR", 127);
        ("LEFT", 128);
        ("RIGHT", 129);
        ("SIZE", 130);
        ("INVERT", 131);
        ("AND", 132);
        ("OR", 133);
        ("XOR", 134);
        ("EQUAL", 135);
        ("EQUALVERIFY", 136);
        ("1ADD", 139);
        ("1SUB", 140);
        ("2MUL", 141);
        ("2DIV", 142);
        ("NEGATE", 143);
        ("ABS", 144);
        ("NOT", 145);
        ("0NOTEQUAL", 146);
        ("ADD", 147);
        ("SUB", 148);
        ("MUL", 149);
        ("DIV", 150);
        ("MOD", 151);
        ("LSHIFT", 152);
        ("RSHIFT", 153);
        ("BOOLAND", 154);
        ("BOOLOR", 155);
        ("NUMEQUAL", 156);
        ("NUMEQUALVERIFY", 157);
        ("NUMNOTEQUAL", 158);
        ("LESSTHAN", 159);
        ("GREATERTHAN", 160);
        ("LESSTHANOREQUAL", 161);
        ("GREATERTHANOREQUAL", 162);
        ("MIN", 163);
        ("MAX", 164);
        ("WITHIN", 165);
        ("RIPEMD160", 166);
        ("SHA1", 167);
        ("SHA256", 168);
        ("HASH160", 169);
        ("HASH256", 170);
        ("CODESEPARATOR", 171);
        ("CHECKSIG", 172);
        ("CHECKSIGVERIFY", 173);
        ("CHECKMULTISIG", 174);
        ("CHECKMULTISIGVERIFY", 175);
        ("RESERVED", 80);
        ("VER", 98);
        ("VERIF", 101);
        ("VERNOTIF", 102);
        ("RESERVED1", 137);
        ("RESERVED2", 138);
        ("NOP1", 176);
        ("NOP2", 177);
        ("NOP3", 178);
        ("NOP4", 179);
        ("NOP5", 180);
        ("NOP6", 181);
        ("NOP7", 182);
        ("NOP8", 183);
        ("NOP9", 184);
        ("NOP10", 185)]

(**
## Script tests
*)
let parseScript (scriptString: string) = 
    let tokens = scriptString.Split([|' '|], StringSplitOptions.RemoveEmptyEntries) |> Array.toList
    let scriptBytes = new MemoryStream()
    let scriptWriter = new BinaryWriter(scriptBytes)

    let intToBytes (i: bigint) =
        let pos = abs i
        let bi = pos.ToByteArray()
        let posTrimIdx = revFind bi (fun b -> b <> 0uy)
        let iTrimIdx = 
            if (bi.[posTrimIdx] &&& 0x80uy) <> 0uy
                then posTrimIdx + 1
                else posTrimIdx
        let bytes = bi.[0..iTrimIdx]
        if i < 0I then
            bytes.[iTrimIdx] <- bytes.[iTrimIdx] ||| 0x80uy
        bytes

    let rec parseOne (tokens: string list) =
        match tokens with 
        | [] -> ignore()
        | token::rest -> 
            let c = token.[0]
            let code = (opCodes |> Map.tryFind (if token.StartsWith("OP_") then token.[3..] else token))
            if code.IsSome then
                scriptWriter.Write(byte code.Value)
            elif c = '\'' then
                let message = ASCIIEncoding.ASCII.GetBytes (token.[1..token.Length-2])
                let len = message.Length
                if len <= 75
                then scriptWriter.Write(byte message.Length)
                else 
                    scriptWriter.Write(0x4dy)
                    scriptWriter.Write(uint16 message.Length)
                scriptWriter.Write(message)
            elif token.StartsWith("0x")
            then
                let hex = Hex.Decode token.[2..]
                scriptWriter.Write(hex)
            else
                let (s, n) = bigint.TryParse token
                assert s
                if n >= 0I && n <= 16I
                then 
                    let code = byte opCodes.[token]
                    scriptWriter.Write(code)
                else
                    let bytes = intToBytes n
                    scriptWriter.Write(byte bytes.Length)
                    scriptWriter.Write(bytes)
            parseOne rest

    parseOne tokens
    scriptBytes.ToArray()

[<TestFixture>]
type ``Given a ScriptRuntime`` ()=
    let validJson = JsonValue.Load(__SOURCE_DIRECTORY__ + "/../paket-files/bitcoin/bitcoin/src/test/data/script_valid.json")
    let invalidJson = JsonValue.Load(__SOURCE_DIRECTORY__ + "/../paket-files/bitcoin/bitcoin/src/test/data/script_invalid.json")

    let evalScript (sigScript: string) (pubScript: string) = 
        let interpreter = new ScriptRuntime(fun a _ -> a)
        interpreter.Verify(parseScript sigScript, parseScript pubScript)

    [<Test>] 
    member x.``when evaluating scripts from a valid jsonfile, I should not fail.`` () =
        validJson.AsArray() |> Array.iteri(fun i s ->
            if i = 278 then ignore()
            match s with 
            | JsonValue.Array arr ->
                let inScript = arr.[0].AsString()
                let outScript = arr.[1].AsString()
                evalScript inScript outScript |> should equal true
            )

    [<Test>] 
    member x.``when evaluating scripts from a invalid jsonfile, I should fail.`` () =
        for s in invalidJson.AsArray() do
            match s with 
            | JsonValue.Array arr ->
                let inScript = arr.[0].AsString()
                let outScript = arr.[1].AsString()
                evalScript inScript outScript |> should equal false

(**
## Signature hash tests
*)
[<TestFixture>]
type ``Given a Tx Hashing function`` ()=
    let validJson = JsonValue.Load(__SOURCE_DIRECTORY__ + "/../paket-files/bitcoin/bitcoin/src/test/data/sighash.json")

    [<Test>] 
    member x.``when evaluating hashes from a valid json file, I should not fail.`` () =
        for s in validJson.AsArray() do
            match s with
            | JsonValue.Array [| txJ; scriptJ; indexJ; hashTypeJ; resultJ |] ->
            let txHex = Hex.Decode(txJ.AsString())
            let script = Hex.Decode(scriptJ.AsString())
            let index = indexJ.AsInteger()
            let hashType = hashTypeJ.AsInteger()
            let result = resultJ.AsString()
            let tx = ParseByteArray txHex Tx.Parse
            let scriptNoCodeSep = script |> Array.filter(fun b -> b <> 0xabuy)
            let hash = computeTxHash tx index scriptNoCodeSep hashType |> Array.rev
            let hashHex = Hex.ToHexString hash
            hashHex |> should equal result
            | _ -> ignore()


(**
## Transaction parsing tests
*)
[<TestFixture>]
type ``Given a Tx`` ()=
    let validJson = JsonValue.Load(__SOURCE_DIRECTORY__ + "/../paket-files/bitcoin/bitcoin/src/test/data/tx_valid.json")
    let invalidJson = JsonValue.Load(__SOURCE_DIRECTORY__ + "/../paket-files/bitcoin/bitcoin/src/test/data/tx_invalid.json")

    [<Test>] 
    member x.``when verifying transactions from a valid json file, I should not fail.`` () =
        for s in validJson.AsArray() do
            match s with
            | JsonValue.Array [| prevInputsJ; txHexJ; flagsJ |] ->
                let txHex = Hex.Decode(txHexJ.AsString())
                let tx = ParseByteArray txHex Tx.Parse
                let prevOutputsMap = new Dictionary<OutPoint, byte[]>(new Mempool.OutpointCompare())
                prevInputsJ.AsArray() |> Array.map(fun p ->
                    match p with
                    | JsonValue.Array [| JsonValue.String prevHashJ; JsonValue.Number index; JsonValue.String script |] ->
                        (new OutPoint(hashFromHex prevHashJ, int index), parseScript script)
                    | _ -> raise (new ArgumentException())
                ) |> Seq.iter(fun (k, v) -> prevOutputsMap.Add(k, v))
                let verified = 
                    tx.TxIns |> Array.mapi(fun i txIn ->
                        let outpoint = txIn.PrevOutPoint
                        let script = prevOutputsMap.[outpoint]
                        let scriptInterpreter = new ScriptRuntime(computeTxHash tx i)
                        scriptInterpreter.Verify(txIn.Script, script)
                    ) |> Seq.forall id
                (flagsJ.AsString() = "NONE" || verified) |> should equal true
            | _ -> ignore()

    [<Test>] 
    member x.``when verifying transactions from an invalid json file, I should not fail.`` () =
        for s in invalidJson.AsArray() do
            match s with
            | JsonValue.Array [| prevInputsJ; txHexJ; flagsJ |] ->
                let txHex = Hex.Decode(txHexJ.AsString())
                let tx = ParseByteArray txHex Tx.Parse
                let prevOutputsMap = new Dictionary<OutPoint, byte[]>(new Mempool.OutpointCompare())
                prevInputsJ.AsArray() |> Array.map(fun p ->
                    match p with
                    | JsonValue.Array [| JsonValue.String prevHashJ; JsonValue.Number index; JsonValue.String script |] ->
                        (new OutPoint(hashFromHex prevHashJ, int index), parseScript script)
                    | _ -> raise (new ArgumentException())
                ) |> Seq.iter(fun (k, v) -> prevOutputsMap.Add(k, v))
                let verified = 
                    tx.TxIns |> Array.mapi(fun i txIn ->
                        let outpoint = txIn.PrevOutPoint
                        let script = prevOutputsMap.[outpoint]
                        let scriptInterpreter = new ScriptRuntime(computeTxHash tx i)
                        scriptInterpreter.Verify(txIn.Script, script)
                    ) |> Seq.forall id
                let ok = (flagsJ.AsString() = "NONE" || verified)
                if ok then
                    printfn "%A" txHexJ
            | _ -> ignore()

(**
## Canonical signature tests
*)
[<TestFixture>]
type ``Given a Signature file`` ()=
    let validJson = JsonValue.Load(__SOURCE_DIRECTORY__ + "/../paket-files/bitcoin/bitcoin/src/test/data/sig_canonical.json")

    [<Test>] 
    member x.``when verifying signatures from a valid json file, I should not fail.`` () =
        for s in validJson.AsArray() do
            let signature = Hex.Decode (s.AsString())
            let r = checkCanonicalSignature signature
            printfn "%A %A" s r

        
        
