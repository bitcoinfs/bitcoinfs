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
# Wallet
*)
module Wallet

(*** hide ***)
open System
open System.Collections
open System.Text
open System.Linq
open System.IO
open System.Net
open Org.BouncyCastle.Crypto.Digests
open Org.BouncyCastle.Crypto.Macs
open Org.BouncyCastle.Crypto.Parameters
open Org.BouncyCastle.Math.EC
open Org.BouncyCastle.Utilities.Encoders
open Db
open Protocol
open Murmur
open Script

let secp256k1Curve = Org.BouncyCastle.Asn1.Sec.SecNamedCurves.GetByName("secp256k1")
let ecDomain = new ECDomainParameters(secp256k1Curve.Curve, secp256k1Curve.G, secp256k1Curve.N)

    
let createBigInt (bytes: byte[]) = new Org.BouncyCastle.Math.BigInteger(1, bytes)

(**
## Utilities to work with addresses
The rest of the code is only dealing with binary data whether in the form of hashes or keys. Base58 encoding
is human readable but not as efficient for storing and comparison.
*)
let base58alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
let fromBase58 (base58: string) =
    let bi = 
        base58.ToCharArray()
            |> Seq.fold (fun acc digit ->
                acc * 58I + bigint (base58alphabet.IndexOf(digit))
                ) 0I
    let biBytes = bi.ToByteArray() |> Array.rev
    let leading0Out = base58.ToCharArray() |> Seq.takeWhile (fun c -> c = '1') |> Seq.length // how many leading 0 we want
    let leading0In = biBytes |> Seq.takeWhile (fun d -> d = 0uy) |> Seq.length // how many leading 0 we have so far
    let delta0 = leading0Out - leading0In
    if delta0 > 0 then // adjust the number of leading 0 by adding or truncating
        [(Array.zeroCreate<byte> delta0); biBytes] |> Array.concat
    elif delta0 < 0 then
        biBytes.[-delta0..]
    else
        biBytes

let toBase58 (bytes: byte[]) =
    let bi = new bigint(bytes |> Array.rev)
    let sb = new StringBuilder()
    Protocol.iterate (fun (bi: bigint) ->
            let (div, rem) = bigint.DivRem (bi, 58I)
            sb.Append(base58alphabet.[int rem]) |> ignore
            div
            )
            bi
        |> Seq.takeWhile(fun bi -> bi <> 0I) |> Seq.length |> ignore
    bytes |> Seq.takeWhile (fun b -> b = 0uy) |> Seq.iter (fun _ -> sb.Append '1' |> ignore) // add leading 1s
    new string(sb.ToString().ToCharArray() |> Array.rev)

let to58Check (version: byte) (bytes: byte[]) =
    let bytesVer = [[| version |]; bytes] |> Array.concat
    let checksum = (dsha bytesVer).[0..3]
    [bytesVer; checksum] |> Array.concat

exception InvalidBase58CheckException

let from58Check (version: byte) (bytes: byte[]) =
    if bytes.Length < 4 then raise InvalidBase58CheckException
    let v = bytes.[0]
    let c = bytes.[bytes.Length-4..]
    let bs = bytes.[0..bytes.Length-5]
    let checksum = (dsha bs).[0..3]
    if v <> version || not (hashCompare.Equals(checksum, c)) then raise InvalidBase58CheckException
    bs.[1..]

let fromBase58Check (version: byte) = fromBase58 >> (from58Check version)
let toBase58Check (version: byte) = toBase58 << (to58Check version)

let toAddress = hash160 >> (toBase58Check 0uy)

(**
## [BIP-32][2] Hierarchical Deterministic Wallets

[2]: https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki
*)
let hmacOf(chain: byte[])(fnChain: unit -> byte[]) =
    let sha512 = new Sha512Digest()
    let hmac = new HMac(sha512)
    hmac.Init(new KeyParameter(chain))
    let data = fnChain()
    hmac.BlockUpdate(data, 0, data.Length)
    let res = Array.zeroCreate 64
    hmac.DoFinal(res, 0) |> ignore
    (res.[0..31], res.[32..])

exception BIP32Exception

type BIP32PrivKeyExt(secret: Org.BouncyCastle.Math.BigInteger, chain: byte[]) =
    let toPub() = 
        let p = ecDomain.G.Multiply(secret)
        new FpPoint(ecDomain.Curve, p.X, p.Y, true)

    let toPrivChild index =
        let (l, r) =
                hmacOf chain (fun () ->
                use ms = new MemoryStream()
                use writer = new BinaryWriter(ms)
                if index < 0 then
                    writer.Write(0uy)
                    writer.Write(secret.ToByteArrayUnsigned())
                else
                    writer.Write(toPub().GetEncoded())
                writer.Write(IPAddress.HostToNetworkOrder(index))
                ms.ToArray()
            )
        let childSecret = createBigInt(l).Add(secret).Mod(ecDomain.N)
        new BIP32PrivKeyExt(childSecret, r)

    member x.ToPublic() = toPub()
    member x.ToPrivChild(index: int) = toPrivChild index
    member x.ToPublicExt() = new BIP32PublicExt(x.ToPublic(), chain)

and BIP32PublicExt(point: ECPoint, chain: byte[]) =
    let toPublicChild index =
        let (l, r) =
                hmacOf chain (fun () ->
                use ms = new MemoryStream()
                use writer = new BinaryWriter(ms)
                if index < 0 then raise BIP32Exception
                else
                    writer.Write(point.GetEncoded())
                writer.Write(IPAddress.HostToNetworkOrder(index))
                ms.ToArray()
            )
        let childPoint = ecDomain.G.Multiply(createBigInt(l)).Add(point)
        new BIP32PublicExt(FpPoint(ecDomain.Curve, childPoint.X, childPoint.Y, true), r)

    override x.ToString() = sprintf "(%s,%s)" (point.GetEncoded() |> Hex.ToHexString) (chain |> Hex.ToHexString)
    member x.ToPublic() = point
    member x.ToPublicChild(index: int) = toPublicChild index

let BIP32master (master: byte[]) =
     let (l, r) = hmacOf(Encoding.ASCII.GetBytes "Bitcoin seed") (fun () -> master)
     new BIP32PrivKeyExt(new Org.BouncyCastle.Math.BigInteger(1, l), r)

(**
## [Electrum][3] Wallet

Electrum style deterministic wallets. It requires the master public key
[3]: https://electrum.org/
*)
type Electrum(mpub: byte[], group: int) =
    let deriveExp index =
        use ms = new MemoryStream()
        use writer = new BinaryWriter(ms)
        let prefix = sprintf "%d:%d:" index group
        writer.Write(Encoding.ASCII.GetBytes prefix)
        writer.Write(mpub)
        ms.ToArray() |> dsha |> createBigInt
    let masterPoint = ecDomain.Curve.CreatePoint(createBigInt(mpub.[0..31]), createBigInt(mpub.[32..]), true)
    
    member x.Derive(index: int) = ecDomain.G.Multiply(deriveExp index).Add(masterPoint)
        
(**
## [Armory][4] Wallet

Armory style deterministic wallets. It requires the public master key and the chain code
[4]: https://bitcoinarmory.com/
*)
type Armory(chain: byte[]) =
    let derive (pkey: byte[]) =
        let point = ecDomain.Curve.DecodePoint pkey
        let pkeyUnc = new FpPoint(ecDomain.Curve, point.X, point.Y, false)
        let chainMod = dsha (pkeyUnc.GetEncoded())
        let chain2 = 
            Array.map2 (fun a b -> a ^^^ b)
                chain chainMod
        let exp = createBigInt chain2
        point.Multiply exp

    member x.Derive pk = derive pk

(*** hide ***)
let electrumHashes (mpk: byte[]) (cReceive: int) (cChange: int) = 
    let electrumReceive = new Electrum(mpk, 0)
    let electrumChange = new Electrum(mpk, 1)
    let derive (electrumWallet: Electrum) (c: int) = 
        seq {
            for i in 0..c-1 do
            let pubKey = electrumWallet.Derive(i).GetEncoded() 
            yield pubKey |> hash160
        }
    [derive electrumReceive cReceive; derive electrumChange cChange] |> Seq.concat

let armoryHashes (mpk: byte[]) (c: int) = 
    let armory = new Armory(mpk.[33..])
    let addresses = 
        Protocol.iterate (fun (pk: byte[]) ->
            (armory.Derive pk).GetEncoded()
        ) mpk.[0..32] |> Seq.map hash160

    addresses |> Seq.skip 1 |> Seq.take c

let bip32Hashes (mpk: byte[]) (chain: byte[]) (isReceived: bool) (c: int) = 
    let publicKeyExt = (new BIP32PublicExt(ecDomain.Curve.DecodePoint(mpk), chain)).ToPublicChild(if isReceived then 0 else 1)

    seq { 
        for i in 0..c-1 do
            yield publicKeyExt.ToPublicChild(i).ToPublic().GetEncoded() |> hash160
        }

