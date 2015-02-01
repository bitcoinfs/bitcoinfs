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

(*** hide ***)
module Db

open System
open System.IO
open System.Collections
open System.Collections.Generic
open System.Linq
open System.Net
open System.Net.Sockets
open Murmur
open Protocol
open Org.BouncyCastle.Utilities.Encoders
open FSharpx
open FSharpx.Collections
open FSharpx.Choice
open NodaTime
open System.Data
open System.Data.SQLite
open LevelDB

(**
# Database

The database module handles the persistance of the blockchain, unspent transaction outputs and peer
addresses. 

- The largest amount of data is in the blocks of the blockchain. It represents nearly 30 GB at this time
(2015) and will continue growing. They are written as binary files so that they can be conveniently trimmed.
- The unspent transaction outputs are the stashes of bitcoins that haven't been used by a transaction yet. They
are the application main data. Once blocks are analyzed, the application doesn't need them anymore except during a
reorganization of the blockchain. Instead, the application refers to the UTXO which is a much smaller set of data (~1GB).
The UTXO are kept in a LevelDB database for better performance.
- Finally, the metadata is in a SQLite database. The relational database allows advanced querying that LevelDB doesn't
provide and the amount of data isn't an issue here.

## Backup
To make a backup, the easiest way is to shutdown the application and copy the content of the `utxo` folder which has the
UTXO database and the `bitcoin.db` file that has the associated metadata. The blocks can be saved too but they are not 
vital.
*)
let connectionString = sprintf "Data Source=%s/bitcoin.db" baseDir
let dbLock = new obj() // Serialize all db access because of SQLite

(**
DB Connections can't be shared between threads but they are coming from a pool and are cheap to establish. Using ADO.NET, 
I can write parametrized SQL statements. It's direct SQL and therefore not portable to other DB providers but it works
well here. The database model isn't sophisticated enough to warrant an entity-relation library. I prefer to keep the 
database layer a straight get and put interface.
*)

let updateAddr(addr: AddrEntry) = 
    lock dbLock (fun () ->
        use connection = new SQLiteConnection(connectionString)
        connection.Open()
        let updateAddrQuery = new SQLiteCommand(@"insert or ignore into peerInfo(host, port, ts, user_agent, state, score) values(@host, @port, @ts, @user_agent, 0, 0);
            update peerInfo set ts = @ts where host = @host and port = @port", connection)
        updateAddrQuery.Parameters.Add("@host", DbType.String, 256) |> ignore
        updateAddrQuery.Parameters.Add("@port", DbType.Int32) |> ignore
        updateAddrQuery.Parameters.Add("@ts", DbType.DateTime) |> ignore
        updateAddrQuery.Parameters.Add("@user_agent", DbType.String, 256) |> ignore
        updateAddrQuery.Parameters.[0].Value <- addr.Address.EndPoint.Address.ToString()
        updateAddrQuery.Parameters.[1].Value <- addr.Address.EndPoint.Port
        let dts = (new Instant(int64(addr.Timestamp) * NodaConstants.TicksPerSecond)).ToDateTimeUtc()
        updateAddrQuery.Parameters.[2].Value <- dts
        updateAddrQuery.Parameters.[3].Value <- ""
        updateAddrQuery.ExecuteNonQuery() |> ignore
    )
(**
## Peers

The peerInfo table has the addresses of the peers that were advertised either through seed discovery or through
peer to peer `addr` messages. I don't do much peer management. Typically, the quality of the information degrades over
time since peers disconnect and reconnect freely. Therefore, I keep updating the table and the query that returns peers
sorts them from the most recent to the least.

Peers have a state telling whether they are in use but they should also have a badness score. It's not done at the moment.
The application will disconnect from badly behaved peers but without a score value and a ban period, nothing prevents
a peer from reconnecting immediately. This is on the TODO list.
*)
let getPeers() =
    lock dbLock (fun () ->
        use connection = new SQLiteConnection(connectionString)
        connection.Open()
        use command = new SQLiteCommand("select host, port from peerInfo where state = 0 order by ts desc limit 1000", connection)
        use reader = command.ExecuteReader()
        [while reader.Read() do 
            let host = reader.GetString(0)
            let port = reader.GetInt32(1)
            let ip = IPAddress.Parse(host)
            let endpoint = new IPEndPoint(ip, port)
            yield endpoint
        ]
    )

let getPeer() =
    lock dbLock (fun () ->
        use connection = new SQLiteConnection(connectionString)
        connection.Open()
        use command = new SQLiteCommand("select host, port from peerInfo where state = 0 order by ts desc limit 1", connection)
        use reader = command.ExecuteReader()
        let peers = 
            [while reader.Read() do 
                let host = reader.GetString(0)
                let port = reader.GetInt32(1)
                let ip = IPAddress.Parse(host)
                let endpoint = new IPEndPoint(ip, port)
                yield endpoint
            ]
        peers |> Seq.tryPick Some
    )
(*
Drop peers that are older than a certain timestamp. Normally, 3h ago.
*)
let dropOldPeers dts = 
    use connection = new SQLiteConnection(connectionString)
    connection.Open()
    use command = new SQLiteCommand("delete from peerInfo where ts <= @ts", connection)
    command.Parameters.Add("@ts", DbType.DateTime) |> ignore
    command.Parameters.[0].Value <- dts
    command.ExecuteNonQuery() |> ignore

(*
At startup, mark all the peers as disconnected
*)
let resetState() =
    use connection = new SQLiteConnection(connectionString)
    connection.Open()
    use command = new SQLiteCommand("update peerInfo set state = 0 where state > 0", connection)
    command.ExecuteNonQuery() |> ignore

let updateState(peer: IPEndPoint, state: int) =
    lock dbLock (fun () ->
        use connection = new SQLiteConnection(connectionString)
        connection.Open()
        let query = new SQLiteCommand("update peerInfo set state = ? where host = ? and port = ?", connection)
        query.Parameters.Add("state", DbType.Int32) |> ignore
        query.Parameters.Add("host", DbType.String, 256) |> ignore
        query.Parameters.Add("port", DbType.Int32) |> ignore
        query.Parameters.[0].Value <- state
        query.Parameters.[1].Value <- peer.Address.ToString()
        query.Parameters.[2].Value <- peer.Port
        query.ExecuteNonQuery() |> ignore
    )
(**
## Headers

I keep all the information that I parse from a header. The tx-count is not populated in the `Headers` message
and will be zero. The column is there for later. The hash isn't part of the header but is in fact the actual hash of the
header itself. It is calculated during parsing and then stored. Finally, the height is also determined by looking up the previous header.
If the previous header is not present in the database, then the header is skipped and not stored at all. When the missing
header comes and the block connects, I'll get the header again.
*)    
let headerConnection = new SQLiteConnection(connectionString)
headerConnection.Open()
let command = new SQLiteCommand(@"insert or replace into header(hash, height, version, prev_hash, next_hash, merkle_root, ts, bits, nonce, tx_count, is_main, state) values(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)", headerConnection)
command.Parameters.Add("hash", DbType.Binary, 32) |> ignore
command.Parameters.Add("height", DbType.Int32) |> ignore
command.Parameters.Add("version", DbType.Int32) |> ignore
command.Parameters.Add("prev_hash", DbType.Binary, 32) |> ignore
command.Parameters.Add("next_hash", DbType.Binary, 32) |> ignore
command.Parameters.Add("merkle_root", DbType.Binary, 32) |> ignore
command.Parameters.Add("ts", DbType.Int32) |> ignore
command.Parameters.Add("bits", DbType.Int32) |> ignore
command.Parameters.Add("nonce", DbType.Int32) |> ignore
command.Parameters.Add("tx_count", DbType.Int32) |> ignore
command.Parameters.Add("state", DbType.Int32) |> ignore
command.Parameters.Add("is_main", DbType.Boolean) |> ignore

let readTip(): byte[] =
    lock dbLock (fun () ->
        use command = new SQLiteCommand("select best from chainstate where id = 0", headerConnection)
        use reader = command.ExecuteReader()
        [while reader.Read() do 
            let tip = Array.zeroCreate 32
            reader.GetBytes(0, 0L, tip, 0, 32) |> ignore
            yield tip
        ] |> List.head
    )

let writeTip(tip: byte[]) = 
    lock dbLock (fun () ->
        use command = new SQLiteCommand("update chainstate set best = ? where id = 0", headerConnection)
        command.Parameters.Add("best", DbType.Binary, 32) |> ignore
        command.Parameters.[0].Value <- tip
        command.ExecuteNonQuery() |> ignore
    )

let getHeader (reader: SQLiteDataReader) =
    lock dbLock (fun () ->
        [while reader.Read() do 
            let hash = Array.zeroCreate 32
            reader.GetBytes(0, 0L, hash, 0, 32) |> ignore
            let height = reader.GetInt32(1)
            let version = reader.GetInt32(2)
            let prev_hash = Array.zeroCreate 32
            reader.GetBytes(3, 0L, prev_hash, 0, 32) |> ignore
            let next_hash = Array.zeroCreate 32
            reader.GetBytes(4, 0L, next_hash, 0, 32) |> ignore
            let merkle_root = Array.zeroCreate 32
            reader.GetBytes(5, 0L, merkle_root, 0, 32) |> ignore
            let ts = reader.GetInt32(6)
            let bits = reader.GetInt32(7)
            let nonce = reader.GetInt32(8)
            let tx_count = reader.GetInt32(9)
            let is_main = reader.GetBoolean(10)
            let bh = new BlockHeader(hash, version, prev_hash, merkle_root, uint32 ts, bits, nonce, tx_count)
            bh.Height <- height
            bh.NextHash <- next_hash
            bh.IsMain <- is_main
            yield bh
        ]
    )

let genesisHeader = 
    lock dbLock (fun () ->
        use command = new SQLiteCommand("select hash, height, version, prev_hash, next_hash, merkle_root, ts, bits, nonce, tx_count, is_main from header where height = 0", headerConnection)
        use reader = command.ExecuteReader()
        let res = getHeader reader
        res.Head
        )

let readHeader(hash: byte[]): BlockHeader = 
    lock dbLock (fun () ->
        use command = new SQLiteCommand("select hash, height, version, prev_hash, next_hash, merkle_root, ts, bits, nonce, tx_count, is_main from header where hash = ?", headerConnection)
        command.Parameters.Add("hash", DbType.Binary, 32) |> ignore
        command.Parameters.[0].Value <- hash
        use reader = command.ExecuteReader()
        let res = getHeader reader
        if res.Length <> 0 then res.[0] else BlockHeader.Zero
    )

let getHeaderByHeight (height: int): BlockHeader =
    lock dbLock (fun () ->
        use command = new SQLiteCommand("select hash, height, version, prev_hash, next_hash, merkle_root, ts, bits, nonce, tx_count, is_main from header where height = ? and is_main = 1", headerConnection)
        command.Parameters.Add("height", DbType.Int32) |> ignore
        command.Parameters.[0].Value <- height
        use reader = command.ExecuteReader()
        let res = getHeader reader
        if res.Length <> 0 then res.[0] else BlockHeader.Zero
    )

let getNextHeader(hash: byte[]): BlockHeader = 
    lock dbLock (fun () ->
        use command = new SQLiteCommand("select hash, height, version, prev_hash, next_hash, merkle_root, ts, bits, nonce, tx_count, is_main from header where prev_hash = ?", headerConnection)
        command.Parameters.Add("prev_hash", DbType.Binary, 32) |> ignore
        command.Parameters.[0].Value <- hash
        use reader = command.ExecuteReader()
        let res = getHeader reader
        if res.Length <> 0 then res.[0] else BlockHeader.Zero
    )

let writeHeaders(header: BlockHeader) = 
    lock dbLock (fun () ->
        command.Parameters.[0].Value <- header.Hash
        command.Parameters.[1].Value <- header.Height
        command.Parameters.[2].Value <- header.Version
        command.Parameters.[3].Value <- header.PrevHash
        command.Parameters.[4].Value <- header.NextHash
        command.Parameters.[5].Value <- header.MerkleRoot
        command.Parameters.[6].Value <- header.Timestamp
        command.Parameters.[7].Value <- header.Bits
        command.Parameters.[8].Value <- header.Nonce
        command.Parameters.[9].Value <- header.TxCount
        command.Parameters.[10].Value <- header.IsMain
        command.Parameters.[11].Value <- 0

        command.ExecuteNonQuery() |> ignore
    )

(**
## Bloom Filter
A [Bloom Filter][1] is a probabilistic filter that has a configurable probability of false positive and no
false negative. Public keys that match the addresses that I own are inserted into the Bloom Filter and checked
when I process transactions. It allows me to quickly reject transactions that do not belong to my wallets.

[1]: https://en.wikipedia.org/wiki/Bloom_filter
*)
type BloomFilter(filter: byte[], cHashes: int, nTweak: int) =
    let bits = new BitArray(filter)
    let hashers = seq {
        for i in 0..cHashes-1 do
            yield MurmurHash.Create32(uint32(i*0xFBA4C795+nTweak)) } |> Seq.toArray

    let add (v: byte[]) =
        for hasher in hashers do
            let hash = hasher.ComputeHash v
            let bucket = BitConverter.ToUInt32(hash, 0) % (uint32 filter.Length*8u)
            bits.Set(int bucket, true)

    let check (v: byte[]) =
        (hashers |> Seq.map (fun hasher ->
            let hash = hasher.ComputeHash v
            let h = BitConverter.ToUInt32(hash, 0)
            let bucket = h % (uint32 filter.Length*8u)
            bits.Get(int bucket)
            )).All(fun b ->  b)

    new(N: int, P: float, cHashes: int, nTweak: int) = 
        let size = int(min (-1.0/log 2.0**2.0*(float N)*log P) 36000.0)
        new BloomFilter(Array.zeroCreate size, cHashes, nTweak)
    member x.Add v = add v
    member x.Check v = check v

type AddressEntry = {
    Id: int
    Account: int
    Hash: byte[]
    Address: string
    }
(**
## Wallet
A wallet is simply a table that has a collection of hashes which match either a p2pkh script or p2sh script.
Technically there is a chance that there is a collision between these two types of scripts but the odds are extremely small
This class loads every key from the table in memory and builds a Bloom filter. Every add/del UTXO is looked up in the walet
and should be done as quickly as possible. Since the chances of having a match is rather small, the Bloom filter reduces the need
to do a detailed search through the keys.
*)
type Wallet() =
    let bloomFilter = new BloomFilter(settings.BloomFilterSize, 0.00001, 10, 4)

    let loadData() =
        lock dbLock (fun () ->
            use command = new SQLiteCommand("select id, account, hash, address from keys", headerConnection)
            use reader = command.ExecuteReader()
            [while reader.Read() do 
                let id = reader.GetInt32(0)
                let account  = reader.GetInt32(1)
                let hash = Array.zeroCreate 20
                reader.GetBytes(2, 0L, hash, 0, 20) |> ignore
                let address = reader.GetString(3)
                yield (hash, { Id = id; Account = account; Hash = hash; Address = address })
            ] |> Map.ofSeq
        )
    let addresses = loadData()
    let get (hash: byte[]) =
        maybe {
            do! Option.conditional (bloomFilter.Check hash) ()
            return! addresses |> Map.tryFind hash
        }
    do
        addresses |> Map.iter (fun k _ -> bloomFilter.Add k)
    member x.TryGet (hash: byte[]) = get hash

let wallet = new Wallet()

(**
## UTXO accessor

The UTXO accessor interface is the abstract interface over the UTXO data store. The primary store is the levelDB database where
the main chain gets synced up to. However during acceptance of a new block(s), the blockchain validator works with a temporary set of UTXO.
Being a low level store, LevelDB doesn't have support for transactions and therefore it has to be done at the application layer. The technique I use is a simple
versioning in-memory table. Regardless of whether it is talking directly to the on-disk db or through an overlay, the application
code uses the same interface.
*)
type IUTXOAccessor =
    inherit IDisposable
    abstract DeleteUTXO: OutPoint -> unit
    abstract AddUTXO: OutPoint * UTXO -> unit
    abstract GetUTXO: OutPoint -> Option<UTXO> // Try to get a given Outpoint
    abstract GetCount: byte[] -> int // Counts how many UTXO exists for a given transaction hash

type TxTableAccessor() =
    let connection = new SQLiteConnection(connectionString)
    let insertTx = new SQLiteCommand("insert or ignore into tx(hash, vout, key_hash, amount) values (?, ?, ?, ?)", connection)
    let deleteTx = new SQLiteCommand("delete from tx where hash=? and vout=?", connection)

    let addToTxTable (outpoint: OutPoint) (utxo: UTXO) =
        let script = utxo.TxOut.Script
        lock dbLock (fun () ->
            maybe {
                let! hash = Script.scriptToHash(script)
                let! addressEntry = wallet.TryGet(hash)
                insertTx.Parameters.[0].Value <- outpoint.Hash
                insertTx.Parameters.[1].Value <- outpoint.Index
                insertTx.Parameters.[2].Value <- hash
                insertTx.Parameters.[3].Value <- utxo.TxOut.Value
                insertTx.ExecuteNonQuery() |> ignore
                logger.InfoF "%s %d" addressEntry.Address utxo.TxOut.Value
            } |> ignore
            )

    let deleteFromTxTable (outpoint: OutPoint) =
        lock dbLock (fun () ->
            deleteTx.Parameters.[0].Value <- outpoint.Hash
            deleteTx.Parameters.[1].Value <- outpoint.Index
            deleteTx.ExecuteNonQuery() |> ignore
            )

    do
        connection.Open()
        insertTx.Parameters.Add("hash", DbType.Binary) |> ignore
        insertTx.Parameters.Add("vout", DbType.Int32) |> ignore
        insertTx.Parameters.Add("key_hash", DbType.Binary) |> ignore
        insertTx.Parameters.Add("amount", DbType.Int64) |> ignore
        deleteTx.Parameters.Add("hash", DbType.Binary) |> ignore
        deleteTx.Parameters.Add("vout", DbType.Int32) |> ignore

    interface IDisposable with
        override x.Dispose() = 
            insertTx.Dispose()
            deleteTx.Dispose()
            connection.Dispose()

    member x.Add (outpoint: OutPoint) (utxo: UTXO) = addToTxTable outpoint utxo
    member x.Delete (outpoint: OutPoint) = deleteFromTxTable outpoint

let txTableAccessor = new TxTableAccessor()

(**
This wallet does not store the history of transactions but just the result (unspent outputs). So when a transaction
spents an outpoint, it is deleted from the `tx` table. Another option would be to keep on adding records. I may change
the implementation later. It slightly makes undoing a transaction more complicated. One must differenciate between
undoing a transaction vs spending an output. 
*)
let addIfInWallet (txTableAccessor: TxTableAccessor) (wallet: Wallet) (outpoint: OutPoint) (utxo: UTXO) =
    let script = utxo.TxOut.Script
    maybe {
        let! hash = Script.scriptToHash(script)
        let! addressEntry = wallet.TryGet(hash)
        txTableAccessor.Add outpoint utxo
    } |> ignore

let removeIfInWallet (txTableAccessor: TxTableAccessor) (wallet: Wallet) (outpoint: OutPoint) (utxo: UTXO) =
    let script = utxo.TxOut.Script
    maybe {
        let! hash = Script.scriptToHash(script)
        let! addressEntry = wallet.TryGet(hash)
        txTableAccessor.Delete outpoint
    } |> ignore

(**
The LevelDB accessor converts keys & values into binary strings and uses the LevelDB-Sharp bridge
to read or write to the database.
*)
type LevelDBUTXOAccessor(db: DB, wallet: Wallet, txTableAccessor: TxTableAccessor) =
    let ro = new ReadOptions()
    let wo = new WriteOptions()

    let deleteUTXO (outpoint: OutPoint) = 
        let k = outpoint.ToByteArray()
        maybe {
            let! v = Option.ofNull (db.Get(ro, k))
            let utxo = ParseByteArray v UTXO.Parse
            removeIfInWallet txTableAccessor wallet outpoint utxo
        } |> ignore
        db.Delete(wo, k)
    let addUTXO (outpoint: OutPoint) (utxo: UTXO) = 
        let k = outpoint.ToByteArray()
        let v = utxo.ToByteArray()
        addIfInWallet txTableAccessor wallet outpoint utxo
        db.Put(wo, k, v)
    let getUTXO (outpoint: OutPoint) =
        let k = outpoint.ToByteArray()
        let v = db.Get(ro, k)
        if v <> null 
        then Some(ParseByteArray v UTXO.Parse)
        else 
            None

    // Use the fact that the txhash is a prefix for the key
    // Seek into the database and iterate as long as the key has a prefix equal to the tx hash
    // It eliminates the need to keep an additional counter
    let getCount (txHash: byte[]) =
        let cursor = new Iterator(db, ro)
        cursor.Seek(txHash)
        let mutable count = 0
        let rec getCountInner (count: int): int = 
            if cursor.IsValid then
                let k = cursor.Key
                let hash = k.[0..txHash.Length-1] // first part of the key is the txhash
                if hash = txHash 
                then 
                    cursor.Next()
                    getCountInner (count+1)
                else count
            else count

        let count = getCountInner(0)
        count

    new() = 
        let options = new Options()
        options.CreateIfMissing <- true
        new LevelDBUTXOAccessor(DB.Open(options, sprintf "%s/utxo" baseDir), wallet, txTableAccessor)
        
    interface IUTXOAccessor with
        member x.DeleteUTXO(outpoint) = deleteUTXO outpoint
        member x.AddUTXO(outpoint, txOut) = addUTXO outpoint txOut
        member x.GetUTXO(outpoint) = getUTXO outpoint
        member x.GetCount(txHash) = getCount txHash
        member x.Dispose() = db.Dispose()

    member val Db = db with get

let levelDbAccessor = new LevelDBUTXOAccessor()
let utxoAccessor = levelDbAccessor :> IUTXOAccessor

let scanUTXO () =
    let creditToWallet = addIfInWallet txTableAccessor wallet 
    lock dbLock (fun () ->
        let ro = new ReadOptions()
        use cursor = new Iterator(levelDbAccessor.Db, ro)
        cursor.SeekToFirst()
        while cursor.IsValid do
            let k = cursor.Key
            let v = cursor.Value
            let outpoint = ParseByteArray k OutPoint.Parse
            let utxo = ParseByteArray v UTXO.Parse
            creditToWallet outpoint utxo
            cursor.Next()
        )

(**
Format of the UNDO file. The transactions stored in blocks must be reverted if they end up being
part of an orphaned block. However, a block does not have enough data to undo the effects on the UTXO db.
A transaction deletes the input TXO and creates new UTXO. If it needs to be reverted, it is easy to delete the
newly created UTXO but difficult to recreate the input TXO unless that data is stored as well.

When a block is processed and the UTXO db updated, I create an undo file that logs the changes applied to the db.
It is kept in the same directory location as the block file and can be trimmed at the same time. Obviously deleting
blocks and undo files removes the ability to reorganize the blockchain into a fork that is deeper than least recent block
available.
*)
type TxOperation = 
    | Add 
    | Delete 

type IUTXOWriter =
    abstract Write: TxOperation * OutPoint * UTXO -> unit

(** 
A few helper functions for validity checks. They appear early in the code because of the `processUTXO` function which goes through the
transactions and calls the UTXO accessor. I take advantage of this traversal to do some basic checks.
*)

let checkMoney (v: int64) = (v >= 0L && v < maxMoney) |> errorIfFalse "not in money range" |> Option.map(fun () -> v)
let checkCoinbaseMaturity (utxo: UTXO) (height: int) = (utxo.Height = 0 || height >= utxo.Height + coinbaseMaturity) |> errorIfFalse "coinbase has not matured" |> Option.map(fun () -> utxo)
let OP_RETURN = 106uy
let isRETURN (script: byte[]) = script.Length > 0 && script.[0] = OP_RETURN

(**
This is the first time that I use the `maybe` computational expression. So it's maybe worth spending some time to talk about it.
`maybe` is a builder for the monad `Option` type. Inside the `maybe`
block, `let!` statements evaluate an expression to either `Some` or `None`. If the result is `None`, the rest is not evaluated and the `maybe` block
returns `None`. It's syntaxic sugar for the [monadic][1] `bind`, `map`, etc. Sometimes I need to use these functions explicitly but when the `maybe`
builder does the job, the code is easier to read. Even though it looks like a normal loop over tx inputs and outputs, if any of the checks
fail, evaluation is short circuited and returns `None`. Exceptions could have worked but it is harder to control their propagation and
monads keep the function pure (except at the db level of course).

[1]: http://en.wikipedia.org/wiki/Monad_%28functional_programming%29
*)
let processUTXO (utxoAccessor: IUTXOAccessor) (utxoWriter: IUTXOWriter) (isCoinbase: bool) (height: int) (tx: Tx)  =
    maybe {
        let! totalIn = 
            tx.TxIns |> Seq.map (fun txIn ->
                if not isCoinbase then
                    let utxo = utxoAccessor.GetUTXO txIn.PrevOutPoint
                    utxo |> Option.map (fun utxo ->
                        utxoAccessor.DeleteUTXO txIn.PrevOutPoint
                        utxoWriter.Write(Delete, txIn.PrevOutPoint, utxo)
                        utxo) 
                        |> Option.bind (fun utxo -> checkCoinbaseMaturity utxo height)
                        |> Option.bind (fun utxo -> checkMoney utxo.TxOut.Value)
                else Some 0L
                ) |> Seq.toList |> Option.sequence |> Option.map Seq.sum
        let! totalOut =
            tx.TxOuts |> Seq.mapi (fun iTxOut txOut ->
                let outpoint = new OutPoint(tx.Hash, iTxOut)
                let utxo = UTXO(txOut, if isCoinbase then height else 0)
                if not (isRETURN utxo.TxOut.Script) then
                    utxoAccessor.AddUTXO (outpoint, utxo)
                    utxoWriter.Write(Add, outpoint, utxo)
                if not isCoinbase
                then checkMoney txOut.Value 
                else Some 0L
            ) |> Seq.toList |> Option.sequence |> Option.map Seq.sum
        let! _ = checkMoney totalIn
        let! _ = checkMoney totalOut
        let fee = totalIn - totalOut
        do! fee >= 0L |> errorIfFalse "fee must be positive"
        return fee
    }

(** 
## Block storage

Blocks are stored as flat binary file in the directory under the blocksDir configured in the `app.config`. The path follows a naming
convention that takes the depth and hash into consideration. A block of hash '0bb74cf88a2e07275a36cb57e81ddb64933568f7720e2f91ff84c5ee614fa3e3' and height 1002
will be under blocks/1/1002/0bb74cf88a2e07275a36cb57e81ddb64933568f7720e2f91ff84c5ee614fa3e3. The undo block has the same name and location but with the .undo extension.
Undo blocks are written in the same order as the transactions of the block are written. Therefore when they are reverted, they must be applied in *reverse* order.
*)
let blocksBaseDir = settings.BlocksDir

let getBlockDir (bh: BlockHeader) =
    let height = bh.Height
    let path = sprintf "%s/%d/%d" blocksBaseDir (height/1000) height
    Directory.CreateDirectory path |> ignore
    path

let hasBlock (bh: BlockHeader) =
    let path = getBlockDir bh
    File.Exists (sprintf "%s/%s" path (hashToHex bh.Hash))

let storeBlock (b: Block) (p: byte[]) =
    let path = getBlockDir b.Header
    use fs = new FileStream(sprintf "%s/%s" path (hashToHex b.Header.Hash), FileMode.Create)
    use writer = new BinaryWriter(fs)
    writer.Write(p)

let deleteBlock (bh: BlockHeader) =
    let path = getBlockDir bh
    File.Delete (sprintf "%s/%s" path (hashToHex bh.Hash))

type UndoWriter(fs: FileStream) =
    let writer = new BinaryWriter(fs)

    interface IDisposable with
        override x.Dispose() =
            writer.Close()
            fs.Close()

    interface IUTXOWriter with
        member x.Write(txOp: TxOperation, outpoint: OutPoint, utxo: UTXO) = 
            match txOp with
            | Add -> writer.Write(0uy) // 0 is add
            | Delete -> writer.Write(1uy)
            writer.Write(outpoint.ToByteArray())
            writer.Write(utxo.ToByteArray())
    
let storeUndoBlock (b: Block) = 
    let path = getBlockDir b.Header
    let fs = new FileStream(sprintf "%s/%s.undo" path (hashToHex b.Header.Hash), FileMode.Create)
    new UndoWriter(fs)

let loadBlock (bh: BlockHeader) =
    let path = getBlockDir bh
    use fs = new FileStream(sprintf "%s/%s" path (hashToHex bh.Hash), FileMode.Open)
    use reader = new BinaryReader(fs)
    let block = Block.Parse reader
    block.Header.Height <- bh.Height
    block
let getBlockSize (bh: BlockHeader) =
    let path = getBlockDir bh
    use fs = new FileStream(sprintf "%s/%s" path (hashToHex bh.Hash), FileMode.Open)
    int32 fs.Length

let undoBlock (utxoAccessor: IUTXOAccessor) (bh: BlockHeader) = 
    logger.DebugF "Undoing block #%d" bh.Height
    let path = getBlockDir bh

    use fsUndo = new FileStream(sprintf "%s/%s.undo" path (hashToHex bh.Hash), FileMode.Open)
    use reader = new BinaryReader(fsUndo)
    let fops = new List<unit -> unit>()
    while (fsUndo.Position <> fsUndo.Length) do
        let op = reader.ReadByte()
        let outpoint = OutPoint.Parse reader
        let utxo = UTXO.Parse reader
        let fop = 
            match op with 
            | 0uy -> fun() -> utxoAccessor.DeleteUTXO outpoint // 0 was an add and to undo an add, do a delete
            | 1uy -> fun() -> utxoAccessor.AddUTXO (outpoint, utxo)
            | _ -> ignore

        fops.Add(fop)
    fops |> Seq.toList |> List.rev |> List.iter(fun fop -> fop()) // Don't forget to reverse the list
    let block = loadBlock bh
    block.Txs

