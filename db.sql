create table peerInfo(
    host varchar(256) not null,
    port int not null,
    ts datetime not null,
    user_agent varchar(256) not null,
    state int not null,
    score int not null,
    constraint pk_peerInfo primary key (host, port)
);    

create table chainstate (
    id int not null,
    best binary(32) not null,
    constraint pk_chainstate primary key(id));
    
create table header(
    hash binary(32) not null,
    height int not null,
    version int not null,
    prev_hash binary(32) not null,
    merkle_root binary(32) not null,
    ts int not null,
    bits int not null,
    nonce int not null,
    tx_count int not null,
    state int not null,
    next_hash binary(32) not null,
    is_main bool not null,
    constraint pk_header primary key (hash));
create index i_prev_header on header(prev_hash);

insert into header values(
x'6fe28c0ab6f1b372c1a6a246ae63f74f931e8365e15a089c68d6190000000000', 0, 1,
x'0000000000000000000000000000000000000000000000000000000000000000', 
x'3ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a',
1231006505, 486604799, 2083236893, 1, 0, x'', 0);

insert into chainstate values(0,
x'6fe28c0ab6f1b372c1a6a246ae63f74f931e8365e15a089c68d6190000000000');

select header.* from chainstate, header where chainstate.best = header.hash;

create table account(
     id int not null,
     owner string not null,
     description string,
     constraint pk_account primary key (id));

create table keys(
     id int not null,
     account int not null,
     hash binary(20) not null,
     address string not null,
     constraint pk_keys primary key (id),
     constraint fk_account foreign key (account) references account(id));

create index i_key_address on keys(hash, address);
create unique index i_key_hash on keys(hash);

create table tx(
     hash binary(32) not null,
     vout int not null,
     key_hash binary(20) not null,
     amount int64 not null,
     constraint pk_tx primary key (hash, vout),
     constraint fk_key foreign key (key_hash) references keys(hash));
     
select tx.amount, keys.address from tx, keys where tx.key_hash = keys.hash;
select sum(tx.amount) from tx;
select max(height) from header;
select * from peerInfo order by ts desc;


