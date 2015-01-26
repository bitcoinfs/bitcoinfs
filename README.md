# bitcoinfs

An alternative full node bitcoin implementation in F#. The [source code][2] is on GitHub and this documentation
was generated directly from the code.

## Introduction
This project is under development and currently in alpha stage. Generally speaking, writing
a fully compliant bitcoin node is extremely hard - some think impossible. The Bitcoin project
is experimental and never aimed to deliver a 100% accurate specification. The Satoshi client
is the de-facto standard. By far the most used client on the network, it dictates what should
be accepted and what should be rejected. Even the slightest deviation can cause a fork and potential
loss of funds. It should go without saying

> Do not use this code in production when real funds are at stake. 

A lot of effort has been put into aligning its behavior with the core client but nevertheless there
are almost certainly bugs that could be exploited to cause it to deviate from the reference
implementation.

That being said this code has been through the "official" [block acceptance test][1] and has run
for an extended period of time. It implements all the consensus rules including the bugs that 
are now included in the blockchain since the genesis of Bitcoin.

> However, Bitcoin F# has fully validated the existing mainnet blockchain and passes all the integration
tests including large reorg tests. It is also the only implementation in a functional language and comes
under 2.5 kLOC, making it the smallest client too.

In writing this code, my goal was 

- to make a client that is compatible with the rest of the network to the extend of
the supported features
- Simple and readable code. It is not code golf but it is not paid by the line code either.
- Header first, blocks later. The client downloads the block headers first and checks the validity
of the chain then it downloads the blocks from multiple peers in parallel. It dramatically improves
synchronization.
- Easy pruning. Blocks are stored on disk in a normal directory fashion and can be removed by deleting
files. Other implementations use a database or custom data files.
- I didn't want any wallet spending functionality even if I have included support for BIP32, Armory and Electrum style
watch-only wallets. 
- No JSON API either. I will prefer to extend the core.

All in all, it is a small but working client that can be used as a relay for transactions since it
validates inputs and as the base of an online wallet. However, at this point the only wallet
features are watch-only for BIP-32, Electrum and Armory wallets.

Further documentation can be obtained at the [project github pages][3]

License
GPL v3

[1]: https://github.com/TheBlueMatt/test-scripts
[2]: https://github.com/bitcoinfs/bitcoinfs
[3]: http://bitcoinfs.github.io/bitcoinfs
