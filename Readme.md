# he-ring, a toolkit library to build Homomorphic Encryption

Building on [feanor-math](https://crates.io/crates/feanor-math), this library provides efficient implementations of various building blocks for Homomorphic Encryption (HE).
The focus is on implementations of the ring `R_q = Z[X]/(Phi_n(X), q)` as required for second-generation HE schemes (like BGV, BFV), but also contains many other components and schemes.

The goal of this library is **not** to provide an easy-to-use implementation of homomorphic encryptions for use in applications - there are many good libraries for that already.
Instead, the goal is to provide a toolkit for researchers that simplifies implementing variants of existing HE schemes, as well as new HE schemes.

## Features

In short, he-ring contains the following:
 - multiple efficient implementations of arithmetic in the ring `R_q`, which provide different performance characteristics (supporting arbitrary `n`)
 - an implementation of the isomorphism `R/(p^e) = GR(p, e, d) x ... x GR(p, e, d)` via "hypercube structures" (compare "Bootstrapping for HElib" by Halevi and Shoup, <https://ia.cr/2014/873>)
 - an implementation of "gadget products", i.e. the certain kind of inner product that is used in HE schemes to multiply ciphertexts with lower noise growth
 - implementations of the BFV and BGV encryption schemes
 - bootstrapping for BFV and BGV
 - tools for arithmetization, including modelling of arithmetic circuits, polynomial-to-circuit conversion via Paterson-Stockmeyer and HElib-style linear transforms

The following features are available partially, and/or WIP:
 - Noise estimation and optional automated modulus-switching for BGV

## Examples

In addition to the API documentation, detailed guides and examples to some parts of HE-Ring can be found in [`crate::examples`].

## Notation (comparison with HElib)

We sometimes use notation differently from the way it is used in HElib, and follow instead most modern HE literature.
In particular, we use the following letters:

| HE-Ring   | HElib     | Meaning                                                   |
| --------- | --------- | --------------------------------------------------------- |
| `n`       | `m`       | Index (sometimes conductor) of the cyclotomic number ring |
| `digits`  | `c`       | Number of parts to decompose into during gadget products  |
| `log2(q)` | `bits`    | Size of the ciphertext modulus                            |
| `p`       | `p`       | Prime factor of the plaintext modulus                     |
| `r`       | `r`       | Exponent of the plaintext modulus                         |
| `t`       | none      | Plaintext modulus `p^r`                                   |
| `m[i]`    | `ords[i]` | Length of the `i`-th hypercube dimension                  |

## Performance

When optimizing for performance, please use the Intel HEXL library (by enabling the feature `use_hexl` and providing a build of HEXL, as described in more detail in the documentation of [`feanor-math-hexl`](https://github.com/FeanorTheElf/feanor-math-hexl)), since the default NTT does not provide SOTA performance. Also note that `he-ring` is currently single-threaded.

Note that while this library is already quite optimized, it may not be fully competitive with other HE libraries that have existed for longer and thus received more optimization effort.
Also, our goal of providing a modular toolkit of building blocks makes some kinds of optimizations more difficult, since components cannot always make as many assumptions on the input as they could if they only support a single HE scheme.

### Profiling

`he-ring` is instrumented using the framework defined by the Rust library [`tracing`](https://crates.io/crates/tracing).
Hence, running any `he-ring` functions with an active tracing subscriber will generate corresponding tracing events that the subscriber can use for profiling purposes.
There are various crates that implement tracing subscribers with profiling functionality.

For tests within this crate, we use [`tracing-chrome`](https://crates.io/crates/tracing-chrome) which generates Perfetto json trace files (can be displayed by Google Chrome without requiring plugins).
In particular, if you enable ignored tests and run one of the  `measure_time_`-prefixed test in this crate, this will generate a trace file.
Of course, this is only included on test builds, in library builds, the parent application is free to configure `tracing` as desired.

## Disclaimer

This library has been designed for research on homomorphic encryption.
I did not have practical considerations (like side-channel resistance) in mind, and advise against using using it in production.

## How to cite HE-Ring

Please use the following bibtex entry to cite HE-Ring:
```text
@misc{hering,
    title = {{HE-Ring}: A homomorphic encryption library},
    url = {https://github.com/FeanorTheElf/he-ring},
    author = {Hiroki Okada and Rachel Player and Simon Pohmann},
    year = {2025}
}
```

## License

`he-ring` is licensed under the [MIT license](https://choosealicense.com/licenses/mit/).