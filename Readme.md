# Fheanor

## A toolkit library to build Homomorphic Encryption

Building on [feanor-math](https://crates.io/crates/feanor-math), this library provides efficient implementations of various building blocks for Homomorphic Encryption (HE).
The focus is on implementations of the ring `R_q = Z[X]/(Phi_m(X), q)` as required for second-generation HE schemes (like BGV, BFV), but also contains many other components and schemes.

The goal of this library is **not** to provide an easy-to-use implementation of homomorphic encryptions for use in applications - there are many good libraries for that already.
Instead, the goal is to provide a toolkit for researchers that simplifies implementing variants of existing HE schemes, as well as new HE schemes.

**Note** Fheanor was previously called "HE-Ring".

## Features

In short, Fheanor contains the following:
 - Multiple efficient implementations of arithmetic in the ring `R_q`, which provide different performance characteristics (supporting arbitrary `m`)
 - An implementation of the isomorphism `R/(p^e) = GR(p, e, d) x ... x GR(p, e, d)` via "hypercube structures" (compare "Bootstrapping for HElib" by Halevi and Shoup, <https://ia.cr/2014/873>)
 - An implementation of "gadget products", i.e. the certain kind of inner product that is used in HE schemes to multiply ciphertexts with lower noise growth
 - Fast "RNS-conversions", i.e. non-algebraic operations like rounding, implemented directly on the values `x mod p_1, ..., x mod p_r` for different primes `p_1, ..., p_r`
 - Implementations of the BFV, BGV and CLPX encryption schemes
 - Bootstrapping for BFV and BGV
 - Tools for arithmetization, including modelling of arithmetic circuits, polynomial-to-circuit conversion via Paterson-Stockmeyer and HElib-style linear transforms

The following features are available partially, and/or WIP:
 - Noise estimation and optional automated modulus-switching for BGV

## Examples

In addition to the API documentation, detailed guides and examples to some parts of Fheanor can be found in [`crate::examples`].

## Notation (comparison with HElib)

We sometimes use notation differently from the way it is used in HElib, and follow instead most modern HE literature.
In particular, we use the following letters:

| Fheanor      | HElib     | Meaning                                                   |
| ------------ | --------- | --------------------------------------------------------- |
| `m` *        | `m`       | Index (sometimes conductor) of the cyclotomic number ring |
| `n` *        | `n`       | Degree of the number ring                                 |
| `digits`     | `c`       | Number of parts to decompose into during gadget products  |
| `log2(q)`    | `bits`    | Size of the ciphertext modulus                            |
| or `log2_q`  |           |                                                           |
| `p`          | `p`       | Prime factor of the plaintext modulus                     |
| `r`          | `r`       | Exponent of the plaintext modulus                         |
| `t`          | none      | Plaintext modulus `p^r`                                   |
| `l[i]`       | `ords[i]` | Length of the `i`-th hypercube dimension                  |
| `n/d` or `l` |           | Total number of slots
| `sk_hwt`     | `skHwt`   | Hamming weight of the secret key (if chosen to be sparse) |
| `Phi_m`      |           | `m`-th cyclotomic polynomial                              |

* `m` was previously called `n` in Fheanor, with `n` being referred to only as `phi(n)`.
For consistency with previous work, this has been renamed.

## SemVer and Backward Compatibility

As indicated by the `0.x.y` SemVer version, Fheanor is still in an alpha phase, and every new release may contain breaking changes.
In fact, most of the version I published recently contained many significant breaking changes.
Hence, it is recommended to fix the used version of Fheanor, using `version = "=0.x.y"` in your `Cargo.toml`, and only upgrade when you are willing to adjust to the new API changes.
This will be different once we reach version `1.0.0` (although I will probably use the [stability](https://docs.rs/stability/latest/stability/) crate to mark unstable APIs, as already done for `feanor-math`).

## Performance

When optimizing for performance, please use the Intel HEXL library (by enabling the feature `use_hexl` and providing a build of HEXL, as described in more detail in the documentation of [`feanor-math-hexl`](https://github.com/FeanorTheElf/feanor-math-hexl)), since the default NTT does not provide SOTA performance (this is being worked on, and improving). Also note that Fheanor is currently single-threaded (as usual, type implementing [`std::marker::Sync`] are thread-safe, which includes basically all types in Fheanor).

Note that while this library is already quite optimized, it may not be fully competitive with other HE libraries that have existed for longer and thus received more optimization effort.
Also, our goal of providing a modular toolkit of building blocks makes some kinds of optimizations more difficult, since components cannot always make as many assumptions on the input as they could if they only support a single HE scheme.

### Profiling

Fheanor is instrumented using the framework defined by the Rust library [`tracing`](https://crates.io/crates/tracing).
Hence, running any Fheanor functions with an active tracing subscriber will generate corresponding tracing events that the subscriber can use for profiling purposes.
There are various crates that implement tracing subscribers with profiling functionality.

For tests within this crate, we use [`tracing-chrome`](https://crates.io/crates/tracing-chrome) which generates Perfetto json trace files (can be displayed by Google Chrome without requiring plugins).
In particular, if you enable ignored tests and run one of the  `measure_time_`-prefixed test in this crate, this will generate a trace file.
Of course, this is only included on test builds, in library builds, the parent application is free to configure `tracing` as desired.

## Disclaimer

This library has been designed for research on homomorphic encryption.
I did not have practical considerations (like side-channel resistance) in mind, and advise against using using it in production.

## How to cite Fheanor

Please use the following bibtex entry to cite Fheanor:
```text
@misc{cryptoeprint:2025/864,
    author = {Hiroki Okada and Rachel Player and Simon Pohmann},
    title = {Fheanor: a new, modular {FHE} library for designing and optimising schemes},
    howpublished = {Cryptology {ePrint} Archive, Paper 2025/864},
    year = {2025},
    url = {https://eprint.iacr.org/2025/864}
}
```

## License

Fheanor is licensed under the [MIT license](https://choosealicense.com/licenses/mit/).