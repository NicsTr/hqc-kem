# HQC-KEM

This is a draft at implementing HQC-KEM (FIPS-207) with the following constraints:

* Is valid against the Known Answer Tests from the latest reference implementation (02/2026)
* Uses pure safe Rust
* Is `no_std` and does __not__ require any dynamic allocator 
* Is a best-effort constant-time implementation (by using crates provided by [https://github.com/RustCrypto/utils]())
* Implements KEMs traits from [https://github.com/RustCrypto/traits]()

⚠️Currently, this crate is not sufficiently tested and does not implement all implementation optimizations ⚠️
