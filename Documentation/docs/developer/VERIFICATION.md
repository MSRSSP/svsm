# VERIFICATION

Formal verification is done via [Verus](https://github.com/verus-lang/verus).
To run verification, you need to setup the verification tools in order to run
`cargo verify`.

## Setup

Run the following commands to install verus and cargo-verify.

```
cd svsm
./scripts/vinstall.sh
```

## Build

### Build svsm with verification

```
cd svsm/kernel
cargo verify
```

By default, it will verify all crates (except for vstd), if you want to skip
verifying other crates, use `cargo verify --features verus_no_dep_verify`.


### Pass verus arguments for verification.

For debugging purposes, it may be helpful to pass additional Verus arguments.
You can specify extra arguments using environmental variable
{crate}_{lib/bin}_VERUS_ARGS to a specific crate
{crate} or VERUS_ARGS to all crates.

**Examples**

* Compiles a crate without verifying svsm crate:

    ```
    svsm_lib_VERUS_ARGS="--no-verify" cargo verify
    ```

* Compiles a crate while only verifying address module in svsm crate:

    ```
    svsm_lib_VERUS_ARGS="--verify-module address" cargo verify
    ```



### Build without verification

```
cd svsm/kernel
cargo build
```

## Developing specification and proof

While Verus allows you to write specifications and proofs in Rust, it's
beneficial to use the verus!{} macro for a more concise, mathematical syntax
similar to Dafny, F*, and Coq. To get started, be sure to read the [Verus
Tutorial](https://verus-lang.github.io/verus/guide/overview.html)


### Guidelines

* Minimize annotations inside executable Rust.
* Define specification and proof code in `*.verus.rs` or in a different crates.
  Those codes wrapped in verus!{} macro and need verusfmt to format.

```
cd svsm
cargo vfmt
```
