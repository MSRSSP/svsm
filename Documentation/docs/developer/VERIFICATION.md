VERIFICATION
=======

To run verification, we will need to a few steps to setup the build toolchains.


## Build

### Install verification tools

```
cd svsm
./scripts/vinstall.sh
```

### Build svsm with verification

```
cd svsm/kernel
cargo verify
```

You can pass extra verus arguments via {crate}_VERUS_ARGS to a specific crate {crate} or VERUS_ARGS to all crates.

It is helpful to add extra args for debugging, for example,

`svsm_VERUS_ARGS="--no-verify" cargo verify` compiles the code with verification annotation without verifying it.

`svsm_VERUS_ARGS="--verify-module address" cargo verify` verify only a module in the crate svsm. NOTE: you may have verified the module but cannot build the crate.


### Run without verification

```
cd svsm/kernel
cargo build
```

## Manage specification and proof codes

* Minimize annotations inside executable Rust.
* Define specification and proof code in `*.verus.rs` or in a different crates. Those codes wrapped in verus!{} macro and need verusfmt to format.

```
cd svsm
cargo vfmt
```
