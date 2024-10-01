VERIFICATION
=======

To run verification, we will need to a few steps to setup the build toolchains.

## NOTE
Verus only supports a specific version of rust compiler (v1.78) and so we need to change the default rust compiler version.

SVSM used v1.80 and so we need v1.78 nightly build.

## Code styles

`*.verus.rs` are codes wrapped in verus!{} macro and need verusfmt to format.

```
cd svsm
cargo vfmt
```

## Build

### Install verus-rustc for build

```
cd svsm
cargo install cargo-run-script 
VERUS_PATH=`realpath ../verus` cargo vdep
VERUS_PATH=`realpath ../verus` cargo vinstall
```

Use `VERUS_PATH=`realpath ../verus` cargo vinstall --force` if you want to reinstall.

### Run with verification

```
cd svsm/kernel
cargo build --features verus
```

`cargo build` will call `rustc` for targets that are not verified and call `verus` for targets that are to be verified.


### Run without verification

```
cd svsm/kernel
cargo build --no-default-features
```