// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

fn main() {
    assert!(cfg!(feature = "verus"));
    init_verify(&["vstd"]);
}

fn init_verify(verus_libs: &[&str]) {
    println!("cargo:rerun-if-changed=build.rs");
    println!("rerun-if-env-changed=VERUS");
    println!("rerun-if-env-changed=VERUS_TARGETS");
    println!("rerun-if-env-changed=HOME");
    if cfg!(feature = "noverify") {
        println!("cargo:rustc-env=VERUS_ARGS=--no-verify");
    } else {
        let verus_args = [
            "--rlimit=8000",
            "--expand-errors",
            "--multiple-errors=5",
            "--triggers-silent",
            "--no-auto-recommends-check",
            "--trace",
            "-Z unstable-options",
        ];
        println!("cargo:rustc-env=VERUS_ARGS={}", verus_args.join(" "));
    }

    let target = std::env::var("CARGO_PKG_NAME").unwrap_or_default();
    let mut targets: Vec<&str> = vec![&target];
    targets.extend(verus_libs);
    println!("cargo:rustc-env=VERUS_TARGETS={}", targets.join(","));
    for (key, value) in std::env::vars() {
        // You can filter or modify which ones to pass to rustc
        println!("cargo:rustc-env={}={}", key, value);
    }

    let module_path = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    println!("cargo:rustc-env=MODULE_PATH={}", module_path);
}
