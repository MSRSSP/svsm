// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

fn main() {
    // Extra cfgs
    //println!("cargo::rustc-check-cfg=cfg(fuzzing)");
    //println!("cargo::rustc-check-cfg=cfg(test_in_svsm)");

    // Stage 2
    println!("cargo:rustc-link-arg-bin=stage2=-nostdlib");
    println!("cargo:rustc-link-arg-bin=stage2=--build-id=none");
    println!("cargo:rustc-link-arg-bin=stage2=-Tkernel/src/stage2.lds");
    println!("cargo:rustc-link-arg-bin=stage2=-no-pie");

    // SVSM 2
    println!("cargo:rustc-link-arg-bin=svsm=-nostdlib");
    println!("cargo:rustc-link-arg-bin=svsm=--build-id=none");
    println!("cargo:rustc-link-arg-bin=svsm=--no-relax");
    println!("cargo:rustc-link-arg-bin=svsm=-Tkernel/src/svsm.lds");
    println!("cargo:rustc-link-arg-bin=svsm=-no-pie");
    if std::env::var("CARGO_FEATURE_MSTPM").is_ok() && std::env::var("CARGO_CFG_TEST").is_err() {
        println!("cargo:rustc-link-arg-bin=svsm=-Llibmstpm");
        println!("cargo:rustc-link-arg-bin=svsm=-lmstpm");
    }

    // Extra linker args for tests.
    println!("cargo:rerun-if-env-changed=LINK_TEST");
    if std::env::var("LINK_TEST").is_ok() {
        println!("cargo:rustc-cfg=test_in_svsm");
        println!("cargo:rustc-link-arg=-nostdlib");
        println!("cargo:rustc-link-arg=--build-id=none");
        println!("cargo:rustc-link-arg=--no-relax");
        println!("cargo:rustc-link-arg=-Tkernel/src/svsm.lds");
        println!("cargo:rustc-link-arg=-no-pie");
    }

    println!("cargo:rerun-if-changed=kernel/src/stage2.lds");
    println!("cargo:rerun-if-changed=kernel/src/svsm.lds");
    println!("cargo:rerun-if-changed=build.rs");
    if cfg!(feature = "verus") {
        init_verify(&["vmath", "vstd"]);
    }
}

fn init_verify(verus_libs: &[&str]) {
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
