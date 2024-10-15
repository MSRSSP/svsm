#!/bin/bash
cargo install --git https://github.com/microsoft/verismo/ --rev 1114995 cargo-v
builtin=`cargo metadata --format-version 1 | jq -r '.packages[] | select(.name == "builtin_macros") | .targets[].src_path'`
verus=`dirname $builtin`/../../../source/target-verus/release/verus
if [ -f ${verus} ]; then
    echo "verus (${verus}) is already built"
else
    cargo v prepare-verus 
fi
cargo install --git https://github.com/microsoft/verismo/ --rev 1114995 verus-rustc
curl --proto '=https' --tlsv1.2 -LsSf https://github.com/verus-lang/verusfmt/releases/download/v0.4.3/verusfmt-installer.sh | sh
