#!/bin/bash

script_path=$(realpath "$0")
SVSM_DIR=$(dirname "$script_path")/..

activate() {
    rustup override set nightly-2023-12-22
    export RUSTC=verus-rustc
    echo "set RUSTC = $RUSTC"
}

deactivate() {
    rustup override unset
    unset RUSTC
    echo "unset RUSTC"
}

case $1 in
    activate)
        activate
        ;;
    deactivate)
        deactivate
        ;;
    *)
        activate
        ;;
esac