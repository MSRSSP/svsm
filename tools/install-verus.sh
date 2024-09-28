script_path=$(realpath "$0")
SVSM_DIR=$(dirname $script_path)/../../
cd $SVSM_DIR
git clone https://github.com/verus-lang/verus
cat <<EOL > verus/rust-toolchain.toml
[toolchain]
#channel = "1.76.0"
channel = "nightly-2023-12-22" # (not officially supported)
components = [ "rustc", "rust-std", "cargo", "rustfmt", "rustc-dev", "llvm-tools" ]
EOL
cd verus/source
tools/get-z3.sh && source ../tools/activate && vargo build --release