#!/bin/bash
set -exo pipefail

cargo test
cargo run --release examples.txt -k 4 | FileCheck examples.txt 
# Run again but with proofs
cargo run --release examples.txt -k 4 -v | FileCheck examples.txt
echo "SUCCESS"