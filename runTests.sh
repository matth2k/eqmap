#!/bin/bash
set -exo pipefail

cargo test
cargo run --release examples.txt -k 4 | FileCheck examples.txt 
echo "SUCCESS"