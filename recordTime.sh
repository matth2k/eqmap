#!/bin/bash
set -exo pipefail

# Collect timing information
echo "Timing information" > time.txt
echo "==================" >> time.txt
echo "debug, no proof" >> time.txt
/bin/time -p --append -o time.txt cargo run hard_examples.txt -k 4 -t 60 -s 15000 --verbose 2>>/dev/null
echo "==================" >> time.txt
echo "debug, proof" >> time.txt
/bin/time -p --append -o time.txt cargo run hard_examples.txt -k 4 -t 60 -s 15000 2>>/dev/null
echo "==================" >> time.txt
echo "release, no proof" >> time.txt
/bin/time -p --append -o time.txt cargo run --release hard_examples.txt -k 4 -t 60 -s 15000 2>>/dev/null
echo "release, proof" >> time.txt
/bin/time -p --append -o time.txt cargo run --release hard_examples.txt -k 4 -t 60 -s 15000 --verbose 2>>/dev/null
echo "==================" >> time.txt
cat time.txt
echo "SUCCESS"