# Copyright 2025 The EqMap Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import argparse
import sys
import os
import json

# cargo llvm-cov --all-features --workspace --json
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "-p",
        "--percent",
        dest="percent",
        required=False,
        help="Minimum code coverage per line per source file",
        type=float,
        default=80.0,
    )
    parser.add_argument(
        "-w",
        "--whitelist",
        dest="whitelist",
        nargs="+",
        help="Files to whitelist",
        type=str,
        default=["main.rs"],
    )
    parser.add_argument(
        "input", nargs="?", type=argparse.FileType("r"), default=sys.stdin
    )
    parser.add_argument(
        "output", nargs="?", type=argparse.FileType("w"), default=sys.stdout
    )
    args = parser.parse_args()

    whitelisted = set(args.whitelist)
    data = json.load(args.input)
    data = data["data"]
    percent = args.percent
    passed = True

    print(f"### Code Coverage Summary ({percent:.2f}%)", file=args.output)

    for datum in data:
        files = datum["files"]
        for record in files:
            filePassed = True
            name = record["filename"]
            stem = os.path.basename(name)
            if stem in whitelisted:
                continue
            lineCoverage = record["summary"]["lines"]["percent"]
            if lineCoverage < percent:
                print(
                    f"#### {name}: Only {lineCoverage:.2f}% by line", file=args.output
                )
                print(f"```rust", file=args.output)
                passed = False
                with open(name, "r") as f:
                    lines = f.readlines()
                    printed = set()
                    for segment in record["segments"]:
                        line = segment[0] - 1
                        executed = segment[2] != 0
                        if not executed:
                            txt = lines[line - 1].strip("\n")
                            content = txt.strip()
                            if (
                                line not in printed
                                and len(content) > 3
                                and not content.startswith("//")
                                and not content.startswith("}")
                                and not content.startswith("#")
                            ):
                                print(
                                    f"{txt} // {stem}:{line}",
                                    file=args.output,
                                )
                                printed.add(line)
                print(f"```", file=args.output)

    if passed:
        print("All files passed", file=args.output)
    sys.exit(0 if passed else 1)
