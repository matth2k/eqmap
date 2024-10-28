![](https://github.com/matth2k/lut-synth/actions/workflows/rust.yml/badge.svg)

# lut-synth: LUT Network Synthesis with E-Graphs

## Description
An early experiment on representing LUT networks within E-Graphs for logic synthesis

### Dependencies
* Rust/cargo
  * egg
  * bitvec

### Installing
`cargo build`

`cargo run < examples.txt // Run the synthesizer on a few examples`

### Docs

`<LutLang> ::= <Program> | <Node>`

`<Node> ::= <Const> | x | <Input> | NOR <Node> <Node> | MUX <Node> <Node> <Node> | LUT <Program> Node ... Node`

`<Const> ::= false | true // Base type is a bool`

`<Input> ::= <String> // Any string is parsed as an input variable`

`<Program> ::= <u64> // Can store a program for up to 6 bits`