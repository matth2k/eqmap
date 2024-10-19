use egg::*;
use lut_synth::{
    analysis::{LutAnalysis, PermuteInput},
    lut,
};

#[allow(dead_code)]
fn make_rules() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules: Vec<Rewrite<lut::LutLang, LutAnalysis>> = Vec::new();
    // Logic element conversions
    rules.push(rewrite!("nor2-conversion"; "(NOR ?a ?b)" => "(LUT 1 ?a ?b)"));

    // s? a : b
    rules.push(rewrite!("mux2-1-conversion"; "(MUX ?s ?a ?b)" => "(LUT 202 ?s ?a ?b)"));

    // Evaluate constant programs
    rules.push(rewrite!("lut2-const"; "(LUT 0 ?a ?b)" => "false"));
    rules.push(rewrite!("lut3-const"; "(LUT 0 ?a ?b ?c)" => "false"));
    rules.push(rewrite!("lut4-const"; "(LUT 0 ?a ?b ?c ?d)" => "false"));
    rules.push(rewrite!("lut5-const"; "(LUT 0 ?a ?b ?c ?d ?e)" => "false"));
    rules.push(rewrite!("lut6-const"; "(LUT 0 ?a ?b ?c ?d ?e ?d)" => "false"));

    // Evaluate constant inputs (impl as modify-analysis for multi-input cases)
    rules.push(rewrite!("lut1-const-f"; "(LUT 0 ?a)" => "false"));
    rules.push(rewrite!("lut1-const-t"; "(LUT 3 ?a)" => "true"));
    rules.push(rewrite!("lut1-const-id"; "(LUT 2 ?a)" => "?a"));
    rules.push(rewrite!("lut1-const-i"; "(LUT 1 false)" => "true"));
    rules.push(rewrite!("lut1-const-i"; "(LUT 1 true)" => "false"));

    // DSD an input 6-LUT into two 4-LUTs
    // DSD with one shared variable: an k-LUT (k even) into two (N/2 + 1)-LUTS

    // LUT permutation groups
    rules.push(rewrite!("lut2-permute"; "(LUT ?p ?a ?b)" 
        => {PermuteInput::new(1, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap()])}));

    for i in 1..3 {
        let rname = format!("lut3-permute-{}", i);
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap()])}));
    }

    for i in 1..4 {
        let rname = format!("lut4-permute-{}", i);
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c ?d)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap(), "?d".parse().unwrap()])}));
    }

    for i in 1..5 {
        let rname = format!("lut5-permute-{}", i);
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c ?d ?e)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap(), "?d".parse().unwrap(), "?e".parse().unwrap()])}));
    }

    for i in 1..6 {
        let rname = format!("lut6-permute-{}", i);
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c ?d ?e ?f)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap(), "?d".parse().unwrap(), "?e".parse().unwrap(), "?f".parse().unwrap()])}));
    }
    // LUT fuse mutually exclusive inputs

    // 2-(2,2) => 4-LUT
    // 2-(2,3) => 5-LUT
    // 2-(3,3) => 6-LUT
    // 3-(2,2,2) => 6-LUT

    // LUT fuse non-mutually exclusive inputs (hard, opposite of DSD)
    rules
}

/// parse an expression, simplify it using egg, and pretty print it back out
fn simplify(s: &str) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<lut::LutLang> = s.parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let runner = Runner::default().with_expr(&expr).run(&make_rules());

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];
    println!("{:?}", runner.egraph);

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    println!("Simplified {} to {} with cost {}", expr, best, best_cost);
    best.to_string()
}

#[test]
fn simple_tests() {
    assert_eq!(simplify("(LUT 2 a b)"), "(LUT 2 a b)");
    assert_eq!(simplify("(LUT 3 a b c)"), "(LUT 3 a b c)");

    assert_eq!(simplify("(LUT 0 a)"), "false");
    assert_eq!(simplify("(LUT 3 b)"), "true");
    assert_eq!(simplify("(LUT 1 true)"), "false");
    assert_eq!(simplify("(LUT 2 true)"), "true");
    assert_eq!(simplify("(LUT 1 false)"), "true");
    assert_eq!(simplify("(LUT 2 false)"), "false");
}
fn main() {
    println!("Hello, world!");
    lut::init();
}
