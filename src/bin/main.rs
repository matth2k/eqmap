use egg::*;
use lut_synth::{
    analysis::{LutAnalysis, PermuteInput},
    lut,
};

#[allow(dead_code)]
fn make_rules() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    vec![
        rewrite!("nor2-conversion"; "(NOR ?a ?b)" => "(LUT 1 ?a ?b)"),
        // Evaluate constant programs
        rewrite!("lut2-const"; "(LUT 0 ?a ?b)" => "false"),
        rewrite!("lut3-const"; "(LUT 0 ?a ?b ?c)" => "false"),
        rewrite!("lut4-const"; "(LUT 0 ?a ?b ?c ?d)" => "false"),
        rewrite!("lut5-const"; "(LUT 0 ?a ?b ?c ?d ?e)" => "false"),
        rewrite!("lut6-const"; "(LUT 0 ?a ?b ?c ?d ?e ?d)" => "false"),
        // Evaluate constant inputs (impl as modify analysis)

        // DSD an input 6-LUT into two 4-LUTs
        // DSD with one shared variable: an k-LUT (k even) into two (N/2 + 1)-LUTS

        // LUT permutation groups
        rewrite!("lut2-permute"; "(LUT ?p ?a ?b)" => {PermuteInput::new(1, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap()])}),
        // LUT fuse mutually exclusive inputs

        // LUT fuse non-mutually exclusive inputs (hard, opposite of DSD)
    ]
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
}
fn main() {
    println!("Hello, world!");
    lut::init();
}
