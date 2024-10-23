use std::io::Read;

use egg::*;
use lut_synth::{cost::LUTKCostFn, lut, rewrite::all_rules};

/// simplify expr using egg, and pretty print it back out
fn simplify_expr(
    expr: &RecExpr<lut::LutLang>,
) -> (RecExpr<lut::LutLang>, Explanation<lut::LutLang>) {
    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let mut runner = Runner::default()
        .with_explanations_enabled()
        .with_expr(&expr)
        .run(&all_rules());

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];
    // println!("{:?}", runner.egraph);

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, LUTKCostFn::<6>);
    let (_best_cost, best) = extractor.find_best(root);
    let expl = runner.explain_equivalence(&expr, &best);
    eprintln!(
        "Saturated to {} nodes",
        runner.egraph.total_number_of_nodes()
    );
    (best, expl)
}

/// parse an expression, simplify it using egg, and pretty print it back out
fn simplify(s: &str) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<lut::LutLang> = s.parse().unwrap();

    simplify_expr(&expr).0.to_string()
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

#[test]
fn redundant_inputs() {
    assert_eq!(simplify("(LUT 1 a a a a a)"), "(LUT 1 a)");
    assert_eq!(simplify("(LUT 1 a a a a a a)"), "(LUT 1 a)");
    assert_eq!(simplify("(LUT 1 a b a b a b)"), "(LUT 1 a b)");
}

#[test]
fn test_eval() {
    let expr: RecExpr<lut::LutLang> = "(MUX s0 a b)".parse().unwrap();
    let other: RecExpr<lut::LutLang> = "(LUT 202 s0 a b)".parse().unwrap();
    assert!(lut::LutLang::func_equiv_always(&expr, &other));
}

// #[test]
// fn test_dsd() {
//     let expr: RecExpr<lut::LutLang> = "(MUX s1 (MUX s0 a b) (MUX s0 c d))".parse().unwrap();
//     let other: RecExpr<lut::LutLang> = "(LUT 17858377336630846080 s1 s0 a b c d)".parse().unwrap();
//     assert!(lut::LutLang::func_equiv_always(&expr, &other));
// }

fn main() -> std::io::Result<()> {
    let mut buf = String::new();
    std::io::stdin().read_to_string(&mut buf)?;
    for line in buf.lines() {
        let line = line.trim();
        if line.starts_with("//") || line.is_empty() {
            continue;
        }
        let expr = line.split("//").next().unwrap();
        let expr: RecExpr<lut::LutLang> = expr.parse().unwrap();
        let (simplified, expl) = simplify_expr(&expr);
        println!("{} => {}", expr.to_string(), simplified.to_string());

        // Verify functionality
        if true {
            let result = lut::LutLang::func_equiv_always(&expr, &simplified);
            if !result {
                eprintln!("Failed for explanation {:?}", expl.to_string());
                return Err(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "Functionality verification failed",
                ));
            }
        }
    }
    Ok(())
}
