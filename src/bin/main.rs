use clap::Parser;
use egg::*;
use lut_synth::{cost::LUTKCostFn, lut, rewrite::all_rules};
use std::{
    io::{IsTerminal, Read},
    path::PathBuf,
};

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
//     let other: RecExpr<lut::LutLang> = "(LUT 18374951396690406058 s1 s0 a b c d)".parse().unwrap();
//     let dsd: RecExpr<lut::LutLang> = "(LUT 1337 s1 (LUT 61642 ?s1 ?s0 ?c ?d) a b)"
//         .parse()
//         .unwrap();
//     assert!(lut::LutLang::func_equiv_always(&expr, &other));
//     assert!(lut::LutLang::func_equiv_always(&other, &dsd));
// }

/// Simple program to greet a person
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Path to input file. If not provided, reads from stdin
    input: Option<PathBuf>,

    /// Verify functionality of the output
    #[arg(short, long, default_value_t = false)]
    no_verify: bool,
}

fn main() -> std::io::Result<()> {
    let args = Args::parse();
    let mut buf = String::new();

    if args.input.is_some() {
        std::fs::File::open(args.input.unwrap())?.read_to_string(&mut buf)?;
    } else {
        let mut stdin = std::io::stdin();
        if stdin.is_terminal() {
            while stdin.read_line(&mut buf)? <= 1 {}
        } else {
            stdin.read_to_string(&mut buf)?;
        }
    }

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
        if !args.no_verify {
            eprintln!("Skipping functonality tests...");
        } else {
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
