use clap::Parser;
use egg::*;
use lut_synth::{
    cost::KLUTCostFn,
    lut,
    rewrite::{all_rules_minus_dsd, known_decompositions},
};
use std::{
    io::{IsTerminal, Read},
    path::PathBuf,
    time::Duration,
};

/// simplify `expr` using egg with at most `k` fan-in on LUTs
fn simplify_expr<A>(
    expr: &RecExpr<lut::LutLang>,
    rules: &Vec<Rewrite<lut::LutLang, A>>,
    k: usize,
    gen_proof: bool,
) -> (RecExpr<lut::LutLang>, Option<Explanation<lut::LutLang>>)
where
    A: Analysis<lut::LutLang> + std::default::Default,
{
    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it

    let mut runner = if gen_proof {
        Runner::default().with_explanations_enabled()
    } else {
        Runner::default().with_explanations_disabled()
    };
    let mut runner = runner
        .with_time_limit(Duration::from_secs(20))
        .with_expr(&expr)
        .run(rules);

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, KLUTCostFn::new(k));
    let (_best_cost, best) = extractor.find_best(root);
    let expl = if gen_proof {
        runner.explain_equivalence(&expr, &best).into()
    } else {
        None
    };
    eprintln!(
        "Grown to {} nodes with reason {:?}",
        runner.egraph.total_number_of_nodes(),
        runner
            .stop_reason
            .unwrap_or(egg::StopReason::Other("Unknown".to_string()))
    );
    (best, expl)
}

/// parse an expression, simplify it with DSD and at most 4 fan-in, and pretty print it back out
fn simplify(s: &str) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<lut::LutLang> = s.parse().unwrap();
    let mut rules = all_rules_minus_dsd();
    rules.append(&mut known_decompositions());

    simplify_expr(&expr, &rules, 4, false).0.to_string()
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

#[test]
fn test_dsd() {
    let expr: RecExpr<lut::LutLang> = "(MUX s1 (MUX s0 a b) (MUX s0 c d))".parse().unwrap();
    let other: RecExpr<lut::LutLang> = "(LUT 18374951396690406058 s1 s0 a b c d)".parse().unwrap();
    assert!(lut::LutLang::func_equiv_always(&expr, &other));
    let dsd: RecExpr<lut::LutLang> = "(LUT 51952 s1 (LUT 61642 s1 s0 c d) a b)".parse().unwrap();
    assert!(lut::LutLang::func_equiv_always(&other, &dsd));
}

#[test]
fn test_incorrect_dsd() {
    let expr: RecExpr<lut::LutLang> = "(MUX s1 (MUX s0 a b) (MUX s0 c d))".parse().unwrap();
    let p: u64 = 18374951396690406058;
    for i in 0..64 {
        let pos_to_flip: usize = i;
        let p = p ^ (1 << pos_to_flip);
        let other: RecExpr<lut::LutLang> = format!("(LUT {} s1 s0 a b c d)", p).parse().unwrap();
        assert!(!lut::LutLang::func_equiv_always(&expr, &other));
    }
}

/// Lut-Synth Args
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Path to input file. If not provided, reads from stdin
    input: Option<PathBuf>,

    /// Don't verify functionality of the output
    #[arg(short = 'c', long, default_value_t = false)]
    no_verify: bool,

    /// Don't use disjoint set decompositions
    #[arg(short, long, default_value_t = false)]
    no_dsd: bool,

    /// Print explanations (this generates a proof and runs longer)
    #[arg(short = 'v', long, default_value_t = false)]
    verbose: bool,

    /// Max fan in size for LUTs
    #[arg(short = 'k', long, default_value_t = 4)]
    k: usize,
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

    let mut rules = all_rules_minus_dsd();
    if !args.no_dsd {
        rules.append(&mut known_decompositions());
    }

    for line in buf.lines() {
        let line = line.trim();
        if line.starts_with("//") || line.is_empty() {
            continue;
        }
        let expr = line.split("//").next().unwrap();
        let expr: RecExpr<lut::LutLang> = expr.parse().unwrap();

        if !args.no_verify {
            lut::verify_expr(&expr)
                .map_err(|s| std::io::Error::new(std::io::ErrorKind::Other, s))?;
        }

        let (simplified, expl) = simplify_expr(&expr, &rules, args.k, args.verbose);
        let expl: Option<String> = match expl {
            Some(mut e) => e.get_flat_string().into(),
            None => None,
        };

        if args.verbose {
            eprintln!("{}", expl.as_ref().unwrap());
        } else {
            eprintln!("{} => ", expr.to_string());
        }

        println!("{}", simplified.to_string());

        // Verify functionality
        if args.no_verify {
            eprintln!("Skipping functonality tests...");
        } else {
            let result = lut::LutLang::func_equiv_always(&expr, &simplified);
            if !result {
                match expl.as_ref() {
                    Some(e) => eprintln!("Failed for explanation {}", e),
                    None => eprintln!("Failed for unknown reason. Try running with --verbose for an attempted proof"),
                }
                return Err(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "Functionality verification failed",
                ));
            }
        }
    }
    Ok(())
}
