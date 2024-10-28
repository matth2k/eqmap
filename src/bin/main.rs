use clap::Parser;
use egg::*;
use indicatif::{MultiProgress, ProgressBar, ProgressStyle};
use lut_synth::{
    cost::KLUTCostFn,
    lut,
    rewrite::{all_rules_minus_dsd, known_decompositions},
};
use std::{
    io::{IsTerminal, Read, Write},
    path::PathBuf,
    time::{Duration, Instant},
};

fn report_progress<A>(
    runner: &Runner<lut::LutLang, A>,
    iter_bar: &mut ProgressBar,
    node_bar: &mut ProgressBar,
) -> Result<(), String>
where
    A: Analysis<lut::LutLang> + std::default::Default,
{
    iter_bar.inc(1);
    let nodes = runner.egraph.total_number_of_nodes();
    node_bar.set_position(nodes as u64);
    Ok(())
}

/// simplify `expr` using egg with at most `k` fan-in on LUTs
fn simplify_expr<A>(
    expr: &RecExpr<lut::LutLang>,
    rules: &Vec<Rewrite<lut::LutLang, A>>,
    k: usize,
    gen_proof: bool,
    prog_bar: bool,
    timeout: u64,
    node_limit: usize,
    iter_limit: usize,
) -> (RecExpr<lut::LutLang>, Option<Explanation<lut::LutLang>>)
where
    A: Analysis<lut::LutLang> + std::default::Default,
{
    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it

    let runner = if gen_proof {
        eprintln!("WARNING: Proof generation is on (slow)");
        Runner::default().with_explanations_enabled()
    } else {
        Runner::default().with_explanations_disabled()
    };

    // Print a progress bar to get a sense of growth
    let mp = MultiProgress::new();

    // Use back-off scheduling on runner to avoid transpositions taking too much time
    let bos = BackoffScheduler::default()
        .with_ban_length(2)
        .with_initial_match_limit(960);

    let runner = runner
        .with_scheduler(bos)
        .with_time_limit(Duration::from_secs(timeout))
        .with_node_limit(node_limit)
        .with_iter_limit(iter_limit);

    let runner = if prog_bar {
        let (mut iter_bar, mut node_bar) = (
            mp.add(ProgressBar::new(iter_limit as u64).with_message("iterations")),
            mp.add(ProgressBar::new(node_limit as u64)),
        );
        iter_bar.set_style(
            ProgressStyle::with_template("[{bar:60.cyan/blue}] {pos}/{len} iterations").unwrap(),
        );
        node_bar.set_style(
            ProgressStyle::with_template("[{bar:60.magenta}] {pos}/{len} nodes").unwrap(),
        );
        runner.with_hook(move |r| report_progress(r, &mut iter_bar, &mut node_bar))
    } else {
        runner
    };

    let mut runner = runner.with_expr(&expr).run(rules);

    // Clear the progress bar
    mp.clear().unwrap();

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];
    if gen_proof {
        let report = runner.report();
        eprintln!("INFO: {}", report.to_string().replace("\n", "\nINFO: "));
    }

    // use an Extractor to pick the best element of the root eclass
    let extraction_start = Instant::now();
    let extractor = Extractor::new(&runner.egraph, KLUTCostFn::new(k));
    let (_best_cost, best) = extractor.find_best(root);
    let extraction_time = extraction_start.elapsed();
    if gen_proof {
        eprintln!(
            "INFO: Extraction time: {} seconds",
            extraction_time.as_secs_f64()
        );
    }
    let expl = if gen_proof {
        runner.explain_equivalence(&expr, &best).into()
    } else {
        None
    };
    eprintln!(
        "INFO: Grown to {} nodes with reason {:?}",
        runner.egraph.total_number_of_nodes(),
        runner
            .stop_reason
            .unwrap_or(egg::StopReason::Other("Unknown".to_string()))
    );
    (best, expl)
}

#[allow(dead_code)]
/// parse an expression, simplify it with DSD and at most 4 fan-in, and pretty print it back out
fn simplify(s: &str) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<lut::LutLang> = s.parse().unwrap();
    let mut rules = all_rules_minus_dsd();
    rules.append(&mut known_decompositions());

    simplify_expr(&expr, &rules, 4, false, false, 20, 20_000, 30)
        .0
        .to_string()
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

/// LUT Network Synthesis with E-Graphs
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Path to input file. If not provided, reads from stdin
    input: Option<PathBuf>,

    /// Don't verify functionality of the output
    #[arg(short = 'c', long, default_value_t = false)]
    no_verify: bool,

    /// Don't use disjoint set decompositions
    #[arg(short = 'd', long, default_value_t = false)]
    no_dsd: bool,

    /// Print explanations (this generates a proof and runs longer)
    #[arg(short = 'v', long, default_value_t = false)]
    verbose: bool,

    /// Max fan in size for LUTs
    #[arg(short = 'k', long, default_value_t = 4)]
    k: usize,

    /// Timeout in seconds for each expression
    #[arg(short = 't', long,
        default_value_t =
        if cfg!(debug_assertions) {
            24
        } else {
            8
        })
    ]
    timeout: u64,

    /// Maximum number of nodes in graph
    #[arg(short = 's', long, default_value_t = 18_000)]
    node_limit: usize,

    /// Maximum number of rewrite iterations
    #[arg(short = 'n', long, default_value_t = 20)]
    iter_limit: usize,
}

fn main() -> std::io::Result<()> {
    let args = Args::parse();
    let mut buf = String::new();

    if cfg!(debug_assertions) {
        eprintln!("WARNING: Debug assertions are enabled");
    }

    if args.input.is_some() {
        std::fs::File::open(args.input.unwrap())?.read_to_string(&mut buf)?;
    } else {
        let mut stdin = std::io::stdin();
        if stdin.is_terminal() {
            print!("> ");
            std::io::stdout().flush()?;
            while stdin.read_line(&mut buf)? <= 2 {
                print!("> ");
                std::io::stdout().flush()?;
            }
        } else {
            stdin.read_to_string(&mut buf)?;
        }
    }

    let mut rules = all_rules_minus_dsd();
    if !args.no_dsd {
        rules.append(&mut known_decompositions());
    }

    if args.verbose {
        eprintln!("INFO: Running with {} rewrite rules", rules.len());
        eprintln!(
            "INFO: DSD rewrites {}",
            if args.no_dsd { "OFF" } else { "ON" }
        );
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

        if cfg!(debug_assertions) {
            eprintln!("WARNING: Running with debug assertions is slow");
        }

        let (simplified, expl) = simplify_expr(
            &expr,
            &rules,
            args.k,
            args.verbose,
            true, // let's always use a progress bar for now
            args.timeout,
            args.node_limit,
            args.iter_limit,
        );
        let expl: Option<String> = match expl {
            Some(mut e) => {
                let proof = e.get_flat_string();
                let linecount = proof.lines().count();
                format!("{}\n Approx. {} lines in proof tree", proof, linecount).into()
            }
            None => None,
        };

        if args.verbose {
            eprintln!("INFO: {}", expl.as_ref().unwrap().replace("\n", "\nINFO: "));
            eprintln!("INFO: ============================================================");
        } else {
            eprintln!("{} => ", expr.to_string());
        }

        println!("{}", simplified.to_string());

        // Verify functionality
        if args.no_verify {
            eprintln!("INFO: Skipping functionality tests...");
        } else {
            let result = lut::LutLang::func_equiv_always(&expr, &simplified);
            if !result {
                match expl.as_ref() {
                    Some(e) => eprintln!("ERROR: Failed for explanation {}", e),
                    None => eprintln!("ERROR: Failed for unknown reason. Try running with --verbose for an attempted proof"),
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
