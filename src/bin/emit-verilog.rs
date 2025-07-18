use std::{
    io::{IsTerminal, Read, Write},
    path::PathBuf,
};

use clap::Parser;
use egg::RecExpr;
use eqmap::{asic::CellLang, driver::Canonical, lut::LutLang, verilog::SVModule};
/// Emit a LutLang Expression as a Verilog Netlist
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Path to input file. If not provided, reads from stdin
    input: Option<PathBuf>,

    /// The name of the module to generate
    #[arg(short = 'm', long)]
    mod_name: Option<String>,

    /// The names of the output ports from right to left
    #[arg(short = 'o', long)]
    output_names: Vec<String>,

    /// Emit a specific LUT expr instead of from file
    #[arg(long)]
    command: Option<String>,

    /// Canonicalize the input expression
    #[arg(short = 'c', long, default_value_t = false)]
    canonicalize: bool,

    /// Parse input as a CellLang expression
    #[arg(short = 'a', long, default_value_t = false)]
    asic: bool,
}

fn main() -> std::io::Result<()> {
    let args = Args::parse();
    let mut buf = String::new();

    let mod_name = if args.command.is_some() {
        buf = args.command.unwrap();
        args.mod_name.unwrap_or("top".to_string())
    } else {
        match args.input {
            Some(p) => {
                std::fs::File::open(&p)?.read_to_string(&mut buf)?;
                let stem = p.file_stem().unwrap().to_str().unwrap();
                args.mod_name.unwrap_or(stem.to_string())
            }
            None => {
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
                args.mod_name.unwrap_or("top".to_string())
            }
        }
    };

    for line in buf.lines() {
        let line = line.trim();
        if line.starts_with("//") || line.is_empty() {
            continue;
        }
        let expr = line.split("//").next().unwrap();
        let module = if !args.asic {
            let expr: RecExpr<LutLang> = expr.parse().map_err(std::io::Error::other)?;

            let expr = if args.canonicalize {
                LutLang::canonicalize_expr(expr)
            } else {
                expr
            };

            SVModule::from_luts(expr, mod_name.clone(), args.output_names.clone())
                .map_err(std::io::Error::other)?
        } else {
            let expr: RecExpr<CellLang> = expr.parse().map_err(std::io::Error::other)?;

            SVModule::from_cells(expr, mod_name.clone(), args.output_names.clone())
                .map_err(std::io::Error::other)?
        };
        print!("{module}");
        break;
    }

    Ok(())
}
