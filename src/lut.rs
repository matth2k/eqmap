use egg::define_language;
use egg::Id;
use egg::Language;
use egg::RecExpr;
use egg::Symbol;

const OR_TABLE: u64 = 0xFFFFFFFFFFFFFFFE;
const NOR_TABLE: u64 = 0x1;

define_language! {
    pub enum LutLang {
        Const(bool),
        Program(u64), // The only node type that is not a net
        Var(Symbol),
        "x" = DC,
        "NOR" = Nor([Id; 2]),
        // "NAND" = Nand([Id; 2]),
        "LUT" = Lut(Box<[Id]>), // Program is first
    }
}

impl LutLang {
    /// Verify a LutLang node
    fn verify(&self) -> Result<(), String> {
        match self {
            LutLang::Lut(list) => {
                let l = list.len();
                if l == 0 {
                    return Err("LUT must have at least one element".to_string());
                } else if l - 1 > 6 {
                    return Err("Only 6-Luts or smaller supported".to_string());
                } else {
                    Ok(())
                }
            }
            _ => Ok(()),
        }
    }

    /// Verify a LutLang expression [expr] rooted at [self]
    fn verify_rec(&self, expr: &RecExpr<Self>) -> Result<(), String> {
        self.verify()?;
        for c in self.children() {
            let t = &expr[*c];
            t.verify_rec(expr)?;
        }
        Ok(())
    }

    /// Extract the program from a Lut node contained in expression [expr]
    fn get_program(&self, expr: RecExpr<Self>) -> Result<u64, String> {
        match self {
            LutLang::Lut(l) => {
                self.verify()?;
                let p = l.first().unwrap();
                match expr[*p] {
                    LutLang::Program(p) => Ok(p),
                    _ => Err("First element of LUT must be a program".to_string()),
                }
            }
            _ => Err("Not a LUT".to_string()),
        }
    }

    /// Identify a node as a k-LUT and return k
    fn get_lut_size(&self) -> Result<usize, String> {
        match self {
            LutLang::Lut(l) => {
                self.verify()?;
                Ok(l.len() - 1)
            }
            _ => Err("Not a LUT".to_string()),
        }
    }
}

pub fn eval_lut(p: u64, inputs: &[bool]) -> bool {
    let b2: usize = 2;
    let mut index = 0;
    for (i, input) in inputs.iter().rev().enumerate() {
        if *input {
            index += b2.pow(i as u32);
        }
    }
    (p >> index) & 1 == 1
}

pub fn init() {
    println!("Initializing LUT");
    let mut expr: RecExpr<LutLang> = RecExpr::default();
    let a = expr.add(LutLang::Var(Symbol::from("a")));
    let b = expr.add(LutLang::Var(Symbol::from("b")));
    let program = expr.add(LutLang::Program(0));
    let f = expr.add(LutLang::Lut(vec![program, a, b].into()));
    println!("LUT: {} {:?}", expr, f);
}
