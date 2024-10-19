use super::analysis::LutAnalysis;
use bitvec::prelude::*;
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
        "MUX" = Mux([Id; 3]), // s, a, b
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
    fn get_program(&self, expr: &RecExpr<Self>) -> Result<u64, String> {
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

    /// Extract the program from a Lut node contained in [egraph]
    pub fn get_program_in_egraph(
        &self,
        egraph: &egg::EGraph<LutLang, LutAnalysis>,
    ) -> Result<u64, String> {
        match self {
            LutLang::Lut(l) => {
                self.verify()?;
                let p = l.first().unwrap();
                let class = &egraph[*p];
                let data = &class.data;
                data.get_program()
            }
            _ => Err("Not a LUT".to_string()),
        }
    }

    /// Extract the program from a Lut node contained in [egraph]
    pub fn get_operand_classes(
        &self,
        _egraph: &egg::EGraph<LutLang, LutAnalysis>,
    ) -> Result<Vec<Id>, String> {
        match self {
            LutLang::Lut(l) => {
                self.verify()?;
                Ok(Vec::from(&l[1..]))
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

/// [inputs] should be big-end first
pub fn eval_lut(p: u64, inputs: &[bool]) -> bool {
    let mut index = 0;
    for (i, input) in inputs.iter().rev().enumerate() {
        if *input {
            index += 1 << i;
        }
    }
    (p >> index) & 1 == 1
}

/// Convert a u64 LUT to a bitvec
pub fn to_bitvec(p: u64, capacity: usize) -> BitVec {
    assert!(capacity <= 64);
    let mut bv: BitVec = bitvec!(usize, Lsb0; 0; capacity);
    bv[0..capacity].store::<u64>(p);
    bv
}

/// Convert a bitvec to a u64 LUT
pub fn from_bitvec(bv: &BitVec) -> u64 {
    assert!(bv.len() <= 64);
    bv[0..bv.len()].load::<u64>()
}

/// Evaluate a LUT with a bitvec input stored lsb first
pub fn eval_lut_bv(p: u64, inputs: &BitVec) -> bool {
    let mut index = 0;
    assert!(inputs.len() <= 6);
    for (i, input) in inputs.iter().enumerate() {
        if *input {
            index += 1 << i;
        }
    }
    (p >> index) & 1 == 1
}

/// Return the LUT with the [msb] input tied to [v]
pub fn eval_lut_const_input(p: &u64, msb: usize, v: bool) -> u64 {
    assert!(msb <= 5);
    assert_eq!(msb >> (1 << (msb + 1)), 0);
    if v {
        p >> (1 << msb)
    } else {
        p & (1 << (1 << msb)) - 1
    }
}

/// Swap the truth table for input i and input (i+1).
/// Together these generate the permutation group.
/// [pos] 0 is the lsb.
pub fn swap_pos(bv: &u64, k: usize, pos: usize) -> u64 {
    assert!(pos < k - 1);
    let mut list: Vec<BitVec> = Vec::new();
    for i in 0..(1 << k) {
        list.push(to_bitvec(i, k));
    }
    for i in 0..(1 << k) {
        let tmp = list[i][pos];
        let tmp2 = list[i][pos + 1];
        list[i].set(pos, tmp2);
        list[i].set(pos + 1, tmp);
    }
    let mut nbv: BitVec = BitVec::with_capacity(1 << k);
    for i in 0..(1 << k) {
        nbv.push(eval_lut_bv(*bv, &list[i]));
    }
    from_bitvec(&nbv)
}

/// Fuse look-up tables [p] into [q] at position [i]
/// Will crash if the result would be >= 2**64.
/// Only works for mutually exclusive input groups.
pub fn fuse_lut(p: &u64, q: &u64, i: usize) -> u64 {
    (p << (1 << i)) | q
}

/// Fuse look-up tables [p] with [q]
pub fn fuse_lut_heavy(p: &u64, q: &u64, pi: &[Id], qi: &[Id]) -> (u64, Vec<Id>) {
    todo!()
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
