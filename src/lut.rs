/*!

  The lut module defines the grammar used to represent LUTs, gates, and principal inputs.

*/
use std::collections::HashMap;

use super::analysis::LutAnalysis;
use bitvec::prelude::*;
use egg::define_language;
use egg::Id;
use egg::Language;
use egg::RecExpr;
use egg::Symbol;

define_language! {
    /// Definitions of e-node types. [Program] is the only node type that is not a net/signal.
    #[allow(missing_docs)]
    pub enum LutLang {
        Const(bool),
        Program(u64), // The only node type that is not a net
        Var(Symbol),
        "x" = DC,
        "NOR" = Nor([Id; 2]),
        "MUX" = Mux([Id; 3]), // s, a, b
        "AND" = And([Id; 2]),
        "XOR" = Xor([Id; 2]),
        "NOT" = Not([Id; 1]),
        "LUT" = Lut(Box<[Id]>), // Program is first
    }
}

impl LutLang {
    /// Verify the grammar of a single [LutLang] node
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
            LutLang::Var(f) => match f.as_str() {
                "NOR" | "LUT" | "MUX" | "AND" | "XOR" | "NOT" => {
                    return Err(
                        "Variable name is already reserved. Check for missing parentheses."
                            .to_string(),
                    );
                }
                _ => Ok(()),
            },
            _ => Ok(()),
        }
    }

    /// Recursively verify the grammar of a [LutLang] expression `expr` rooted at `self`
    pub fn verify_rec(&self, expr: &RecExpr<Self>) -> Result<(), String> {
        self.verify()?;
        for c in self.children() {
            let t = &expr[*c];
            t.verify_rec(expr)?;
            match self {
                LutLang::Lut(l) => {
                    if let LutLang::Program(p) = expr[l[0]] {
                        let k = l.len() - 1;
                        if k < 6 && p >= (1 << (1 << k)) {
                            return Err("Program too large for LUT".to_string());
                        }
                    } else {
                        return Err("LUT must have a program".to_string());
                    }
                }
                _ => (),
            }
        }
        Ok(())
    }

    /// Extract the program from a [LutLang::Lut] contained in expression `expr`
    pub fn get_program(&self, expr: &RecExpr<Self>) -> Result<u64, String> {
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

    /// Extract the program from a [LutLang::Lut] contained in `egraph`
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

    /// Extract the operand class ids from a [LutLang::Lut] contained in `egraph`
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

    /// Returns the fan-in of a [LutLang::Lut]
    pub fn get_lut_size(&self) -> Result<usize, String> {
        match self {
            LutLang::Lut(l) => {
                self.verify()?;
                Ok(l.len() - 1)
            }
            _ => Err("Not a LUT".to_string()),
        }
    }

    /// Evaluates the boolean value of a [LutLang] node contained in `expr` given the input state `inputs`
    fn eval(&self, inputs: &HashMap<String, bool>, expr: &RecExpr<Self>) -> bool {
        match self {
            LutLang::Const(b) => *b,
            LutLang::Var(s) => *inputs.get(s.as_str()).unwrap(),
            LutLang::Program(_) => panic!("Program node should not be evaluated"),
            LutLang::DC => false,
            LutLang::Nor(a) => {
                let a0 = &a[0];
                let a1 = &a[1];
                !(expr[*a0].eval(inputs, expr) || expr[*a1].eval(inputs, expr))
            }
            LutLang::And(a) => {
                let a0 = &a[0];
                let a1 = &a[1];
                expr[*a0].eval(inputs, expr) && expr[*a1].eval(inputs, expr)
            }
            LutLang::Xor(a) => {
                let a0 = &a[0];
                let a1 = &a[1];
                expr[*a0].eval(inputs, expr) ^ expr[*a1].eval(inputs, expr)
            }
            LutLang::Not(a) => {
                let a0 = &a[0];
                !expr[*a0].eval(inputs, expr)
            }
            LutLang::Mux(a) => {
                let a0 = &a[0];
                let a1 = &a[1];
                let a2 = &a[2];
                if expr[*a0].eval(inputs, expr) {
                    expr[*a1].eval(inputs, expr)
                } else {
                    expr[*a2].eval(inputs, expr)
                }
            }
            LutLang::Lut(a) => {
                let p = match expr[*a.first().unwrap()] {
                    LutLang::Program(p) => p,
                    _ => panic!("First element of LUT must be a program"),
                };
                let x: Vec<bool> = a[1..]
                    .iter()
                    .map(|id| expr[*id].eval(inputs, expr))
                    .collect();
                eval_lut(p, &x)
            }
        }
    }

    /// This funcion returns true if two expressions evaluate to the same value under the certain `inputs`
    pub fn func_equiv(
        expr: &RecExpr<Self>,
        other: &RecExpr<Self>,
        inputs: &HashMap<String, bool>,
    ) -> bool {
        expr[(expr.as_ref().len() - 1).into()].eval(inputs, expr)
            == other[(other.as_ref().len() - 1).into()].eval(inputs, other)
    }

    fn get_inputs(&self) -> Vec<String> {
        match self {
            LutLang::Var(s) => vec![s.as_str().to_string()],
            _ => Vec::new(),
        }
    }

    fn get_inputs_rec(&self, expr: &RecExpr<Self>) -> Vec<String> {
        let mut inputs = self.get_inputs();
        let mut children_inputs: Vec<String> = self
            .children()
            .iter()
            .map(|c| expr[*c].get_inputs_rec(expr))
            .flatten()
            .collect();
        inputs.append(&mut children_inputs);
        inputs
    }

    fn get_input_set(&self, expr: &RecExpr<Self>) -> Vec<String> {
        let mut inputs = self.get_inputs_rec(expr);
        inputs.sort();
        inputs.dedup();
        inputs
    }

    /// Given two expressions and a set of input values,
    /// this funcion returns true if they represent the same boolean function
    pub fn func_equiv_always(expr: &RecExpr<Self>, other: &RecExpr<Self>) -> bool {
        let root = &expr[(expr.as_ref().len() - 1).into()];
        let inputs = root.get_input_set(&expr);
        for i in 0..1 << inputs.len() {
            let input_map = inputs
                .iter()
                .cloned()
                .zip((0..inputs.len()).map(|j| (i >> j) & 1 == 1))
                .collect();
            let result = Self::func_equiv(&expr, &other, &input_map);
            if !result {
                return false;
            }
        }
        true
    }
}

/// Verify the grammar of a [LutLang] expression from its root
pub fn verify_expr(expr: &RecExpr<LutLang>) -> Result<(), String> {
    expr.as_ref().last().unwrap().verify_rec(expr)?;
    Ok(())
}

/// Evaluates the boolean value of a Lut program given a slice of [bool] inputs (msb first).
pub fn eval_lut(p: u64, inputs: &[bool]) -> bool {
    let mut index = 0;
    for (i, input) in inputs.iter().rev().enumerate() {
        if *input {
            index += 1 << i;
        }
    }
    (p >> index) & 1 == 1
}

/// Convert a [u64] LUT program to a lsb-first [BitVec] of length `capacity`
pub fn to_bitvec(p: u64, capacity: usize) -> BitVec {
    assert!(capacity <= 64);
    let mut bv: BitVec = bitvec!(usize, Lsb0; 0; capacity);
    bv[0..capacity].store::<u64>(p);
    bv
}

/// Convert a lsb-first [BitVec] LUT program to a [u64]
pub fn from_bitvec(bv: &BitVec) -> u64 {
    assert!(bv.len() <= 64);
    bv[0..bv.len()].load::<u64>()
}

/// Evaluates the boolean value of a LUT program given a [BitVec] (lsb first).
pub fn eval_lut_bv(p: u64, inputs: &BitVec) -> bool {
    let mut index = 0;
    assert!(inputs.len() <= 64);
    for (i, input) in inputs.iter().enumerate() {
        if *input {
            index += 1 << i;
        }
    }
    (p >> index) & 1 == 1
}

/// Return a partially-evaluated LUT program with the `msb` input tied to the constant `v`
pub fn eval_lut_const_input(p: &u64, msb: usize, v: bool) -> u64 {
    assert!(msb <= 5);
    assert_eq!(msb >> (1 << (msb + 1)), 0);
    if v {
        p >> (1 << msb)
    } else {
        p & (1 << (1 << msb)) - 1
    }
}

/// Swap the truth table for input `pos` and input `pos + 1`, where `pos` is offset from the lsb.
/// Together these generate the permutation group.
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
    let mut nbv: BitVec = bitvec!(usize, Lsb0; 0; 1 << k);
    for i in 0..(1 << k) {
        let index = from_bitvec(&list[i]) as usize;
        nbv.set(index, eval_lut_bv(*bv, &to_bitvec(i as u64, k)));
    }
    from_bitvec(&nbv)
}
