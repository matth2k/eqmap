/*!

  The code module contains a super simple cost function that extracts LUTs with at most `k` fan-in.

*/
use super::lut::LutLang;
use egg::{CostFunction, Id, Language, RecExpr};

/// A cost function that extracts LUTs with at most `k` fan-in.
pub struct KLUTCostFn {
    k: usize,
}

impl KLUTCostFn {
    /// Returns a new cost function with the given `k` value.
    pub fn new(k: usize) -> Self {
        if k < 1 || k > LutLang::MAX_LUT_SIZE {
            panic!("k must be between 1 and {}", LutLang::MAX_LUT_SIZE);
        }
        Self { k }
    }
}

impl CostFunction<LutLang> for KLUTCostFn {
    type Cost = u64;
    fn cost<C>(&mut self, enode: &LutLang, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            LutLang::Lut(l) => {
                if l.len() <= self.k + 1 {
                    (l.len() - 1) as u64
                } else {
                    u64::MAX
                }
            }
            LutLang::Program(_) => 0,
            LutLang::Const(_) => 0,
            LutLang::Var(_) => 1,
            LutLang::DC => 0,
            _ => u64::MAX,
        };
        enode.fold(op_cost, |sum, id| {
            if costs(id) > u64::MAX - sum {
                u64::MAX
            } else {
                sum + costs(id)
            }
        })
    }
}

/// The size of a given LUT.
pub enum LutSize {
    /// A LUT of given size.
    Size(usize),
    /// A LUT of any size. A wildcard in a sense.
    Any,
}

/// A cost function counting LUTs of a given size.
pub struct NumKLUTsCostFn {
    size: LutSize,
}

impl NumKLUTsCostFn {
    /// Returns a new cost function counting LUTs of `size`.
    pub fn new(size: LutSize) -> Self {
        const TOO_LARGE: usize = LutLang::MAX_LUT_SIZE + 1;
        match size {
            LutSize::Size(0) | LutSize::Size(TOO_LARGE..) => {
                panic!("k must be between 1 and {}", LutLang::MAX_LUT_SIZE)
            }
            size => Self { size },
        }
    }
}

impl CostFunction<LutLang> for NumKLUTsCostFn {
    type Cost = u64;
    fn cost<C>(&mut self, enode: &LutLang, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            LutLang::Lut(l) => match self.size {
                LutSize::Size(k) if l.len() == k + 1 => 1,
                LutSize::Any => 1,
                LutSize::Size(_) => 0,
            },
            LutLang::Program(_)
            | LutLang::Const(_)
            | LutLang::Var(_)
            | LutLang::DC
            | LutLang::Nor(_)
            | LutLang::Mux(_)
            | LutLang::And(_)
            | LutLang::Xor(_)
            | LutLang::Not(_) => 0,
        };
        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

/// Return the number of luts in the given expr.
pub fn get_lut_count(expr: &RecExpr<LutLang>) -> u64 {
    NumKLUTsCostFn::new(LutSize::Any).cost_rec(expr)
}

/// Return the number of k-luts in the given expr.
pub fn get_lut_count_k(expr: &RecExpr<LutLang>, k: usize) -> u64 {
    let size = LutSize::Size(k);
    NumKLUTsCostFn::new(size).cost_rec(expr)
}
