use egg::{CostFunction, Id, Language};

use super::lut::LutLang;

/// A cost function that extracts LUTs with at most `k` fan-in.
pub struct KLUTCostFn {
    k: usize,
}

impl KLUTCostFn {
    /// Returns a new cost function with the given `k` value.
    pub fn new(k: usize) -> Self {
        if k < 1 || k > 6 {
            panic!("k must be between 1 and 6");
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
                    l.len() as u64
                } else {
                    u64::MAX
                }
            }
            LutLang::Program(_) => 0,
            LutLang::Const(_) => 0,
            LutLang::Var(_) => 1,
            LutLang::DC => 0,
            LutLang::Nor(_) => u64::MAX,
            LutLang::Mux(_) => u64::MAX,
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
