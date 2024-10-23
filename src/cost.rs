use egg::{CostFunction, Id, Language};

use super::lut::LutLang;
pub struct LUTKCostFn<const K: usize>;
impl<const K: usize> CostFunction<LutLang> for LUTKCostFn<K> {
    type Cost = u64;
    fn cost<C>(&mut self, enode: &LutLang, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            LutLang::Lut(l) => {
                if l.len() <= K + 1 {
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
