use super::lut;
use egg::{Analysis, DidMerge};

/// This is the data associated with an eclass
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LutAnalysisData {
    /// If a class is a Program(u64), it should be alone
    program: Option<u64>,
    /// If a class is a constant true or false, store it
    const_val: Option<bool>,
    /// If a class is an input, store it
    input: Option<String>,
}

impl LutAnalysisData {
    pub fn new(program: Option<u64>, const_val: Option<bool>, input: Option<String>) -> Self {
        Self {
            program,
            const_val,
            input,
        }
    }

    pub fn default() -> Self {
        Self {
            program: None,
            const_val: None,
            input: None,
        }
    }

    /// Extract the LUT program in this class. If it is an input or gate, throw an error
    pub fn get_program(&self) -> Result<u64, String> {
        match self.program {
            Some(p) => Ok(p),
            None => Err("No program found".to_string()),
        }
    }

    /// Return the constant associated with this class. If it is not a constant, throw an error.
    pub fn get_as_const(&self) -> Result<bool, String> {
        match self.const_val {
            Some(v) => Ok(v),
            None => Err("No constant value found".to_string()),
        }
    }

    pub fn is_an_input(&self) -> bool {
        self.input.is_some()
    }
}

#[derive(Default)]
pub struct LutAnalysis;
impl Analysis<lut::LutLang> for LutAnalysis {
    type Data = LutAnalysisData;
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        assert!(to.program == from.program);
        assert!(
            to.const_val == from.const_val || to.const_val.is_none() || from.const_val.is_none()
        );
        assert!(to.input == from.input || to.input.is_none() || from.input.is_none());
        let mut merged = to.clone();
        merged.const_val = from.const_val.or(to.const_val);
        merged.input = from.input.clone().or(to.input.clone());
        let merged_to = merged != *to;
        *to = merged;
        DidMerge(merged_to, *to != from)
    }
    fn make(egraph: &egg::EGraph<lut::LutLang, Self>, enode: &lut::LutLang) -> Self::Data {
        match enode {
            lut::LutLang::Lut(_l) => LutAnalysisData::new(None, None, None),
            lut::LutLang::Program(p) => LutAnalysisData::new(Some(*p), None, None),
            lut::LutLang::Const(c) => LutAnalysisData::new(None, Some(*c), None),
            lut::LutLang::Var(v) => LutAnalysisData::new(None, None, Some(v.to_string())),
            _ => LutAnalysisData::default(),
        }
    }
    fn modify(egraph: &mut egg::EGraph<lut::LutLang, Self>, id: egg::Id) {
        // Evaluate constant input at the msb
        let nodes = egraph[id].nodes.clone();
        for node in nodes {
            if let lut::LutLang::Lut(_) = node {
                let operands = node.get_operand_classes(egraph).expect("Expected operands");
                let msb_const = egraph[operands[0]].data.get_as_const();
                if msb_const.is_ok() {
                    let program = node
                        .get_program_in_egraph(egraph)
                        .expect("Expected program");
                    if operands.len() > 1 {
                        let mod_program = lut::eval_lut_const_input(
                            &program,
                            operands.len() - 1,
                            msb_const.unwrap(),
                        );
                        let pi = egraph.add(lut::LutLang::Program(mod_program));
                        let mut c = operands.clone();
                        c[0] = pi;
                        let repl = egraph.add(lut::LutLang::Lut(c.into()));
                        egraph.union(id, repl);
                    } else {
                        let const_val = msb_const.unwrap();
                        match program & 3 {
                            0 => {
                                let repl = egraph.add(lut::LutLang::Const(false));
                                egraph.union(id, repl);
                            }
                            3 => {
                                let repl = egraph.add(lut::LutLang::Const(true));
                                egraph.union(id, repl);
                            }
                            2 => {
                                let repl = egraph.add(lut::LutLang::Const(const_val));
                                egraph.union(id, repl);
                            }
                            1 => {
                                let repl = egraph.add(lut::LutLang::Const(!const_val));
                                egraph.union(id, repl);
                            }
                            _ => (),
                        }
                    }
                }
            }
        }
    }
}
