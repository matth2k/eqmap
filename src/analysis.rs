use super::lut;
use bitvec::{bitvec, order::Lsb0};
use egg::{Analysis, Applier, DidMerge, Var};

/// This is the data associated with an eclass
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LutAnalysisData {
    /// If a class is a Program(u64), it should be alone
    program: Option<u64>,
    /// If a class is a constant true or false, store it
    const_val: Option<bool>,
}

impl LutAnalysisData {
    pub fn new(program: Option<u64>, const_val: Option<bool>) -> Self {
        Self { program, const_val }
    }

    pub fn default() -> Self {
        Self {
            program: None,
            const_val: None,
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
}

#[derive(Default)]
pub struct LutAnalysis;
impl Analysis<lut::LutLang> for LutAnalysis {
    type Data = LutAnalysisData;
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        DidMerge(false, false)
    }
    fn make(egraph: &egg::EGraph<lut::LutLang, Self>, enode: &lut::LutLang) -> Self::Data {
        match enode {
            lut::LutLang::Lut(l) => LutAnalysisData::new(None, None),
            lut::LutLang::Program(p) => LutAnalysisData::new(Some(*p), None),
            lut::LutLang::Const(c) => LutAnalysisData::new(None, Some(*c)),
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

/// A rewrite applier for permuting input i with input i-1
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PermuteInput {
    /// Position of the input to permute
    pos: usize,
    program: Var,
    /// List of operands with msb first
    vars: Vec<Var>,
}

impl PermuteInput {
    pub fn new(pos: usize, program: Var, vars: Vec<Var>) -> Self {
        Self { pos, program, vars }
    }
}

impl Applier<lut::LutLang, LutAnalysis> for PermuteInput {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        subst: &egg::Subst,
        _searcher_ast: Option<&egg::PatternAst<lut::LutLang>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let operands = self
            .vars
            .iter()
            .map(|v| subst[*v])
            .collect::<Vec<egg::Id>>();
        let program = egraph[subst[self.program]]
            .data
            .get_program()
            .expect("Expected program");

        assert!(self.pos > 0);
        let pos_from_lsb = (operands.len() - 1) - self.pos;
        let new_program = lut::swap_pos(&program, operands.len(), pos_from_lsb);
        let new_program_id = egraph.add(lut::LutLang::Program(new_program));

        assert!(self.pos < operands.len());

        let mut swaperands = operands.clone();
        let tmp = swaperands[self.pos];
        swaperands[self.pos] = swaperands[self.pos - 1];
        swaperands[self.pos - 1] = tmp;

        let mut c = Vec::from(&[new_program_id]);
        c.append(&mut swaperands);

        let new_lut = egraph.add(lut::LutLang::Lut(c.into()));

        if egraph.union_trusted(eclass, new_lut, rule_name) {
            vec![new_lut]
        } else {
            vec![]
        }
    }
}

/// A rewrite applier for combining two inputs that are the same
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CombineAlikeInputs {
    /// The program redundant in var 0 and 1
    program: Var,
    /// The redundant inputs must be at position 0 and 1
    vars: Vec<Var>,
}

impl CombineAlikeInputs {
    pub fn new(program: Var, vars: Vec<Var>) -> Self {
        Self { program, vars }
    }
}

impl Applier<lut::LutLang, LutAnalysis> for CombineAlikeInputs {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        subst: &egg::Subst,
        _searcher_ast: Option<&egg::PatternAst<lut::LutLang>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let mut operands = self
            .vars
            .iter()
            .map(|v| subst[*v])
            .collect::<Vec<egg::Id>>();
        assert!(operands[0] == operands[1]);
        let program = egraph[subst[self.program]]
            .data
            .get_program()
            .expect("Expected program");
        let k = operands.len();
        let mut new_prog = bitvec!(usize, Lsb0; 0; 1 << (k-1));
        for i in 0..(1 << (k - 2)) {
            let eval_e = lut::eval_lut_bv(program, &lut::to_bitvec(i << 2, 1 << k));
            new_prog.set((i << 1) as usize, eval_e);
            let eval_o = lut::eval_lut_bv(program, &lut::to_bitvec((i << 2) + 3, 1 << k));
            new_prog.set((i << 1) as usize + 1, eval_o);
        }
        let new_prog = lut::from_bitvec(&new_prog);
        let new_prog_id = egraph.add(lut::LutLang::Program(new_prog));
        let mut c = Vec::from(&[new_prog_id]);
        operands.remove(1);
        c.append(&mut operands);
        let new_lut = egraph.add(lut::LutLang::Lut(c.into()));

        if egraph.union_trusted(eclass, new_lut, rule_name) {
            vec![new_lut]
        } else {
            vec![]
        }
    }
}
