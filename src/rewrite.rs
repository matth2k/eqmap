use super::analysis::LutAnalysis;
use super::lut;
use bitvec::{bitvec, order::Lsb0};
use egg::{rewrite, Applier, Rewrite, Var};

pub fn all_rules() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules: Vec<Rewrite<lut::LutLang, LutAnalysis>> = Vec::new();
    // Logic element conversions
    rules.push(rewrite!("nor2-conversion"; "(NOR ?a ?b)" => "(LUT 1 ?a ?b)"));

    // s? a : b
    rules.push(rewrite!("mux2-1-conversion"; "(MUX ?s ?a ?b)" => "(LUT 202 ?s ?a ?b)"));

    // Evaluate constant programs
    rules.push(rewrite!("lut2-const"; "(LUT 0 ?a ?b)" => "false"));
    rules.push(rewrite!("lut3-const"; "(LUT 0 ?a ?b ?c)" => "false"));
    rules.push(rewrite!("lut4-const"; "(LUT 0 ?a ?b ?c ?d)" => "false"));
    rules.push(rewrite!("lut5-const"; "(LUT 0 ?a ?b ?c ?d ?e)" => "false"));
    rules.push(rewrite!("lut6-const"; "(LUT 0 ?a ?b ?c ?d ?e ?d)" => "false"));

    // Evaluate constant inputs (impl as modify-analysis for multi-input cases)
    rules.push(rewrite!("lut1-const-f"; "(LUT 0 ?a)" => "false"));
    rules.push(rewrite!("lut1-const-t"; "(LUT 3 ?a)" => "true"));
    rules.push(rewrite!("lut1-const-id"; "(LUT 2 ?a)" => "?a"));
    rules.push(rewrite!("lut1-const-if"; "(LUT 1 false)" => "true"));
    rules.push(rewrite!("lut1-const-it"; "(LUT 1 true)" => "false"));

    // Remove redudant inputs
    rules.push(rewrite!("lut2-redundant"; "(LUT ?p ?a ?a)" => {CombineAlikeInputs::new("?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?a".parse().unwrap()])}));
    rules.push(rewrite!("lut3-redundant"; "(LUT ?p ?a ?a ?b)" => {CombineAlikeInputs::new("?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?a".parse().unwrap(), "?b".parse().unwrap()])}));
    rules.push(rewrite!("lut4-redundant"; "(LUT ?p ?a ?a ?b ?c)" => {CombineAlikeInputs::new("?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap()])}));
    rules.push(rewrite!("lut5-redundant"; "(LUT ?p ?a ?a ?b ?c ?d)" => {CombineAlikeInputs::new("?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap(), "?d".parse().unwrap()])}));
    rules.push(rewrite!("lut6-redundant"; "(LUT ?p ?a ?a ?b ?c ?d ?e)" => {CombineAlikeInputs::new("?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap(), "?d".parse().unwrap(), "?e".parse().unwrap()])}));

    // DSD an input 6-LUT into two 4-LUTs
    // DSD with one shared variable: an k-LUT (k even) into two (N/2 + 1)-LUTS

    // LUT permutation groups
    rules.push(rewrite!("lut2-permute"; "(LUT ?p ?a ?b)" 
        => {PermuteInput::new(1, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap()])}));

    for i in 1..3 {
        let rname = format!("lut3-permute-{}", i);
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap()])}));
    }

    for i in 1..4 {
        let rname = format!("lut4-permute-{}", i);
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c ?d)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap(), "?d".parse().unwrap()])}));
    }

    for i in 1..5 {
        let rname = format!("lut5-permute-{}", i);
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c ?d ?e)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap(), "?d".parse().unwrap(), "?e".parse().unwrap()])}));
    }

    for i in 1..6 {
        let rname = format!("lut6-permute-{}", i);
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c ?d ?e ?f)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap(), "?d".parse().unwrap(), "?e".parse().unwrap(), "?f".parse().unwrap()])}));
    }
    // LUT fuse inputs (exclusive or not, sometimes the opposite of DSD)

    // 2-(2,2) => 4-LUT
    // 2-(2,3) => 5-LUT
    // 2-(3,3) => 6-LUT
    // 3-(2,2,2) => 6-LUT

    // LUT fuse non-mutually exclusive inputs (hard, opposite of DSD)
    rules
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
