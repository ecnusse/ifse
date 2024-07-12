//! This module defines AST nodes that generally conforms to the syntax described by SMT-LIB Standard 2.6.

use super::token::{Binary, Hexadecimal, Keyword, Numeral, Reserved, StringLiteral, Symbol};
use super::Decimal;
use crate::PrintableList;
use std::collections::VecDeque;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SpecConstant {
    Numeral(Numeral),
    Hexadecimal(Hexadecimal),
    Binary(Binary),
    StringLiteral(StringLiteral),
    Decimal(Decimal),
}

impl fmt::Display for SpecConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SpecConstant::*;
        match self {
            Numeral(n) => n.fmt(f),
            Hexadecimal(h) => h.fmt(f),
            Binary(b) => b.fmt(f),
            StringLiteral(s) => s.fmt(f),
            Decimal(d) => d.fmt(f),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SExpr {
    SpecConstant(SpecConstant),
    Symbol(Symbol),
    Keyword(Keyword),
    Reserved(Reserved),
    List(Vec<SExpr>),
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SExpr::*;
        match self {
            SpecConstant(c) => c.fmt(f),
            Symbol(s) => s.fmt(f),
            Keyword(k) => k.fmt(f),
            Reserved(r) => r.fmt(f),
            List(l) => {
                write!(f, "(")?;
                PrintableList(l).fmt(f)?;
                write!(f, ")")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Index {
    Numeral(Numeral),
    Symbol(Symbol),
}

impl fmt::Display for Index {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Index::*;
        match self {
            Numeral(n) => n.fmt(f),
            Symbol(s) => s.fmt(f),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Identifier {
    Symbol(Symbol),
    Indexed(Symbol, Vec<Index>),
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Identifier::*;
        match self {
            Symbol(s) => s.fmt(f),
            Indexed(s, indices) => {
                write!(f, "(_ ")?;
                write!(f, "{} ", s)?;
                PrintableList(indices).fmt(f)?;
                write!(f, ")")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AttributeValue {
    SpecConstant(SpecConstant),
    Symbol(Symbol),
    SExpr(Vec<SExpr>),
}

impl fmt::Display for AttributeValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use AttributeValue::*;
        match self {
            SpecConstant(c) => c.fmt(f),
            Symbol(s) => s.fmt(f),
            SExpr(s) => {
                write!(f, "(")?;
                PrintableList(s).fmt(f)?;
                write!(f, ")")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Attribute {
    Keyword(Keyword),
    WithValue(Keyword, AttributeValue),
}

impl fmt::Display for Attribute {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Attribute::*;
        match self {
            Keyword(k) => k.fmt(f),
            WithValue(k, v) => write!(f, "{} {}", k, v),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Sort {
    Simple(Identifier),
    Parametric(Identifier, Vec<Sort>),
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Sort::*;
        match self {
            Simple(id) => id.fmt(f),
            Parametric(id, sorts) => {
                write!(f, "({} ", id)?;
                PrintableList(sorts).fmt(f)?;
                write!(f, ")")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum QualIdentifier {
    Simple(Identifier),
    Qualified(Identifier, Sort),
}

impl fmt::Display for QualIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use QualIdentifier::*;
        match self {
            Simple(id) => id.fmt(f),
            Qualified(id, sort) => write!(f, "(as {} {})", id, sort),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VarBinding(pub Symbol, pub Term);
impl fmt::Display for VarBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SortedVar(pub Symbol, pub Sort);

impl fmt::Display for SortedVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Pattern {
    Simple(Symbol),
    Constructor(Symbol, Vec<Symbol>),
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Pattern::*;
        match self {
            Simple(s) => s.fmt(f),
            Constructor(s, ss) => {
                write!(f, "({} ", s)?;
                PrintableList(ss).fmt(f)?;
                write!(f, ")")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MatchCase(pub Pattern, pub Term);

impl fmt::Display for MatchCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    SpecConstant(SpecConstant),
    QualIdentifier(QualIdentifier),
    Let(Vec<VarBinding>, Box<Term>),
    Forall(Vec<SortedVar>, Box<Term>),
    Exists(Vec<SortedVar>, Box<Term>),
    Match(Box<Term>, Vec<MatchCase>),
    Annotated(Box<Term>, Vec<Attribute>),
    Apply(QualIdentifier, Vec<Term>),
}

impl Term {
    const MAX_DEPTH: usize = 2000;
    pub fn height(&self) -> Option<usize> {
        fn dfs_go_deep(term: &Term) -> Option<usize> {
            let mut stack: VecDeque<(&Term, usize)> = vec![(term, 1)].into();

            let mut max_depth = 0;
            while let Some((term, depth)) = stack.pop_front() {
                if depth >= Term::MAX_DEPTH {
                    return None;
                }
                use Term::*;
                match term {
                    SpecConstant(_) => {
                        max_depth = max_depth.max(depth);
                    }
                    QualIdentifier(_) => {
                        max_depth = max_depth.max(depth);
                    }
                    Let(bindings, term) => {
                        for binding in bindings {
                            stack.push_back((&binding.1, depth + 1));
                        }
                        stack.push_back((term, depth + 1));
                    }
                    Forall(_vars, term) => {
                        stack.push_back((term, depth + 1));
                    }
                    Exists(_vars, term) => {
                        stack.push_back((term, depth + 1));
                    }
                    Match(term, cases) => {
                        stack.push_back((term, depth + 1));
                        for case in cases {
                            stack.push_back((&case.1, depth + 1));
                        }
                    }
                    Annotated(term, _) => {
                        stack.push_back((term, depth + 1));
                    }
                    Apply(_, terms) => {
                        for term in terms {
                            stack.push_back((term, depth + 1));
                        }
                    }
                }
            }
            Some(max_depth)
        }

        dfs_go_deep(self)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Term::*;
        match self {
            SpecConstant(c) => c.fmt(f),
            QualIdentifier(q) => q.fmt(f),
            Let(bindings, term) => {
                write!(f, "(let (")?;
                PrintableList(bindings).fmt(f)?;
                write!(f, ") {})", term)
            }
            Forall(vars, term) => {
                write!(f, "(forall (")?;
                PrintableList(vars).fmt(f)?;
                write!(f, ") {})", term)
            }
            Exists(vars, term) => {
                write!(f, "(exists (")?;
                PrintableList(vars).fmt(f)?;
                write!(f, ") {})", term)
            }
            Match(term, cases) => {
                write!(f, "(match {} (", term)?;
                PrintableList(cases).fmt(f)?;
                write!(f, "))")
            }
            Annotated(term, attr) => write!(f, "(! {} {})", term, PrintableList(&attr)),
            Apply(id, terms) => {
                write!(f, "({} ", id)?;
                PrintableList(terms).fmt(f)?;
                write!(f, ")")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SortDeclaration(pub Symbol, pub Numeral);

impl fmt::Display for SortDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SelectorDeclaration(pub Symbol, pub Sort);

impl fmt::Display for SelectorDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstructorDeclaration(pub Symbol, pub Vec<SelectorDeclaration>);

impl fmt::Display for ConstructorDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} ", self.0)?;
        PrintableList(&self.1).fmt(f)?;
        write!(f, ")")
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum DatatypeDeclaration {
    Simple(Vec<ConstructorDeclaration>),
    Parametric(Vec<Symbol>, Vec<ConstructorDeclaration>),
}

impl fmt::Display for DatatypeDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Simple(constructors) => {
                write!(f, "({})", PrintableList(constructors))
            }
            Self::Parametric(syms, constructors) => {
                write!(
                    f,
                    "(par ({}) ({}))",
                    PrintableList(syms),
                    PrintableList(constructors)
                )
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionDeclaration(pub Symbol, pub Vec<SortedVar>, pub Sort);

impl fmt::Display for FunctionDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} (", self.0)?;
        PrintableList(&self.1).fmt(f)?;
        write!(f, ") {})", self.2)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionDefinition(pub Symbol, pub Vec<SortedVar>, pub Sort, pub Term);

impl fmt::Display for FunctionDefinition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (", self.0)?;
        PrintableList(&self.1).fmt(f)?;
        write!(f, ") {} {}", self.2, self.3)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PropLiteral {
    Pos(Symbol),
    Neg(Symbol),
}

impl fmt::Display for PropLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use PropLiteral::*;
        match self {
            Pos(t) => t.fmt(f),
            Neg(t) => write!(f, "(not {})", t),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum InfoFlag {
    AllStatistics,
    AssertionStackLevels,
    Authors,
    ErrorBehavior,
    Name,
    ReasonUnknown,
    Version,
    Other(Keyword),
}

impl fmt::Display for InfoFlag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use InfoFlag::*;
        match self {
            AllStatistics => write!(f, ":all-statistics"),
            AssertionStackLevels => write!(f, ":assertion-stack-levels"),
            Authors => write!(f, ":authors"),
            ErrorBehavior => write!(f, ":error-behaviour"),
            Name => write!(f, ":name"),
            ReasonUnknown => write!(f, ":reason-unknown"),
            Version => write!(f, ":version"),
            Other(k) => k.fmt(f),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BooleanValue {
    True,
    False,
}

impl fmt::Display for BooleanValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BooleanValue::*;
        match self {
            True => write!(f, "true"),
            False => write!(f, "false"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SMTOption {
    DiagnosticOutputChannel(StringLiteral),
    GlobalDeclarations(BooleanValue),
    InteractiveMode(BooleanValue),
    PrintSuccess(BooleanValue),
    ProduceAssertions(BooleanValue),
    ProduceAssignments(BooleanValue),
    ProduceModels(BooleanValue),
    ProduceProofs(BooleanValue),
    ProduceUnsatAssumptions(BooleanValue),
    ProduceUnsatCores(BooleanValue),
    RandomSeed(Numeral),
    RegularOutputChannel(StringLiteral),
    ReproducibleResourceLimit(Numeral),
    Verbosity(Numeral),
    Other(Attribute),
}

impl fmt::Display for SMTOption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SMTOption::*;
        match self {
            DiagnosticOutputChannel(s) => write!(f, ":diagnostic-output-channel {}", s),
            GlobalDeclarations(b) => write!(f, ":global-declarations {}", b),
            InteractiveMode(b) => write!(f, ":interactive-mode {}", b),
            PrintSuccess(b) => write!(f, ":print-success {}", b),
            ProduceAssertions(b) => write!(f, ":produce-assertions {}", b),
            ProduceAssignments(b) => write!(f, ":produce-assignments {}", b),
            ProduceModels(b) => write!(f, ":produce-models {}", b),
            ProduceProofs(b) => write!(f, ":produce-proofs {}", b),
            ProduceUnsatAssumptions(b) => write!(f, ":produce-unsat-assumptions {}", b),
            ProduceUnsatCores(b) => write!(f, ":produce-unsat-cores {}", b),
            RandomSeed(n) => write!(f, ":random-seed {}", n),
            RegularOutputChannel(s) => write!(f, ":regular-output-channel {}", s),
            ReproducibleResourceLimit(n) => write!(f, ":reproducible-resource-limit {}", n),
            Verbosity(n) => write!(f, ":verbosity {}", n),
            Other(a) => write!(f, "{}", a),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MemoryCell {
    Term(Term),
    HexBytes(StringLiteral),
}

impl fmt::Display for MemoryCell {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use MemoryCell::*;
        match self {
            Term(t) => t.fmt(f),
            HexBytes(s) => s.fmt(f),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Command {
    Assert(Term),
    CheckSat,
    CheckSatAssuming(Vec<PropLiteral>),
    DeclareConst(Symbol, Sort),
    DeclareDatatype(Symbol, DatatypeDeclaration),
    DefineCType(Symbol, Sort),
    DeclareDatatypes(Vec<SortDeclaration>, Vec<DatatypeDeclaration>),
    DeclareFun(Symbol, Vec<Sort>, Sort),
    DeclareCB(Symbol, Vec<Symbol>, Symbol),
    DeclareSort(Symbol, Numeral),
    DefineFun(FunctionDefinition),
    DefineFunRec(FunctionDefinition),
    DefineFunsRec(Vec<FunctionDeclaration>, Vec<Term>),
    DefineSort(Symbol, Vec<Symbol>, Sort),
    Echo(StringLiteral),
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo(InfoFlag),
    GetModel,
    GetOption(Keyword),
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue(Vec<Term>),
    Pop(Numeral),
    Push(Numeral),
    Reset,
    ResetAssertions,
    SetInfo(Attribute),
    SetLogic(Symbol),
    SetOption(SMTOption),
    SetArch(Symbol),
    Alloc(Hexadecimal, Numeral, MemoryCell),
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Command::*;
        match self {
            Assert(term) => write!(f, "(assert {})", term),
            CheckSat => write!(f, "(check-sat)"),
            CheckSatAssuming(props) => {
                write!(f, "(check-sat-assuming (")?;
                PrintableList(props).fmt(f)?;
                write!(f, "))")
            }
            DeclareConst(sym, sort) => write!(f, "(declare-const {} {})", sym, sort),
            DeclareDatatype(sym, decl) => write!(f, "(declare-datatype {} {})", sym, decl),
            DefineCType(ctype, sort) => write!(f, "(define-ctype {} {})", ctype, sort),
            DeclareDatatypes(sort_decls, decls) => {
                write!(f, "(declare-datatypes (")?;
                PrintableList(sort_decls).fmt(f)?;
                write!(f, ") (")?;
                PrintableList(decls).fmt(f)?;
                write!(f, "))")
            }
            DeclareFun(sym, sorts, sort) => {
                write!(f, "(declare-fun {} (", sym)?;
                PrintableList(sorts).fmt(f)?;
                write!(f, ") {})", sort)
            }
            DeclareCB(sym, sorts, sort) => {
                write!(f, "(declare-cb {} (", sym)?;
                PrintableList(sorts).fmt(f)?;
                write!(f, ") {})", sort)
            }
            DeclareSort(sym, n) => write!(f, "(declare-sort {} {})", sym, n),
            DefineFun(def) => write!(f, "(define-fun {})", def),
            DefineFunRec(def) => write!(f, "(define-fun-rec {})", def),
            DefineFunsRec(defs, terms) => {
                write!(f, "(define-funs-rec (")?;
                PrintableList(defs).fmt(f)?;
                write!(f, ") (")?;
                PrintableList(terms).fmt(f)?;
                write!(f, "))")
            }
            DefineSort(sym, params, sort) => {
                write!(f, "(define-sort {} (", sym)?;
                PrintableList(params).fmt(f)?;
                write!(f, ") {})", sort)
            }
            Echo(s) => write!(f, "(echo {})", s),
            Exit => write!(f, "(exit)"),
            GetAssertions => write!(f, "(get-assertions)"),
            GetAssignment => write!(f, "(get-assignment)"),
            GetInfo(flag) => write!(f, "(get-info {})", flag),
            GetModel => write!(f, "(get-model)"),
            GetOption(_) => write!(f, "(get-option)"),
            GetProof => write!(f, "(get-proof)"),
            GetUnsatAssumptions => write!(f, "(get-unsat-assumptions)"),
            GetUnsatCore => write!(f, "(get-unsat-core)"),
            GetValue(_) => write!(f, "(get-value)"),
            Pop(n) => write!(f, "(pop {})", n),
            Push(n) => write!(f, "(push {})", n),
            Reset => write!(f, "(reset)"),
            ResetAssertions => write!(f, "(reset-assertions)"),
            SetInfo(info) => write!(f, "(set-info {})", info),
            SetLogic(logic) => write!(f, "(set-logic {})", logic),
            SetOption(opt) => write!(f, "(set-option {})", opt),
            SetArch(arch) => write!(f, "(set-arch {})", arch),
            Alloc(addr, size, value) => write!(f, "(alloc {} {} {})", addr, size, value),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SMTScript(pub Vec<Command>);

impl fmt::Display for SMTScript {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for cmd in &self.0 {
            writeln!(f, "{}", cmd)?;
        }
        Ok(())
    }
}
