use crate::hir::{
    Attribute, AttributeValue, Binary, BooleanValue, Command, ConstructorDeclaration,
    DatatypeDeclaration, Decimal, FunctionDeclaration, FunctionDefinition, Hexadecimal, Identifier,
    Index, InfoFlag, Keyword, MatchCase, MemoryCell, Numeral, Pattern, PropLiteral, QualIdentifier,
    Reserved, SExpr, SMTOption, SMTScript, SelectorDeclaration, Sort, SortDeclaration, SortedVar,
    SpecConstant, StringLiteral, Symbol, Term, Token, VarBinding,
};
use combine::easy::{Errors, Stream as EasyStream};

use combine::parser::function::parser as fparser; // `fparser` is a parser from a non-recursive function.

use combine::stream::PointerOffset;

// `f2parser` makes a (maybe) recursive function a parser.
use combine::{
    attempt, choice, eof, many, many1, parser as f2parser, satisfy, satisfy_map, EasyParser,
    Parser, StdParseResult,
};

use super::{lex, SMTParserError};

type InputType<'a> = EasyStream<&'a [Token]>;

fn numeral<'a>() -> impl Parser<InputType<'a>, Output = Numeral> {
    satisfy_map(|token: Token| {
        if let Token::Numeral(n) = token {
            Some(n.clone())
        } else {
            None
        }
    })
}

fn decimal<'a>() -> impl Parser<InputType<'a>, Output = Decimal> {
    satisfy_map(|token: Token| {
        if let Token::Decimal(dec) = token {
            Some(dec.clone())
        } else {
            None
        }
    })
}

fn hexadecimal<'a>() -> impl Parser<InputType<'a>, Output = Hexadecimal> {
    satisfy_map(|token: Token| {
        if let Token::Hexadecimal(hex) = token {
            Some(hex.clone())
        } else {
            None
        }
    })
}

fn binary<'a>() -> impl Parser<InputType<'a>, Output = Binary> {
    satisfy_map(|token: Token| {
        if let Token::Binary(bin) = token {
            Some(bin.clone())
        } else {
            None
        }
    })
}

fn string_literal<'a>() -> impl Parser<InputType<'a>, Output = StringLiteral> {
    satisfy_map(|token: Token| {
        if let Token::StringLiteral(string) = token {
            Some(string.clone())
        } else {
            None
        }
    })
}

fn spec_constant<'a>() -> impl Parser<InputType<'a>, Output = SpecConstant> {
    choice((
        decimal().map(|token| SpecConstant::Decimal(token.clone())),
        numeral().map(|token| SpecConstant::Numeral(token.clone())),
        hexadecimal().map(|token| SpecConstant::Hexadecimal(token.clone())),
        binary().map(|token| SpecConstant::Binary(token.clone())),
        string_literal().map(|token| SpecConstant::StringLiteral(token.clone())),
    ))
}

fn symbol<'a>() -> impl Parser<InputType<'a>, Output = Symbol> {
    satisfy_map(|token: Token| {
        if let Token::Symbol(symbol) = token {
            Some(symbol.clone())
        } else {
            None
        }
    })
}

fn keyword<'a>() -> impl Parser<InputType<'a>, Output = Keyword> {
    satisfy_map(|token: Token| {
        if let Token::Keyword(keyword) = token {
            Some(keyword.clone())
        } else {
            None
        }
    })
}

fn reserved<'a>() -> impl Parser<InputType<'a>, Output = Reserved> {
    satisfy_map(|token: Token| {
        if let Token::Reserved(reserved) = token {
            Some(reserved.clone())
        } else {
            None
        }
    })
}

fn lp<'a>() -> impl Parser<InputType<'a>, Output = Token> {
    satisfy(|token: Token| {
        if let Token::LParen = token {
            true
        } else {
            false
        }
    })
}

fn rp<'a>() -> impl Parser<InputType<'a>, Output = Token> {
    satisfy(|token: Token| {
        if let Token::RParen = token {
            true
        } else {
            false
        }
    })
}

fn underscore<'a>() -> impl Parser<InputType<'a>, Output = Token> {
    satisfy(|token: Token| {
        if let Token::Reserved(Reserved::Underscore) = token {
            true
        } else {
            false
        }
    })
}

fn __s_expr<'a, 'b>(tokens: &'b mut InputType<'a>) -> StdParseResult<SExpr, InputType<'a>> {
    use SExpr::*;
    let mut choice = choice((
        spec_constant().map(|spec_const| SpecConstant(spec_const.clone())),
        symbol().map(|symbol| Symbol(symbol.clone())),
        keyword().map(|keyword| Keyword(keyword.clone())),
        reserved().map(|reserved| Reserved(reserved.clone())),
        (lp(), many(f2parser(__s_expr)), rp()).map(|(_lp, exprs, _rp)| List(exprs)),
    ));
    choice.parse_stream(tokens).into_result()
}

fn __sort<'a, 'b>(tokens: &'b mut InputType<'a>) -> StdParseResult<Sort, InputType<'a>> {
    use Sort::*;
    let mut choice = choice((
        attempt(identifier().map(|id| Simple(id.clone()))),
        attempt(
            (lp(), identifier(), many1(f2parser(__sort)), rp())
                .map(|(_lp, id, sorts, _rp)| Parametric(id, sorts)),
        ),
    ));
    choice.parse_stream(tokens).into_result()
}

fn index<'a>() -> impl Parser<InputType<'a>, Output = Index> {
    choice((
        numeral().map(|num: Numeral| Index::Numeral(num.clone())),
        symbol().map(|sym: Symbol| Index::Symbol(sym.clone())),
    ))
}

fn identifier<'a>() -> impl Parser<InputType<'a>, Output = Identifier> {
    choice((
        symbol().map(|sym: Symbol| Identifier::Symbol(sym.clone())),
        (lp(), underscore(), symbol(), many1(index()), rp())
            .map(|(_lp, _, sym, indices, _rp)| Identifier::Indexed(sym, indices)),
    ))
}

fn as_<'a>() -> impl Parser<InputType<'a>, Output = Token> {
    satisfy(|token: Token| {
        if let Token::Reserved(Reserved::As) = token {
            true
        } else {
            false
        }
    })
}

fn let_<'a>() -> impl Parser<InputType<'a>, Output = Token> {
    satisfy(|token: Token| {
        if let Token::Reserved(Reserved::Let) = token {
            true
        } else {
            false
        }
    })
}

fn forall<'a>() -> impl Parser<InputType<'a>, Output = Token> {
    satisfy(|token: Token| {
        if let Token::Reserved(Reserved::Forall) = token {
            true
        } else {
            false
        }
    })
}

fn exists<'a>() -> impl Parser<InputType<'a>, Output = Token> {
    satisfy(|token: Token| {
        if let Token::Reserved(Reserved::Exists) = token {
            true
        } else {
            false
        }
    })
}

fn match_<'a>() -> impl Parser<InputType<'a>, Output = Token> {
    satisfy(|token: Token| {
        if let Token::Reserved(Reserved::Match) = token {
            true
        } else {
            false
        }
    })
}

fn exclamation<'a>() -> impl Parser<InputType<'a>, Output = Token> {
    satisfy(|token: Token| {
        if let Token::Reserved(Reserved::Exclamation) = token {
            true
        } else {
            false
        }
    })
}

fn par<'a>() -> impl Parser<InputType<'a>, Output = Token> {
    satisfy(|token: Token| {
        if let Token::Reserved(Reserved::Par) = token {
            true
        } else {
            false
        }
    })
}

fn __attribute_value<'a, 'b>(
    tokens: &'b mut InputType<'a>,
) -> StdParseResult<AttributeValue, InputType<'a>> {
    let mut choice = choice((
        spec_constant().map(|sc| AttributeValue::SpecConstant(sc.clone())),
        symbol().map(|symbol| AttributeValue::Symbol(symbol.clone())),
        (lp(), many(f2parser(__s_expr)), rp()).map(|tuple: (Token, Vec<SExpr>, Token)| {
            let (_lp, s_exprs, _rp) = tuple;
            AttributeValue::SExpr(s_exprs)
        }),
    ));
    choice.parse_stream(tokens).into_result()
}

fn __attribute<'a, 'b>(tokens: &'b mut InputType<'a>) -> StdParseResult<Attribute, InputType<'a>> {
    let mut choice = choice((
        attempt(
            (keyword(), f2parser(__attribute_value))
                .map(|(kw, av)| Attribute::WithValue(kw.clone(), av.clone())),
        ),
        keyword().map(|kw| Attribute::Keyword(kw.clone())),
    ));
    choice.parse_stream(tokens).into_result()
}

fn __sorted_var<'a, 'b>(tokens: &'b mut InputType<'a>) -> StdParseResult<SortedVar, InputType<'a>> {
    let mut tmp =
        (lp(), symbol(), f2parser(__sort), rp()).map(|(_lp, sym, sort, _rp)| SortedVar(sym, sort));
    tmp.parse_stream(tokens).into_result()
}

fn __term<'a, 'b>(tokens: &'b mut InputType<'a>) -> StdParseResult<Term, InputType<'a>> {
    let qual_identifier = || {
        attempt(identifier().map(|identifier| QualIdentifier::Simple(identifier.clone()))).or(
            attempt(
                (lp(), as_(), identifier(), f2parser(__sort), rp())
                    .map(|(_lp, _as, id, sort, _rp)| QualIdentifier::Qualified(id, sort)),
            ),
        )
    };

    let var_binding =
        || (lp(), symbol(), f2parser(__term), rp()).map(|(_lp, sym, t, _rp)| VarBinding(sym, t));

    let pattern = || {
        symbol()
            .map(|sym| Pattern::Simple(sym.clone()))
            .or((lp(), symbol(), many1(symbol()), rp())
                .map(|(_lp, sym, rest, _rp)| Pattern::Constructor(sym, rest)))
    };

    let match_case =
        (lp(), pattern(), f2parser(__term), rp()).map(|(_lp, p, t, _rp)| MatchCase(p, t));

    let mut choice = choice((
        attempt(spec_constant().map(|sc| Term::SpecConstant(sc.clone()))),
        attempt(qual_identifier().map(|qi| Term::QualIdentifier(qi.clone()))),
        attempt((lp(), qual_identifier(), many1(f2parser(__term)), rp())).map(
            |tuple: (Token, QualIdentifier, Vec<Term>, Token)| {
                let (_lp, qi, terms, _rp) = tuple;
                Term::Apply(qi, terms)
            },
        ),
        attempt((
            lp(),
            let_(),
            lp(),
            many1(var_binding()),
            rp(),
            f2parser(__term),
            rp(),
        ))
        .map(|(_lp, _, _, bindings, _, t, _rp)| Term::Let(bindings, Box::new(t.clone()))),
        attempt(
            (
                lp(),
                forall(),
                lp(),
                many1(f2parser(__sorted_var)),
                rp(),
                f2parser(__term),
                rp(),
            )
                .map(|(_lp, _, _, sorted_vars, _, t, _rp)| {
                    Term::Forall(sorted_vars, Box::new(t.clone()))
                }),
        ),
        attempt(
            (
                lp(),
                exists(),
                lp(),
                many1(f2parser(__sorted_var)),
                rp(),
                f2parser(__term),
                rp(),
            )
                .map(|(_lp, _, _, sorted_vars, _, t, _rp)| {
                    Term::Exists(sorted_vars, Box::new(t.clone()))
                }),
        ),
        attempt(
            (
                lp(),
                match_(),
                f2parser(__term),
                lp(),
                many1(match_case),
                rp(),
                rp(),
            )
                .map(|(_lp, _, t, _, cases, _, _rp)| Term::Match(Box::new(t.clone()), cases)),
        ),
        attempt(
            (
                lp(),
                exclamation(),
                f2parser(__term),
                many1(f2parser(__attribute)),
                rp(),
            )
                .map(|(_lp, _, t, attributes, _rp)| {
                    Term::Annotated(Box::new(t.clone()), attributes)
                }),
        ),
    ));
    choice.parse_stream(tokens).into_result()
}

pub fn parse(
    tokens: &[Token],
) -> Result<SMTScript, Errors<Token, &[Token], PointerOffset<[Token]>>> {
    let assert_ = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "assert"
            } else {
                false
            }
        })
    };

    let check_sat = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "check-sat"
            } else {
                false
            }
        })
    };

    let check_sat_assuming = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "check-sat-assuming"
            } else {
                false
            }
        })
    };

    let declare_const = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "declare-const"
            } else {
                false
            }
        })
    };

    let declare_datatype = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "declare-datatype"
            } else {
                false
            }
        })
    };

    let define_ctype = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "define-ctype"
            } else {
                false
            }
        })
    };

    let declare_cb = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "declare-cb"
            } else {
                false
            }
        })
    };

    let declare_datatypes = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "declare-datatypes"
            } else {
                false
            }
        })
    };

    let declare_fun = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "declare-fun"
            } else {
                false
            }
        })
    };

    let declare_sort = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "declare-sort"
            } else {
                false
            }
        })
    };

    let define_fun = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "define-fun"
            } else {
                false
            }
        })
    };

    let define_fun_rec = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "define-fun-rec"
            } else {
                false
            }
        })
    };

    let define_funs_rec = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "define-funs-rec"
            } else {
                false
            }
        })
    };

    let define_sort = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "define-sort"
            } else {
                false
            }
        })
    };

    let echo = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "echo"
            } else {
                false
            }
        })
    };

    let exit = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "exit"
            } else {
                false
            }
        })
    };

    let get_assertions = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "get-assertions"
            } else {
                false
            }
        })
    };

    let get_assignment = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "get-assignment"
            } else {
                false
            }
        })
    };

    let get_info = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "get-info"
            } else {
                false
            }
        })
    };

    let get_model = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "get-model"
            } else {
                false
            }
        })
    };

    let get_option = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "get-option"
            } else {
                false
            }
        })
    };

    let get_proof = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "get-proof"
            } else {
                false
            }
        })
    };

    let get_unsat_core = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "get-unsat-core"
            } else {
                false
            }
        })
    };

    let get_value = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "get-value"
            } else {
                false
            }
        })
    };

    let pop = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "pop"
            } else {
                false
            }
        })
    };

    let push = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "push"
            } else {
                false
            }
        })
    };

    let reset_assertions = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "reset-assertions"
            } else {
                false
            }
        })
    };

    let reset = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "reset"
            } else {
                false
            }
        })
    };

    let set_info = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "set-info"
            } else {
                false
            }
        })
    };

    let set_logic = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "set-logic"
            } else {
                false
            }
        })
    };

    let set_option = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "set-option"
            } else {
                false
            }
        })
    };

    let set_arch = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "set-arch"
            } else {
                false
            }
        })
    };

    let alloc = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "alloc"
            } else {
                false
            }
        })
    };

    let get_unsat_assumptions = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "get-unsat-assumptions"
            } else {
                false
            }
        })
    };

    let not = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s.starts_with("not")
            } else {
                false
            }
        })
    };
    let sort_dec =
        || (lp(), symbol(), numeral(), rp()).map(|(_lp, sym, num, _rp)| SortDeclaration(sym, num));
    let selector_dec = || {
        (lp(), symbol(), f2parser(__sort), rp())
            .map(|(_lp, sym, sort, _rp)| SelectorDeclaration(sym, sort))
    };
    let constructor_dec = || {
        (lp(), symbol(), many(selector_dec()), rp())
            .map(|(_lp, sym, selectors, _rp)| ConstructorDeclaration(sym, selectors))
    };
    let datatype_dec = || {
        attempt(
            (lp(), many1(constructor_dec()), rp())
                .map(|(_lp, ctors, _rp)| DatatypeDeclaration::Simple(ctors)),
        )
        .or(attempt(
            (
                lp(),
                par(),
                lp(),
                many1(symbol()),
                rp(),
                lp(),
                many1(constructor_dec()),
                rp(),
                rp(),
            )
                .map(|(_, _, _, syms, _, _, ctors, _, _)| {
                    DatatypeDeclaration::Parametric(syms, ctors)
                }),
        ))
    };
    let function_dec = || {
        (
            lp(),
            symbol(),
            lp(),
            many(f2parser(__sorted_var)),
            rp(),
            f2parser(__sort),
            rp(),
        )
            .map(|(_, sym, _, sorted_vars, _, return_sort, _)| {
                FunctionDeclaration(sym, sorted_vars, return_sort)
            })
    };
    let function_def = || {
        (
            symbol(),
            lp(),
            many(f2parser(__sorted_var)),
            rp(),
            f2parser(__sort),
            f2parser(__term),
        )
            .map(|(name, _, params, _, return_sort, body)| {
                FunctionDefinition(name.clone(), params, return_sort, body.clone())
            })
    };
    let prop_literal =
        symbol()
            .map(|sym| PropLiteral::Pos(sym.clone()))
            .or((lp(), not(), symbol(), rp()).map(|(_lp, _, sym, _rp)| PropLiteral::Neg(sym)));

    let true_ = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "true"
            } else {
                false
            }
        })
    };

    let false_ = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Symbol(Symbol::Simple(s)) = token {
                s == "false"
            } else {
                false
            }
        })
    };

    let bvalue = || {
        true_()
            .map(|_t: Token| BooleanValue::True)
            .or(false_().map(|_t: Token| BooleanValue::False))
    };

    let diagnostic_output_channel_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "diagnostic-output-channel"
            } else {
                false
            }
        })
    };

    let global_declarations_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "global-declarations"
            } else {
                false
            }
        })
    };

    let interactive_mode_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "interactive-mode"
            } else {
                false
            }
        })
    };

    let produce_assignments_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "produce-assignments"
            } else {
                false
            }
        })
    };

    let produce_models_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "produce-models"
            } else {
                false
            }
        })
    };

    let print_success_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "print-success"
            } else {
                false
            }
        })
    };

    let produce_assertions_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "produce-assertions"
            } else {
                false
            }
        })
    };

    let produce_proofs_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "produce-proofs"
            } else {
                false
            }
        })
    };

    let produce_unsat_assumptions_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "produce-unsat-assumptions"
            } else {
                false
            }
        })
    };

    let produce_unsat_cores_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "produce-unsat-cores"
            } else {
                false
            }
        })
    };

    let random_seed_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "random-seed"
            } else {
                false
            }
        })
    };

    let regular_output_channel_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "regular-output-channel"
            } else {
                false
            }
        })
    };

    let reproducible_resource_limit_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "reproducible-resource-limit"
            } else {
                false
            }
        })
    };

    let verbosity_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "verbosity"
            } else {
                false
            }
        })
    };

    let option = || {
        choice((
            (diagnostic_output_channel_keyword(), string_literal())
                .map(|(_kw, string)| SMTOption::DiagnosticOutputChannel(string.clone())),
            (global_declarations_keyword(), bvalue())
                .map(|(_kw, b)| SMTOption::GlobalDeclarations(b.clone())),
            (interactive_mode_keyword(), bvalue())
                .map(|(_kw, b)| SMTOption::InteractiveMode(b.clone())),
            (print_success_keyword(), bvalue()).map(|(_kw, b)| SMTOption::PrintSuccess(b.clone())),
            (produce_assertions_keyword(), bvalue())
                .map(|(_kw, b)| SMTOption::ProduceAssertions(b.clone())),
            (produce_assignments_keyword(), bvalue())
                .map(|(_kw, b)| SMTOption::ProduceAssignments(b.clone())),
            (produce_models_keyword(), bvalue())
                .map(|(_kw, b)| SMTOption::ProduceModels(b.clone())),
            (produce_proofs_keyword(), bvalue())
                .map(|(_kw, b)| SMTOption::ProduceProofs(b.clone())),
            (produce_unsat_assumptions_keyword(), bvalue())
                .map(|(_kw, b)| SMTOption::ProduceUnsatAssumptions(b.clone())),
            (produce_unsat_cores_keyword(), bvalue())
                .map(|(_kw, b)| SMTOption::ProduceUnsatCores(b.clone())),
            (random_seed_keyword(), numeral()).map(|(_kw, num)| SMTOption::RandomSeed(num.clone())),
            (regular_output_channel_keyword(), string_literal())
                .map(|(_kw, string)| SMTOption::RegularOutputChannel(string.clone())),
            (reproducible_resource_limit_keyword(), numeral())
                .map(|(_kw, n)| SMTOption::ReproducibleResourceLimit(n.clone())),
            (verbosity_keyword(), numeral()).map(|(_kw, num)| SMTOption::Verbosity(num.clone())),
            f2parser(__attribute).map(|attr| SMTOption::Other(attr.clone())),
        ))
    };

    let all_statistics_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "all-statistics"
            } else {
                false
            }
        })
    };

    let assertion_stack_levels_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "assertion-stack-levels"
            } else {
                false
            }
        })
    };

    let authors_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "authors"
            } else {
                false
            }
        })
    };

    let error_behavior_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "error-behavior"
            } else {
                false
            }
        })
    };

    let name_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "name"
            } else {
                false
            }
        })
    };

    let reason_unknown_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "reason-unknown"
            } else {
                false
            }
        })
    };

    let version_keyword = || {
        satisfy::<InputType, _>(|token: Token| {
            if let Token::Keyword(Keyword(s)) = token {
                s == "version"
            } else {
                false
            }
        })
    };

    let info_flag = choice((
        all_statistics_keyword().map(|_kw| InfoFlag::AllStatistics),
        assertion_stack_levels_keyword().map(|_kw| InfoFlag::AssertionStackLevels),
        authors_keyword().map(|_kw| InfoFlag::Authors),
        error_behavior_keyword().map(|_kw| InfoFlag::ErrorBehavior),
        name_keyword().map(|_kw| InfoFlag::Name),
        reason_unknown_keyword().map(|_kw| InfoFlag::ReasonUnknown),
        version_keyword().map(|_kw| InfoFlag::Version),
        keyword().map(|kw| InfoFlag::Other(kw.clone())),
    ));

    let declare_datatypes_guard = fparser(|input: &mut InputType| {
        declare_datatypes().parse_stream(input).into_result()?;
        lp().parse_stream(input).into_result()?;
        let sort_decs: Vec<SortDeclaration> =
            many1(sort_dec()).parse_stream(input).into_result()?.0;
        rp().parse_stream(input).into_result()?;
        lp().parse_stream(input).into_result()?;
        let dt_decls: Vec<DatatypeDeclaration> =
            many1(datatype_dec()).parse_stream(input).into_result()?.0;
        let (_, commit) = rp().parse_stream(input).into_result()?;
        assert!(sort_decs.len() >= 2);
        assert!(dt_decls.len() >= 2);
        assert_eq!(sort_decs.len(), dt_decls.len());
        // let (_, commit) = rp().parse_stream(input).into_result()?;
        Ok(((sort_decs, dt_decls), commit))
    });

    let define_funs_rec_guard = fparser(|input: &mut InputType| {
        define_funs_rec().parse_stream(input).into_result()?;
        lp().parse_stream(input).into_result()?;
        let fun_decs: Vec<FunctionDeclaration> =
            many1(function_dec()).parse_stream(input).into_result()?.0;
        rp().parse_stream(input).into_result()?;
        lp().parse_stream(input).into_result()?;
        let bodies: Vec<Term> = many1(f2parser(__term)).parse_stream(input).into_result()?.0;
        assert!(fun_decs.len() >= 2);
        println!("{:?}", input);
        assert!(bodies.len() >= 2);
        assert_eq!(fun_decs.len(), bodies.len());
        let (_, commit) = rp().parse_stream(input).into_result()?;
        Ok(((fun_decs, bodies), commit))
    });

    // XXX: All `attempt` in the outermost level makes the error info quite meaningless. It simply reports that all of the choice failed.
    //  We should refine this.
    let command = choice((
        attempt((lp(), assert_(), f2parser(__term), rp()).map(|(_, _, t, _)| Command::Assert(t))),
        attempt((lp(), check_sat(), rp()).map(|(_, _, _)| Command::CheckSat)),
        attempt(
            (lp(), check_sat_assuming(), many(prop_literal), rp())
                .map(|(_, _, props, _)| Command::CheckSatAssuming(props)),
        ),
        attempt(
            (lp(), declare_const(), symbol(), f2parser(__sort), rp())
                .map(|(_, _, sym, sort, _)| Command::DeclareConst(sym, sort)),
        ),
        attempt(
            (lp(), declare_datatype(), symbol(), datatype_dec(), rp())
                .map(|(_, _, sym, dec, _)| Command::DeclareDatatype(sym, dec)),
        ),
        attempt(
            (lp(), define_ctype(), symbol(), f2parser(__sort), rp())
                .map(|(_, _, ctype, sort, _)| Command::DefineCType(ctype, sort)),
        ),
        attempt(
            (
                lp(),
                declare_cb(),
                symbol(),
                lp(),
                many(symbol()),
                rp(),
                symbol(),
                rp(),
            )
                .map(|(_, _, sym, _, param_type, _, return_type, _)| {
                    Command::DeclareCB(sym, param_type, return_type)
                }),
        ),
        attempt(
            (lp(), declare_datatypes_guard, rp())
                .map(|(_, (s, d), _)| Command::DeclareDatatypes(s, d)),
        ),
        attempt(
            (
                lp(),
                declare_fun(),
                symbol(),
                lp(),
                many(f2parser(__sort)),
                rp(),
                f2parser(__sort),
                rp(),
            )
                .map(|(_, _, sym, _, sorts, _, sort, _)| Command::DeclareFun(sym, sorts, sort)),
        ),
        attempt(
            (lp(), declare_sort(), symbol(), numeral(), rp())
                .map(|(_, _, sym, num, _)| Command::DeclareSort(sym, num)),
        ),
        attempt((lp(), set_arch(), symbol(), rp()).map(|(_, _, sym, _)| Command::SetArch(sym))),
        attempt(
            (
                lp(),
                alloc(),
                hexadecimal(),
                numeral(),
                string_literal()
                    .map(|s| MemoryCell::HexBytes(s))
                    .or(f2parser(__term).map(|t| MemoryCell::Term(t))),
                rp(),
            )
                .map(|(_, _, hex, num, t, _)| Command::Alloc(hex, num, t)),
        ),
    ))
    .or(choice((
        // Must split since the number overflows capacity of the type checker.
        attempt(
            (lp(), define_fun(), function_def(), rp())
                .map(|(_, _, def, _)| Command::DefineFun(def)),
        ),
        attempt(
            (lp(), define_fun_rec(), function_def(), rp())
                .map(|(_, _, def, _)| Command::DefineFunRec(def)),
        ),
        attempt(
            (lp(), define_funs_rec_guard, rp())
                .map(|(_, (dcs, ts), _)| Command::DefineFunsRec(dcs, ts)),
        ),
        attempt(
            (
                lp(),
                define_sort(),
                symbol(),
                lp(),
                many(symbol()),
                rp(),
                f2parser(__sort),
                rp(),
            )
                .map(|(_, _, sym, _, syms, _, sort, _)| Command::DefineSort(sym, syms, sort)),
        ),
        attempt(
            (lp(), echo(), string_literal(), rp()).map(|(_, _, string, _)| Command::Echo(string)),
        ),
        attempt((lp(), exit(), rp()).map(|(_, _, _)| Command::Exit)),
        attempt((lp(), exit(), rp()).map(|(_, _, _)| Command::Exit)),
        attempt((lp(), get_assertions(), rp()).map(|(_, _, _)| Command::GetAssertions)),
        attempt((lp(), get_assignment(), rp()).map(|(_, _, _)| Command::GetAssignment)),
        attempt((lp(), get_info(), info_flag, rp()).map(|(_, _, flag, _)| Command::GetInfo(flag))),
        attempt((lp(), get_model(), rp()).map(|(_, _, _)| Command::GetModel)),
        attempt((lp(), get_option(), keyword(), rp()).map(|(_, _, kw, _)| Command::GetOption(kw))),
        attempt((lp(), get_proof(), rp()).map(|(_, _, _)| Command::GetProof)),
        attempt(
            (lp(), get_unsat_assumptions(), rp()).map(|(_, _, _)| Command::GetUnsatAssumptions),
        ),
        attempt((lp(), get_unsat_core(), rp()).map(|(_, _, _)| Command::GetUnsatCore)),
        attempt(
            (lp(), get_value(), lp(), many1(f2parser(__term)), rp(), rp())
                .map(|(_, _, _, t, _, _)| Command::GetValue(t)),
        ),
        attempt((lp(), pop(), numeral(), rp()).map(|(_, _, num, _)| Command::Pop(num))),
        attempt((lp(), push(), numeral(), rp()).map(|(_, _, num, _)| Command::Push(num))),
        attempt((lp(), reset_assertions(), rp()).map(|(_, _, _)| Command::ResetAssertions)),
        attempt((lp(), reset(), rp()).map(|(_, _, _)| Command::Reset)),
        attempt(
            (lp(), set_info(), f2parser(__attribute), rp())
                .map(|(_, _, attr, _)| Command::SetInfo(attr)),
        ),
        attempt((lp(), set_logic(), symbol(), rp()).map(|(_, _, sym, _)| Command::SetLogic(sym))),
        (lp(), set_option(), option(), rp()).map(|(_, _, opt, _)| Command::SetOption(opt)),
    )));

    let mut commands = many(command).skip(eof());
    let (parsed, _): (Vec<Command>, _) = commands.easy_parse(tokens)?;

    Ok(SMTScript(parsed))
}

impl<'a, 'b> From<Errors<Token, &'b [Token], PointerOffset<[Token]>>> for SMTParserError<'a> {
    fn from(value: Errors<Token, &'b [Token], PointerOffset<[Token]>>) -> Self {
        let value = value.map_range(|range| range.to_vec());
        SMTParserError::ParseError(value)
    }
}

pub fn parse_str<'a>(text: &'a str) -> Result<SMTScript, SMTParserError<'a>> {
    let tokens = lex(text)?;
    let parsed = parse(&tokens)?;
    Ok(parsed)
}

#[cfg(test)]
mod test {
    use super::*;
    use trim_margin::MarginTrimmable;

    #[test]
    fn test_assert0_command() {
        let program = parse_str("(assert \"true\")").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        let cmd = &commands[0];
        if let Command::Assert(term) = cmd {
            match term {
                Term::SpecConstant(spec_constant) => match spec_constant {
                    SpecConstant::StringLiteral(lit) => {
                        let StringLiteral(s) = lit;
                        assert_eq!("true", s);
                    }
                    _ => assert!(false),
                },
                _ => assert!(false),
            }
        } else {
            assert!(false)
        }
    }

    #[test]
    fn test_check_sat_command() {
        let program = parse_str("(check-sat)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        assert!(if let Command::CheckSat = commands[0] {
            true
        } else {
            false
        });
    }

    #[test]
    fn test_assert_command() {
        let program = parse_str(r#"(assert (< x y))"#).unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        let cmd = &commands[0];
        if let Command::Assert(term) = cmd {
            match term {
                Term::Apply(func, args) => {
                    match func {
                        QualIdentifier::Simple(id) => match id {
                            Identifier::Symbol(sym) => match sym {
                                Symbol::Simple(name) => {
                                    assert_eq!("<", name)
                                }
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    }
                    assert_eq!(2, args.len());

                    match &args[0] {
                        Term::QualIdentifier(qual_identifier) => match qual_identifier {
                            QualIdentifier::Simple(id) => match id {
                                Identifier::Symbol(sym) => match sym {
                                    Symbol::Simple(name) => {
                                        assert_eq!("x", name)
                                    }
                                    _ => assert!(false),
                                },
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    }

                    match &args[1] {
                        Term::QualIdentifier(qual_identifier) => match qual_identifier {
                            QualIdentifier::Simple(id) => match id {
                                Identifier::Symbol(sym) => match sym {
                                    Symbol::Simple(name) => {
                                        assert_eq!("y", name)
                                    }
                                    _ => assert!(false),
                                },
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    }
                }
                _ => assert!(false),
            }
        } else {
            assert!(false)
        }
    }

    #[test]

    fn test_check_sat_assuming_command() {
        let program = parse_str("(check-sat-assuming x (not y))").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());

        match &commands[0] {
            Command::CheckSatAssuming(prop_lits) => {
                assert_eq!(2, prop_lits.len());
                match &prop_lits[0] {
                    PropLiteral::Pos(term) => match term {
                        Symbol::Simple(sym) => assert_eq!("x", sym),
                        _ => assert!(false),
                    },
                    PropLiteral::Neg(term) => match term {
                        Symbol::Simple(sym) => assert_eq!("y", sym),
                        _ => assert!(false),
                    },
                }
            }
            _ => assert!(true),
        }
    }

    #[test]
    fn test_declare_const_command() {
        let program = parse_str("(declare-const x (Int t))").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());

        match &commands[0] {
            Command::DeclareConst(symbol, sort) => {
                match symbol {
                    Symbol::Simple(name) => assert_eq!("x", name),
                    _ => assert!(false),
                }
                match sort {
                    Sort::Parametric(sym, args) => {
                        match sym {
                            Identifier::Symbol(sym) => match sym {
                                Symbol::Simple(name) => assert_eq!("Int", name),
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        }
                        assert_eq!(1, args.len());
                        match &args[0] {
                            Sort::Simple(id) => match id {
                                Identifier::Symbol(sym) => match sym {
                                    Symbol::Simple(name) => assert_eq!("t", name),
                                    _ => assert!(false),
                                },
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        }
                    }
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_declare_datatype_command() {
        let program = parse_str("(declare-datatype T ((T (x Int))) )").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::DeclareDatatype(sym, decl) => {
                match sym {
                    Symbol::Simple(name) => assert_eq!("T", name),
                    _ => assert!(false),
                }

                match decl {
                    DatatypeDeclaration::Simple(ctors) => {
                        assert_eq!(1, ctors.len());
                        let ConstructorDeclaration(sym, fields) = &ctors[0];
                        match sym {
                            Symbol::Simple(name) => assert_eq!("T", name),
                            _ => assert!(false),
                        }
                        assert_eq!(1, fields.len());
                        let SelectorDeclaration(sym, sort) = &fields[0];

                        match sym {
                            Symbol::Simple(name) => assert_eq!("x", name),
                            _ => assert!(false),
                        }

                        match sort {
                            Sort::Simple(id) => match id {
                                Identifier::Symbol(sym) => match sym {
                                    Symbol::Simple(name) => assert_eq!("Int", name),
                                    _ => assert!(false),
                                },
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        }
                    }
                    _ => assert!(false),
                }
            }

            _ => assert!(false),
        }
    }

    #[test]
    fn test_declare_sort_command() {
        let program = parse_str("(declare-sort |Product ID| 33)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::DeclareSort(sort_name, num) => {
                match sort_name {
                    Symbol::Quoted(name) => assert_eq!("Product ID", name),
                    _ => assert!(false),
                }
                let Numeral(n) = num;
                assert_eq!(33, *n);
            }
            _ => assert!(false),
        }
    }

    #[test]

    fn test_declare_fun_command() {
        let program = parse_str("(declare-fun abs (Int) Int)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::DeclareFun(sym, args, sort) => {
                match sym {
                    Symbol::Simple(name) => assert_eq!("abs", name),
                    _ => assert!(false),
                }
                assert_eq!(1, args.len());

                match &args[0] {
                    Sort::Simple(id) => match id {
                        Identifier::Symbol(sym) => match sym {
                            Symbol::Simple(name) => assert_eq!("Int", name),
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }

                match sort {
                    Sort::Simple(id) => match id {
                        Identifier::Symbol(sym) => match sym {
                            Symbol::Simple(name) => assert_eq!("Int", name),
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_declare_datatypes_command() {
        let program = parse_str(
            &r#"
            |(declare-datatypes ((A 1) (B 2)) 
            |    (((A (a Int)))
            |     (par (T) ((B (b T))))
            |    )
            |)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();

        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());

        match &commands[0] {
            Command::DeclareDatatypes(sorts, decls) => {
                assert_eq!(2, sorts.len());
                assert_eq!(2, decls.len());

                let SortDeclaration(sym, num) = &sorts[0];
                match sym {
                    Symbol::Simple(name) => assert_eq!("A", name),
                    _ => assert!(false),
                }

                let Numeral(n) = num;
                assert_eq!(1, *n);
                let SortDeclaration(sym, num) = &sorts[1];

                match sym {
                    Symbol::Simple(name) => assert_eq!("B", name),
                    _ => assert!(false),
                }

                let Numeral(n) = num;
                assert_eq!(2, *n);

                match &decls[0] {
                    DatatypeDeclaration::Simple(ctors) => {
                        assert_eq!(1, ctors.len());
                        let ConstructorDeclaration(sym, selector) = &ctors[0];
                        match sym {
                            Symbol::Simple(name) => assert_eq!("A", name),
                            _ => assert!(false),
                        }
                        assert_eq!(1, selector.len());

                        let SelectorDeclaration(sym, sort) = &selector[0];
                        match sym {
                            Symbol::Simple(name) => assert_eq!("a", name),
                            _ => assert!(false),
                        }

                        match sort {
                            Sort::Simple(id) => match id {
                                Identifier::Symbol(sym) => match sym {
                                    Symbol::Simple(name) => assert_eq!("Int", name),
                                    _ => assert!(false),
                                },
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        }
                    }
                    _ => assert!(false),
                }

                match &decls[1] {
                    DatatypeDeclaration::Parametric(syms, ctors) => {
                        assert_eq!(1, syms.len());

                        match &syms[0] {
                            Symbol::Simple(name) => assert_eq!("T", name),
                            _ => assert!(false),
                        }

                        assert_eq!(1, ctors.len());
                        let ConstructorDeclaration(sym, selectors) = &ctors[0];
                        match sym {
                            Symbol::Simple(name) => assert_eq!("B", name),
                            _ => assert!(false),
                        }

                        assert_eq!(1, selectors.len());

                        let SelectorDeclaration(sym, sort) = &selectors[0];
                        match sym {
                            Symbol::Simple(name) => assert_eq!("b", name),
                            _ => assert!(false),
                        }

                        match sort {
                            Sort::Simple(id) => match id {
                                Identifier::Symbol(sym) => match sym {
                                    Symbol::Simple(name) => assert_eq!("T", name),
                                    _ => assert!(false),
                                },
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        }
                    }
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_define_fun_command() {
        let program = parse_str(
            &r#"
            |(define-fun abs ((num (_ Int 33))) Int
            | num
            |)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();

        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());

        match &commands[0] {
            Command::DefineFun(def) => {
                let FunctionDefinition(sym, params, return_sort, body) = def;
                match sym {
                    Symbol::Simple(name) => assert_eq!("abs", name),
                    _ => assert!(false),
                }

                assert_eq!(1, params.len());

                let SortedVar(sym, sort) = &params[0];
                match sym {
                    Symbol::Simple(name) => assert_eq!("num", name),
                    _ => assert!(false),
                }

                match sort {
                    Sort::Simple(id) => match id {
                        Identifier::Indexed(id, indices) => {
                            match id {
                                Symbol::Simple(name) => assert_eq!("Int", name),
                                _ => assert!(false),
                            }

                            assert_eq!(1, indices.len());
                            match &indices[0] {
                                Index::Numeral(num) => {
                                    let Numeral(num) = num;
                                    assert_eq!(33, *num);
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }

                match return_sort {
                    Sort::Simple(id) => match id {
                        Identifier::Symbol(sym) => match sym {
                            Symbol::Simple(name) => assert_eq!("Int", name),
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }

                match body {
                    Term::QualIdentifier(qid) => match qid {
                        QualIdentifier::Simple(id) => match id {
                            Identifier::Symbol(sym) => match sym {
                                Symbol::Simple(name) => assert_eq!("num", name),
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_define_ctype_command() {
        let program = parse_str("(define-ctype int Int)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::DefineCType(ctype, sort) => {
                match ctype {
                    Symbol::Simple(name) => assert_eq!("int", name),
                    _ => assert!(false),
                }

                match sort {
                    Sort::Simple(id) => match id {
                        Identifier::Symbol(sym) => match sym {
                            Symbol::Simple(name) => assert_eq!("Int", name),
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_declare_cb_command() {
        let program = parse_str("(declare-cb abs (int int) int)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());

        match &commands[0] {
            Command::DeclareCB(sym, param_types, return_type) => {
                match sym {
                    Symbol::Simple(name) => assert_eq!("abs", name),
                    _ => assert!(false),
                }

                assert_eq!(2, param_types.len());

                match &param_types[0] {
                    Symbol::Simple(name) => assert_eq!("int", name),
                    _ => assert!(false),
                }

                match &param_types[1] {
                    Symbol::Simple(name) => assert_eq!("int", name),
                    _ => assert!(false),
                }

                match return_type {
                    Symbol::Simple(name) => assert_eq!("int", name),
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_define_fun_rec_command() {
        let program = parse_str(
            &r#"
            |(define-fun-rec abs ((num (_ Int 33))) Int
            | num
            |)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();

        let SMTScript(commands) = program;

        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::DefineFunRec(def) => {
                let FunctionDefinition(sym, params, return_sort, body) = def;
                match sym {
                    Symbol::Simple(name) => assert_eq!("abs", name),
                    _ => assert!(false),
                }
                assert_eq!(1, params.len());

                let SortedVar(sym, sort) = &params[0];
                match sym {
                    Symbol::Simple(name) => assert_eq!("num", name),
                    _ => assert!(false),
                }

                match sort {
                    Sort::Simple(id) => match id {
                        Identifier::Indexed(id, indices) => {
                            match id {
                                Symbol::Simple(name) => assert_eq!("Int", name),
                                _ => assert!(false),
                            }

                            assert_eq!(1, indices.len());
                            match &indices[0] {
                                Index::Numeral(num) => {
                                    let Numeral(num) = num;
                                    assert_eq!(33, *num);
                                }
                                _ => assert!(false),
                            }
                        }
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }

                match return_sort {
                    Sort::Simple(id) => match id {
                        Identifier::Symbol(sym) => match sym {
                            Symbol::Simple(name) => assert_eq!("Int", name),
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }

                match body {
                    Term::QualIdentifier(qid) => match qid {
                        QualIdentifier::Simple(id) => match id {
                            Identifier::Symbol(sym) => match sym {
                                Symbol::Simple(name) => assert_eq!("num", name),
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_define_funs_rec_command() {
        let src = r#"
            |(define-funs-rec ((abs ((num (_ Int 33))) Int) (neg ((a Int)) Int))
            | (num (- (as a Int)))
            |)
        "#
        .trim_margin()
        .unwrap();

        let program = parse_str(&src).unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());

        match &commands[0] {
            Command::DefineFunsRec(dcls, terms) => {
                assert_eq!(2, dcls.len());
                {
                    let FunctionDeclaration(sym, params, return_sort) = &dcls[0];
                    match sym {
                        Symbol::Simple(name) => assert_eq!("abs", name),
                        _ => assert!(false),
                    }

                    assert_eq!(1, params.len());
                    let SortedVar(sym, sort) = &params[0];
                    match sym {
                        Symbol::Simple(name) => assert_eq!("num", name),
                        _ => assert!(false),
                    }

                    match sort {
                        Sort::Simple(id) => match id {
                            Identifier::Indexed(id, indices) => {
                                match id {
                                    Symbol::Simple(name) => assert_eq!("Int", name),
                                    _ => assert!(false),
                                }

                                assert_eq!(1, indices.len());

                                match &indices[0] {
                                    Index::Numeral(num) => {
                                        let Numeral(num) = num;
                                        assert_eq!(33, *num);
                                    }
                                    _ => assert!(false),
                                }
                            }

                            _ => assert!(false),
                        },

                        _ => assert!(false),
                    }

                    match return_sort {
                        Sort::Simple(id) => match id {
                            Identifier::Symbol(sym) => match sym {
                                Symbol::Simple(name) => assert_eq!("Int", name),

                                _ => assert!(false),
                            },

                            _ => assert!(false),
                        },

                        _ => assert!(false),
                    }
                }

                {
                    let FunctionDeclaration(sym, params, return_sort) = &dcls[1];

                    match sym {
                        Symbol::Simple(name) => assert_eq!("neg", name),
                        _ => assert!(false),
                    }

                    assert_eq!(1, params.len());

                    let SortedVar(sym, sort) = &params[0];

                    match sym {
                        Symbol::Simple(name) => assert_eq!("a", name),
                        _ => assert!(false),
                    }

                    match sort {
                        Sort::Simple(id) => match id {
                            Identifier::Symbol(sym) => match sym {
                                Symbol::Simple(name) => assert_eq!("Int", name),
                                _ => assert!(false),
                            },

                            _ => assert!(false),
                        },

                        _ => assert!(false),
                    }

                    match return_sort {
                        Sort::Simple(id) => match id {
                            Identifier::Symbol(sym) => match sym {
                                Symbol::Simple(name) => assert_eq!("Int", name),

                                _ => assert!(false),
                            },

                            _ => assert!(false),
                        },

                        _ => assert!(false),
                    }
                }

                assert_eq!(2, terms.len());

                match &terms[0] {
                    Term::QualIdentifier(qid) => match qid {
                        QualIdentifier::Simple(id) => match id {
                            Identifier::Symbol(sym) => match sym {
                                Symbol::Simple(name) => assert_eq!("num", name),

                                _ => assert!(false),
                            },

                            _ => assert!(false),
                        },

                        _ => assert!(false),
                    },

                    _ => assert!(false),
                }

                match &terms[1] {
                    Term::Apply(func, term) => {
                        match func {
                            QualIdentifier::Simple(id) => match id {
                                Identifier::Symbol(sym) => match sym {
                                    Symbol::Simple(name) => assert_eq!("-", name),
                                    _ => assert!(false),
                                },
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        }
                        assert_eq!(1, term.len());

                        match &term[0] {
                            Term::QualIdentifier(qid) => match qid {
                                QualIdentifier::Qualified(id, sort) => {
                                    match id {
                                        Identifier::Symbol(sym) => match sym {
                                            Symbol::Simple(name) => assert_eq!("a", name),

                                            _ => assert!(false),
                                        },

                                        _ => assert!(false),
                                    }

                                    match sort {
                                        Sort::Simple(id) => match id {
                                            Identifier::Symbol(sym) => match sym {
                                                Symbol::Simple(name) => assert_eq!("Int", name),

                                                _ => assert!(false),
                                            },

                                            _ => assert!(false),
                                        },

                                        _ => assert!(false),
                                    }
                                }

                                _ => assert!(false),
                            },

                            _ => assert!(false),
                        }
                    }

                    _ => assert!(false),
                }
            }

            _ => assert!(false),
        }
    }

    #[test]

    fn test_define_sort() {
        let program = parse_str("(define-sort T (A) R)").unwrap();

        let SMTScript(commands) = program;

        assert_eq!(1, commands.len());

        match &commands[0] {
            Command::DefineSort(sort_name, params, return_sort) => {
                match sort_name {
                    Symbol::Simple(name) => assert_eq!("T", name),

                    _ => assert!(false),
                }

                assert_eq!(1, params.len());

                match &params[0] {
                    Symbol::Simple(name) => assert_eq!("A", name),
                    _ => assert!(false),
                }

                match return_sort {
                    Sort::Simple(id) => match id {
                        Identifier::Symbol(sym) => match sym {
                            Symbol::Simple(name) => assert_eq!("R", name),
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_echo_command() {
        let program = parse_str(r#"(echo "SPY x FAMILY")"#).unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::Echo(string) => {
                let StringLiteral(lit) = string;
                assert_eq!("SPY x FAMILY", lit);
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_exit_command() {
        let program = parse_str("(exit)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match commands[0] {
            Command::Exit => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]

    fn test_get_assertions_command() {
        let program = parse_str("(get-assertions)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::GetAssertions => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_get_assignment_command() {
        let program = parse_str("(get-assignment)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::GetAssignment => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_get_info_command() {
        let program = parse_str("(get-info :name)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::GetInfo(info_flag) => match info_flag {
                InfoFlag::Name => {}
                _ => assert!(false),
            },
            _ => assert!(false),
        }
    }

    #[test]
    fn test_get_model_command() {
        let program = parse_str("(get-model)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::GetModel => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_get_option_command() {
        let program = parse_str("(get-option :print-success)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::GetOption(option) => {
                let Keyword(kw) = option;
                assert_eq!("print-success", kw);
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_get_proof_command() {
        let program = parse_str("(get-proof)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::GetProof => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_get_unsat_assumptions_command() {
        let program = parse_str("(get-unsat-assumptions)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::GetUnsatAssumptions => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_get_unsat_core_command() {
        let program = parse_str("(get-unsat-core)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::GetUnsatCore => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_get_value_command() {
        let program = parse_str("(get-value (num))").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::GetValue(terms) => {
                assert_eq!(1, terms.len());
                match &terms[0] {
                    Term::QualIdentifier(qid) => match qid {
                        QualIdentifier::Simple(id) => match id {
                            Identifier::Symbol(sym) => match sym {
                                Symbol::Simple(name) => assert_eq!("num", name),
                                _ => assert!(false),
                            },
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    },
                    _ => assert!(false),
                }
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_pop_command() {
        let program = parse_str("(pop 1)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::Pop(num) => {
                let Numeral(n) = num;
                assert_eq!(1, *n);
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_push_command() {
        let program = parse_str("(push 1)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::Push(num) => {
                let Numeral(n) = num;
                assert_eq!(1, *n);
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_reset_command() {
        let program = parse_str("(reset)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::Reset => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_reset_assertions_command() {
        let program = parse_str("(reset-assertions)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::ResetAssertions => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_set_info_command() {
        let program = parse_str("(set-info :name \"SPY x FAMILY\")").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::SetInfo(attribute) => match attribute {
                Attribute::WithValue(keyword, value) => {
                    let Keyword(kw) = keyword;
                    assert_eq!("name", kw);
                    match value {
                        AttributeValue::SpecConstant(spec_constant) => match spec_constant {
                            SpecConstant::StringLiteral(lit) => {
                                let StringLiteral(string) = lit;
                                assert_eq!("SPY x FAMILY", string);
                            }
                            _ => assert!(false),
                        },
                        _ => assert!(false),
                    }
                }
                _ => assert!(false),
            },
            _ => assert!(false),
        }
    }

    #[test]
    fn test_set_logic_command() {
        let program = parse_str("(set-logic QF_UF)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::SetLogic(symbol) => match symbol {
                Symbol::Simple(name) => assert_eq!("QF_UF", name),
                _ => assert!(false),
            },
            _ => assert!(false),
        }
    }

    #[test]
    fn test_set_option_command() {
        let program = parse_str("(set-option :print-success true)").unwrap();
        let SMTScript(commands) = program;
        assert_eq!(1, commands.len());
        match &commands[0] {
            Command::SetOption(option) => match option {
                SMTOption::PrintSuccess(value) => match value {
                    BooleanValue::True => assert!(true),
                    _ => assert!(false),
                },
                _ => assert!(false),
            },
            _ => assert!(false),
        }
    }

    #[test]
    fn test_complex1() {
        let smt_src = r#"
            |(declare-fun a () (_ FloatingPoint 8 24))
            |(declare-fun b () (_ FloatingPoint 8 24))
            |(assert (fp.eq a (fp #b0 #x86 #b00000000000000000000000)))
            |(assert (fp.eq b (fp #b0 #x86 #b00000000000000000000001)))
        "#
        .trim_margin()
        .unwrap();

        let SMTScript(commands) = parse_str(&smt_src).unwrap();
        assert_eq!(4, commands.len());
        assert_eq!(
            "(declare-fun a () (_ FloatingPoint 8 24))",
            format!("{}", commands[0])
        );
        assert_eq!(
            "(declare-fun b () (_ FloatingPoint 8 24))",
            format!("{}", commands[1])
        );
        assert_eq!(
            "(assert (fp.eq a (fp #b0 #x86 #b00000000000000000000000)))",
            format!("{}", commands[2])
        );
        assert_eq!(
            "(assert (fp.eq b (fp #b0 #x86 #b00000000000000000000001)))",
            format!("{}", commands[3])
        );
    }

    #[test]
    fn test_complex2() {
        let smt_src = r#"
            #|(set-info :smt-lib-version 2.5)
            #|(set-logic QF_FPBV)
            #|(set-info :source |
            #|Generated by: Daniel Liew, Daniel Schemmel, Cristian Cadar, Alastair Donaldson, and Rafael Zähl
            #|Generated on: 2017-4-28
            #|Generator: KLEE
            #|Application: Branch satisfiability check for symbolic execution of C programs
            #|Target solver: Z3 or MathSAT5
            #|Corresponding query: An equisatisfiable query (bitvectors replaced with reads from arrays of bitvectors) is available at QF_FPABV/liew/imperial_synthetic_sqrt_klee_bug.x86_64/query.05.smt2
            #||)
            #|(set-info :license "https://creativecommons.org/licenses/by/4.0/")
            #|(set-info :category "industrial")
            #|(set-info :status sat)
            #|(declare-fun x_ackermann!0 () (_ BitVec 32))
            #|(assert (not (fp.isNaN ((_ to_fp 8 24) x_ackermann!0))))
            #|(assert (not (fp.lt ((_ to_fp 8 24) x_ackermann!0) ((_ to_fp 8 24) (_ bv0 32)))))
            #|(assert (not (fp.gt ((_ to_fp 8 24) x_ackermann!0) ((_ to_fp 8 24) (_ bv1120403456 32)))))
            #|(assert (let ((?x8 ((_ to_fp 8 24) x_ackermann!0)))
            #| (let ((?x23 (fp.mul roundNearestTiesToEven (fp.add roundNearestTiesToEven ?x8 ((_ to_fp 8 24) (_ bv0 32))) ((_ to_fp 8 24) (_ bv1056964608 32)))))
            #| (let (($x28 (fp.lt (fp.abs (fp.sub roundNearestTiesToEven ?x23 ?x8)) ((_ to_fp 8 24) (_ bv869711765 32)))))
            #| (not $x28)))))
        "#.trim_margin_with("#|").unwrap();

        let SMTScript(commands) = parse_str(&smt_src).unwrap();
        assert_eq!(11, commands.len());
        assert_eq!(
            "(set-info :smt-lib-version 2.5)",
            format!("{}", commands[0])
        );
        assert_eq!("(set-logic QF_FPBV)", format!("{}", commands[1]));
        assert_eq!(r#"#|(set-info :source |
            #|Generated by: Daniel Liew, Daniel Schemmel, Cristian Cadar, Alastair Donaldson, and Rafael Zähl
            #|Generated on: 2017-4-28
            #|Generator: KLEE
            #|Application: Branch satisfiability check for symbolic execution of C programs
            #|Target solver: Z3 or MathSAT5
            #|Corresponding query: An equisatisfiable query (bitvectors replaced with reads from arrays of bitvectors) is available at QF_FPABV/liew/imperial_synthetic_sqrt_klee_bug.x86_64/query.05.smt2
            #||)
        "#.trim_margin_with("#|").unwrap(), format!("{}", commands[2]));
        assert_eq!(
            "(set-info :license \"https://creativecommons.org/licenses/by/4.0/\")",
            format!("{}", commands[3])
        );
        assert_eq!(
            "(set-info :category \"industrial\")",
            format!("{}", commands[4])
        );
        assert_eq!("(set-info :status sat)", format!("{}", commands[5]));
        assert_eq!(
            "(declare-fun x_ackermann!0 () (_ BitVec 32))",
            format!("{}", commands[6])
        );
        assert_eq!(
            "(assert (not (fp.isNaN ((_ to_fp 8 24) x_ackermann!0))))",
            format!("{}", commands[7])
        );
        assert_eq!(
            "(assert (not (fp.lt ((_ to_fp 8 24) x_ackermann!0) ((_ to_fp 8 24) (_ bv0 32)))))",
            format!("{}", commands[8])
        );
        assert_eq!("(assert (not (fp.gt ((_ to_fp 8 24) x_ackermann!0) ((_ to_fp 8 24) (_ bv1120403456 32)))))", format!("{}", commands[9]));
        assert_eq!("(assert (let ((?x8 ((_ to_fp 8 24) x_ackermann!0))) (let ((?x23 (fp.mul roundNearestTiesToEven (fp.add roundNearestTiesToEven ?x8 ((_ to_fp 8 24) (_ bv0 32))) ((_ to_fp 8 24) (_ bv1056964608 32))))) (let (($x28 (fp.lt (fp.abs (fp.sub roundNearestTiesToEven ?x23 ?x8)) ((_ to_fp 8 24) (_ bv869711765 32))))) (not $x28)))))", format!("{}", commands[10]));
    }

    #[test]

    fn test_complex3() {
        let smt_src = r#"
            #|(set-info :smt-lib-version 2.6)
            #|(set-logic QF_BV)
            #|(set-info :source | Constructed by Trevor Hansen to test edge case parsing |)
            #|(set-info :category "check")
            #|(set-info :status sat)
            #|(declare-fun notes () (_ BitVec 4))
            #|(declare-fun | | () (_ BitVec 4))
            #|(declare-fun || () (_ BitVec 4))
            #|(declare-fun ?v0 () (_ BitVec 4))
            #|(declare-fun v0 () (_ BitVec 4))
            #|(declare-fun |v1| () (_ BitVec 4))
            #|(declare-fun V0 () (_ BitVec 4))
            #|(declare-fun ~!@$%^&*_-+=><.?/ () (_ BitVec 4))
            #|(declare-fun |~!@$%^&*_-+=<>.?/()| () (_ BitVec 4))
            #|(declare-fun |~!@$%^&*_-+=<>.?/| () (_ BitVec 4))
            #|(assert (distinct notes || |~!@$%^&*_-+=<>.?/()| ?v0 |v0| v1 V0 ~!@$%^&*_-+=><.?/))
            #|(assert (not (= v0 V0)))
            #|(assert (not (= |~!@$%^&*_-+=<>.?/| ~!@$%^&*_-+=><.?/)))
            #|(assert (not (= || | |)))
            #|(assert (distinct (distinct || | |) (distinct |~!@$%^&*_-+=<>.?/| v0)))
            #|(check-sat)
            #|(exit)
        "#
        .trim_margin_with("#|")
        .unwrap();

        let SMTScript(commands) = parse_str(&smt_src).unwrap();
        assert_eq!(22, commands.len());
        assert_eq!(
            "(set-info :smt-lib-version 2.6)",
            format!("{}", commands[0])
        );
        assert_eq!("(set-logic QF_BV)", format!("{}", commands[1]));
        assert_eq!(
            "(set-info :source | Constructed by Trevor Hansen to test edge case parsing |)",
            format!("{}", commands[2])
        );
        assert_eq!("(set-info :category \"check\")", format!("{}", commands[3]));
        assert_eq!("(set-info :status sat)", format!("{}", commands[4]));
        assert_eq!(
            "(declare-fun notes () (_ BitVec 4))",
            format!("{}", commands[5])
        );
        assert_eq!(
            "(declare-fun | | () (_ BitVec 4))",
            format!("{}", commands[6])
        );
        assert_eq!(
            "(declare-fun || () (_ BitVec 4))",
            format!("{}", commands[7])
        );
        assert_eq!(
            "(declare-fun ?v0 () (_ BitVec 4))",
            format!("{}", commands[8])
        );
        assert_eq!(
            "(declare-fun v0 () (_ BitVec 4))",
            format!("{}", commands[9])
        );
        assert_eq!(
            "(declare-fun |v1| () (_ BitVec 4))",
            format!("{}", commands[10])
        );
        assert_eq!(
            "(declare-fun V0 () (_ BitVec 4))",
            format!("{}", commands[11])
        );
        assert_eq!(
            "(declare-fun ~!@$%^&*_-+=><.?/ () (_ BitVec 4))",
            format!("{}", commands[12])
        );
        assert_eq!(
            "(declare-fun |~!@$%^&*_-+=<>.?/()| () (_ BitVec 4))",
            format!("{}", commands[13])
        );
        assert_eq!(
            "(declare-fun |~!@$%^&*_-+=<>.?/| () (_ BitVec 4))",
            format!("{}", commands[14])
        );
        assert_eq!(
            "(assert (distinct notes || |~!@$%^&*_-+=<>.?/()| ?v0 |v0| v1 V0 ~!@$%^&*_-+=><.?/))",
            format!("{}", commands[15])
        );
        assert_eq!("(assert (not (= v0 V0)))", format!("{}", commands[16]));
        assert_eq!(
            "(assert (not (= |~!@$%^&*_-+=<>.?/| ~!@$%^&*_-+=><.?/)))",
            format!("{}", commands[17])
        );
        assert_eq!("(assert (not (= || | |)))", format!("{}", commands[18]));
        assert_eq!(
            "(assert (distinct (distinct || | |) (distinct |~!@$%^&*_-+=<>.?/| v0)))",
            format!("{}", commands[19])
        );
        assert_eq!("(check-sat)", format!("{}", commands[20]));
        assert_eq!("(exit)", format!("{}", commands[21]));
    }

    #[test]
    fn test_complex4() {
        let smt_src = r#"
            |(set-option :produce-models true)
            |(check-sat)
        "#
        .trim_margin()
        .unwrap();

        let SMTScript(commands) = parse_str(&smt_src).unwrap();
        assert_eq!(2, commands.len());
        assert_eq!(
            "(set-option :produce-models true)",
            format!("{}", commands[0])
        );
        assert_eq!("(check-sat)", format!("{}", commands[1]));
    }

    #[test]
    fn test_complex5() {
        let smt_src = r#"
            #|(set-info :smt-lib-version 2.6)
            #|(set-info :category "crafted")
            #|(set-info :source |Christoph M. Wintersteiger (cwinter@microsoft.com). Randomly generated floating-point testcases.|)
            #|(set-logic QF_FP)
            #|(set-info :status sat)
            #|(define-sort FPN () (_ FloatingPoint 11 53))
            #|(declare-fun x () FPN)
            #|(declare-fun y () FPN)
            #|(declare-fun r () FPN)
            #|(assert (= x (fp #b0 #b00010101101 #b0011111100110110001111111001000100100101101101110100)))
            #|(assert (= y (fp #b1 #b01101101001 #b1011011111110000011100100011101010000110001001100111)))
            #|(assert (= r (fp #b1 #b01101101001 #b1011011111110000011100100011101010000110001001100111)))
            #|(assert (= (fp.min x y) r))
            #|(check-sat)
            #|(exit)
        "#.trim_margin_with("#|").unwrap();

        let SMTScript(commands) = parse_str(&smt_src).unwrap();
        assert_eq!(15, commands.len());
        assert_eq!(
            "(set-info :smt-lib-version 2.6)",
            format!("{}", commands[0])
        );
        assert_eq!(
            "(set-info :category \"crafted\")",
            format!("{}", commands[1])
        );
        assert_eq!("(set-info :source |Christoph M. Wintersteiger (cwinter@microsoft.com). Randomly generated floating-point testcases.|)", format!("{}", commands[2]));
        assert_eq!("(set-logic QF_FP)", format!("{}", commands[3]));
        assert_eq!("(set-info :status sat)", format!("{}", commands[4]));
        assert_eq!(
            "(define-sort FPN () (_ FloatingPoint 11 53))",
            format!("{}", commands[5])
        );
        assert_eq!("(declare-fun x () FPN)", format!("{}", commands[6]));
        assert_eq!("(declare-fun y () FPN)", format!("{}", commands[7]));
        assert_eq!("(declare-fun r () FPN)", format!("{}", commands[8]));
        assert_eq!("(assert (= x (fp #b0 #b00010101101 #b0011111100110110001111111001000100100101101101110100)))", format!("{}", commands[9]));
        assert_eq!("(assert (= y (fp #b1 #b01101101001 #b1011011111110000011100100011101010000110001001100111)))", format!("{}", commands[10]));
        assert_eq!("(assert (= r (fp #b1 #b01101101001 #b1011011111110000011100100011101010000110001001100111)))", format!("{}", commands[11]));
        assert_eq!("(assert (= (fp.min x y) r))", format!("{}", commands[12]));
        assert_eq!("(check-sat)", format!("{}", commands[13]));
        assert_eq!("(exit)", format!("{}", commands[14]));
    }

    #[test]
    fn test_complex6() {
        let smt_src = r#"
            |(set-logic QF_BV)
            |(set-info :smt-lib-version 2.5)
            |(set-info :status unsat)
            |(declare-const a Bool)
            |(declare-const b Bool)
            |(declare-const c Bool)
            |(assert (and a b))
            |(assert (xor b c))
            |(assert c)
            |(check-sat)
            |(exit)
        "#
        .trim_margin()
        .unwrap();

        let SMTScript(commands) = parse_str(&smt_src).unwrap();
        assert_eq!(11, commands.len());
        assert_eq!("(set-logic QF_BV)", format!("{}", commands[0]));
        assert_eq!(
            "(set-info :smt-lib-version 2.5)",
            format!("{}", commands[1])
        );
        assert_eq!("(set-info :status unsat)", format!("{}", commands[2]));
        assert_eq!("(declare-const a Bool)", format!("{}", commands[3]));
        assert_eq!("(declare-const b Bool)", format!("{}", commands[4]));
        assert_eq!("(declare-const c Bool)", format!("{}", commands[5]));
        assert_eq!("(assert (and a b))", format!("{}", commands[6]));
        assert_eq!("(assert (xor b c))", format!("{}", commands[7]));
        assert_eq!("(assert c)", format!("{}", commands[8]));
        assert_eq!("(check-sat)", format!("{}", commands[9]));
        assert_eq!("(exit)", format!("{}", commands[10]));
    }

    #[test]
    fn test_complex7() {
        let smt_src = r#"
            |(declare-fun x () (_ BitVec 8))
            |(declare-fun y () (_ BitVec 8))
            |(declare-fun z () (_ BitVec 8))
            |(assert
            |    (=
            |      (ite
            |        (= x y)
            |        x
            |        y
            |     )
            |     z
            |   )
            | )
            |(check-sat)
        "#
        .trim_margin()
        .unwrap();

        let SMTScript(commands) = parse_str(&smt_src).unwrap();
        assert_eq!(5, commands.len());
        assert_eq!(
            "(declare-fun x () (_ BitVec 8))",
            format!("{}", commands[0])
        );
        assert_eq!(
            "(declare-fun y () (_ BitVec 8))",
            format!("{}", commands[1])
        );
        assert_eq!(
            "(declare-fun z () (_ BitVec 8))",
            format!("{}", commands[2])
        );
        assert_eq!(
            "(assert (= (ite (= x y) x y) z))",
            format!("{}", commands[3])
        );
        assert_eq!("(check-sat)", format!("{}", commands[4]));
    }

    #[test]
    fn test_array() {
        let smt_src = r#"
        |(set-logic ALL)
        |(declare-fun arr () (Array Int Int))
        |(assert (= (select arr 0) 10))
        |(assert (= (select arr 1) 20))
        |(assert (= (select arr 2) 30))
        |(assert (= (select arr 3) 40))
        |(check-sat)
        |(get-model)
        "#
        .trim_margin()
        .unwrap();

        let commands = parse_str(&smt_src).unwrap();
        let SMTScript(commands) = commands;

        assert_eq!(8, commands.len());
        assert_eq!("(set-logic ALL)", format!("{}", commands[0]));
        assert_eq!(
            "(declare-fun arr () (Array Int Int))",
            format!("{}", commands[1])
        );

        assert_eq!("(assert (= (select arr 0) 10))", format!("{}", commands[2]));
        assert_eq!("(assert (= (select arr 1) 20))", format!("{}", commands[3]));
        assert_eq!("(assert (= (select arr 2) 30))", format!("{}", commands[4]));
        assert_eq!("(assert (= (select arr 3) 40))", format!("{}", commands[5]));
        assert_eq!("(check-sat)", format!("{}", commands[6]));
        assert_eq!("(get-model)", format!("{}", commands[7]));
    }

    #[test]
    fn test_set_arch() {
        let smt_src = r#"
            |(set-arch X86)
        "#
        .trim_margin()
        .unwrap();

        let ast = parse_str(&smt_src).unwrap();
        let SMTScript(commands) = ast;
        assert_eq!(1, commands.len());
        let Command::SetArch(arch) = &commands[0] else {
            panic!("Expected `SetArch` command")
        };
        let Symbol::Simple(arch) = arch else {
            panic!("Expected `Symbol::Simple`")
        };
        assert_eq!("X86", arch);
    }

    #[test]
    fn test_alloc() {
        let smt_src = r#"
            |(alloc #x7FFFFFFF 1 true)
        "#
        .trim_margin()
        .unwrap();

        let ast = parse_str(&smt_src).unwrap();
        let SMTScript(commands) = ast;
        assert_eq!(1, commands.len());
        let Command::Alloc(addr, size, value) = &commands[0] else {
            panic!("Expected `Alloc` command")
        };
        let Hexadecimal { digit_num, bytes } = addr;
        assert_eq!(8, *digit_num);
        for i in 0..3 {
            assert_eq!(0xFF, bytes[i]);
        }
        assert_eq!(0x7F, bytes[3]);
        let Numeral(size) = size;
        assert_eq!(1, *size);
        let MemoryCell::Term(value) = value else {
            panic!("Expected `MemoryCell::Term`")
        };
        let Term::QualIdentifier(qid) = value else {
            panic!("Expected `Term::QualIdentifier`")
        };
        let QualIdentifier::Simple(id) = qid else {
            panic!("Expected `QualIdentifier::Simple`")
        };
        let Identifier::Symbol(sym) = id else {
            panic!("Expected `Identifier::Symbol`")
        };
        let Symbol::Simple(name) = sym else {
            panic!("Expected `Symbol::Simple`")
        };
        assert_eq!("true", name);
    }
}
