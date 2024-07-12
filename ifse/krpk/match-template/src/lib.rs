// Copyright 2022 TiKV Project Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#[macro_use]
extern crate quote;

use std::collections::HashMap;

use either::Either;
use proc_macro2::{Group, Literal, TokenStream, TokenTree};
use quote::ToTokens;
use syn::{
    parse::{Parse, ParseStream, Result},
    punctuated::Punctuated,
    *,
};

/// This crate provides a macro that can be used to append a match expression
/// with multiple arms, where the tokens in the first arm, as a template, can be
/// subsitituted and the template arm will be expanded into multiple arms.
///
/// For example, the following code
///
/// ```ignore
/// match_template! {
///     T = [Int, Real, Double],
///     match Foo {
///         EvalType::T => { panic!("{}", EvalType::T); },
///         EvalType::Other => unreachable!(),
///     }
/// }
/// ```
///
/// generates
///
/// ```ignore
/// match Foo {
///     EvalType::Int => { panic!("{}", EvalType::Int); },
///     EvalType::Real => { panic!("{}", EvalType::Real); },
///     EvalType::Double => { panic!("{}", EvalType::Double); },
///     EvalType::Other => unreachable!(),
/// }
/// ```
///
/// In addition, substitution can vary on two sides of the arms.
///
/// For example,
///
/// ```ignore
/// match_template! {
///     T = [Foo, Bar => Baz],
///     match Foo {
///         EvalType::T => { panic!("{}", EvalType::T); },
///     }
/// }
/// ```
///
/// generates
///
/// ```ignore
/// match Foo {
///     EvalType::Foo => { panic!("{}", EvalType::Foo); },
///     EvalType::Bar => { panic!("{}", EvalType::Baz); },
/// }
/// ```
///
/// Wildcard match arm is also supported (but there will be no substitution).
#[proc_macro]
pub fn match_template(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let mt = parse_macro_input!(input as MatchTemplate);
    mt.expand().into()
}
struct MatchTemplate {
    template_substitutes: HashMap<Ident, Punctuated<Substitution, Token![,]>>,
    match_exp: Box<Expr>,
    template_arms: Vec<Arm>,
    remaining_arms: Vec<Arm>,
}

impl Parse for MatchTemplate {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let mut template_substitutes = HashMap::new();
        while let Ok(template_ident) = input.parse::<Ident>() {
            input.parse::<Token![=]>()?;
            let substitutes_tokens;
            bracketed!(substitutes_tokens in input);
            let substitutes =
                Punctuated::<Substitution, Token![,]>::parse_terminated(&substitutes_tokens)?;
            template_substitutes.insert(template_ident, substitutes);
            input.parse::<Token![,]>()?;
        }
        let m: ExprMatch = input.parse()?;
        let mut arms = m.arms;
        arms.iter_mut().for_each(|arm| arm.comma = None);
        assert!(!arms.is_empty(), "Expect at least 1 match arm");
        // let template_arms = arms.remove(template_substitutes.len());
        let template_arms = {
            let mut template_arms = Vec::new();
            for _ in 0..template_substitutes.len() {
                template_arms.push(arms.remove(0));
            }
            template_arms
        };
        assert!(
            template_arms.iter().all(|arm| arm.guard.is_none()),
            "Expect no match arm guard"
        );

        Ok(Self {
            template_substitutes,
            match_exp: m.expr,
            template_arms,
            remaining_arms: arms,
        })
    }
}

impl MatchTemplate {
    fn expand(self) -> TokenStream {
        let Self {
            template_substitutes,
            match_exp,
            template_arms,
            remaining_arms,
        } = self;
        let mut match_arms = Vec::new();
        for arm in template_arms {
            let pat = arm.pat.clone();
            let pat_ident = {
                fn extract_ident(pat: &Pat) -> &Ident {
                    match pat {
                        Pat::Ident(ident) => &ident.ident,
                        Pat::Reference(pat_ref) => extract_ident(&pat_ref.pat),
                        Pat::Struct(pat_struct) => &pat_struct.path.segments.last().unwrap().ident,
                        Pat::TupleStruct(tuple_struct) => {
                            &tuple_struct.path.segments.last().unwrap().ident
                        }
                        _ => todo!(),
                    }
                }
                extract_ident(&pat)
            };
            let substitutes = template_substitutes.get(&pat_ident).unwrap();
            for substitution in substitutes.iter() {
                let (left_tokens, right_tokens) = match substitution {
                    Substitution::IdenticalIdent(ident) => {
                        (ident.clone().into_token_stream(), ident.into_token_stream())
                    }
                    Substitution::MapIdent(left_ident, right_tokens) => {
                        (left_ident.into_token_stream(), right_tokens.clone())
                    }
                    Substitution::IdenticalLiteral(literal) => (
                        literal.clone().into_token_stream(),
                        literal.into_token_stream(),
                    ),
                    Substitution::MapLiteral(literal, right_tokens) => {
                        (literal.into_token_stream(), right_tokens.clone())
                    }
                };
                let mut new_arm = arm.clone();
                new_arm.pat = replace_in_token_stream(arm.pat.clone(), &pat_ident, &left_tokens);
                new_arm.body = replace_in_token_stream(arm.body.clone(), &pat_ident, &right_tokens);
                match_arms.push(new_arm);
            }
        }
        quote! {
            match #match_exp {
                #(#match_arms,)*
                #(#remaining_arms,)*
            }
        }
    }
}

#[derive(Debug)]
enum Substitution {
    IdenticalIdent(Ident),
    MapIdent(Ident, TokenStream),
    IdenticalLiteral(Literal),
    MapLiteral(Literal, TokenStream),
}

impl Parse for Substitution {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let left: Either<Ident, Literal> = if let Ok(ident) = input.parse::<Ident>() {
            Either::Left(ident)
        } else {
            Either::Right(input.parse::<Literal>()?)
        };
        let fat_arrow: Option<Token![=>]> = input.parse()?;
        if fat_arrow.is_some() {
            let mut right_tokens: Vec<TokenTree> = vec![];
            while !input.peek(Token![,]) && !input.is_empty() {
                right_tokens.push(input.parse()?);
            }
            match left {
                Either::Left(ident) => Ok(Substitution::MapIdent(
                    ident,
                    right_tokens.into_iter().collect(),
                )),
                Either::Right(literal) => Ok(Substitution::MapLiteral(
                    literal,
                    right_tokens.into_iter().collect(),
                )),
            }
        } else {
            match left {
                Either::Left(ident) => Ok(Substitution::IdenticalIdent(ident)),
                Either::Right(literal) => Ok(Substitution::IdenticalLiteral(literal)),
            }
        }
    }
}

fn replace_in_token_stream<T: ToTokens + Parse>(
    input: T,
    from_ident: &Ident,
    to_tokens: &TokenStream,
) -> T {
    let mut tokens = TokenStream::new();
    input.to_tokens(&mut tokens);

    let tokens: TokenStream = tokens
        .into_iter()
        .flat_map(|token| match token {
            TokenTree::Ident(ident) if ident == *from_ident => to_tokens.clone(),
            TokenTree::Group(group) => Group::new(
                group.delimiter(),
                replace_in_token_stream(group.stream(), from_ident, to_tokens),
            )
            .into_token_stream(),
            other => other.into(),
        })
        .collect();

    syn::parse2(tokens).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        let input = r#"
            T = [Int, Real, Double],
            match foo() {
                EvalType::T => { panic!("{}", EvalType::T); },
                EvalType::Other => unreachable!(),
            }
        "#;

        let expect_output = r#"
            match foo() {
                EvalType::Int => { panic!("{}", EvalType::Int); },
                EvalType::Real => { panic!("{}", EvalType::Real); },
                EvalType::Double => { panic!("{}", EvalType::Double); },
                EvalType::Other => unreachable!(),
            }
        "#;
        let expect_output_stream: TokenStream = expect_output.parse().unwrap();

        let mt: MatchTemplate = syn::parse_str(input).unwrap();
        let output = mt.expand();
        assert_eq!(output.to_string(), expect_output_stream.to_string());
    }

    #[test]
    fn test_wildcard() {
        let input = r#"
            TT = [Foo, Bar],
            match v {
                VectorValue::TT => EvalType::TT,
                _ => unreachable!(),
            }
        "#;

        let expect_output = r#"
            match v {
                VectorValue::Foo => EvalType::Foo,
                VectorValue::Bar => EvalType::Bar,
                _ => unreachable!(),
            }
        "#;
        let expect_output_stream: TokenStream = expect_output.parse().unwrap();

        let mt: MatchTemplate = syn::parse_str(input).unwrap();
        let output = mt.expand();
        assert_eq!(output.to_string(), expect_output_stream.to_string());
    }

    #[test]
    fn test_map() {
        let input = r#"
            TT = [Foo, Bar => Baz, Bark => <&'static Whooh>()],
            match v {
                VectorValue::TT => EvalType::TT,
                EvalType::Other => unreachable!(),
            }
        "#;

        let expect_output = r#"
            match v {
                VectorValue::Foo => EvalType::Foo,
                VectorValue::Bar => EvalType::Baz,
                VectorValue::Bark => EvalType:: < & 'static Whooh>(),
                EvalType::Other => unreachable!(),
            }
        "#;
        let expect_output_stream: TokenStream = expect_output.parse().unwrap();

        let mt: MatchTemplate = syn::parse_str(input).unwrap();
        let output = mt.expand();
        assert_eq!(output.to_string(), expect_output_stream.to_string());
    }
}
