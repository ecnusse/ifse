//! This module defines the response AST according to SMT-LIB Standard 2.6.
//! These responses are syntactic objects used in a high level. Their semantic counterparts actually returned
//! by a fuzzer are in `crate::fuzzend::response`.

use super::{Attribute, FunctionDeclaration, FunctionDefinition, SExpr, Symbol, Term};

#[derive(Debug, Clone)]
pub enum ErrorBehavior {
    ImmediateExit,
    ContinuedExecution,
}

#[derive(Debug, Clone)]
pub enum ReasonUnknown {
    Timeout,
    Unsat,
    Other(SExpr),
}

#[derive(Debug, Clone)]
pub enum ModelResponse {
    DefineFun(FunctionDefinition),
    DefineFunRec(FunctionDefinition),
    DefineFunsRec(Vec<FunctionDeclaration>, Vec<Term>),
}

#[derive(Debug, Clone)]
pub enum InfoResponse {
    AssertionStackLevels(u32),
    Authors(String),
    ErrorBehavior(ErrorBehavior),
    Name(String),
    ReasonUnknown(ReasonUnknown),
    Version(String),
    Other(Attribute),
}

#[derive(Debug, Clone)]
pub struct ValuationPair(Term, Term);

#[derive(Debug, Clone)]
pub struct TValuationPair(Symbol, Term);

#[derive(Debug, Clone)]
pub enum CheckSatResponse {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct EchoResponse(String);

#[derive(Debug, Clone)]
pub struct GetAssertionsResponse(Vec<Term>);

#[derive(Debug, Clone)]
pub struct GetAssignmentResponse(Vec<ValuationPair>);

#[derive(Debug, Clone)]
pub struct GetInfoResponse(InfoResponse);

#[derive(Debug, Clone)]
pub struct GetModelResponse(ModelResponse);

#[derive(Debug, Clone)]
pub struct GetOptionResponse(Attribute);

#[derive(Debug, Clone)]
pub struct GetProofResponse(SExpr);

#[derive(Debug, Clone)]
pub struct GetUnsatAssumpResponse(Vec<Symbol>);

#[derive(Debug, Clone)]
pub struct GetUnsatCoreResponse(Vec<Symbol>);

#[derive(Debug, Clone)]
pub struct GetValueResponse(Vec<ValuationPair>);

#[derive(Debug, Clone)]
pub enum SpecificSuccessResponse {
    CheckSatResponse(CheckSatResponse),
    EchoResponse(EchoResponse),
    GetAssertionsResponse(GetAssertionsResponse),
    GetAssignmentResponse(GetAssignmentResponse),
    GetInfoResponse(GetInfoResponse),
    GetModelResponse(GetModelResponse),
    GetOptionResponse(GetOptionResponse),
    GetProofResponse(GetProofResponse),
    GetUnsatAssumptionsResponse(GetUnsatAssumpResponse),
    GetUnsatCoreResponse(GetUnsatCoreResponse),
    GetValueResponse(GetValueResponse),
}

#[derive(Debug, Clone)]
pub enum GeneralResponse {
    Success,
    SpecificSuccessResponse(SpecificSuccessResponse),
    Unsupported,
    Error(String),
}
