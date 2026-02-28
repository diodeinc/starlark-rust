/*
 * Copyright 2018 The Starlark in Rust Authors.
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//! Code called by the parser to handle complex cases not handled by the grammar.

use crate::codemap::CodeMap;
use crate::codemap::Pos;
use crate::codemap::Span;
use crate::codemap::Spanned;
use crate::dot_format_parser::FormatConv;
use crate::dot_format_parser::FormatParser;
use crate::dot_format_parser::FormatToken;
use crate::eval_exception::EvalException;
use crate::lexer::TokenFString;
use crate::lexer::lex_exactly_one_identifier;
use crate::slice_vec_ext::VecExt;
use crate::syntax::DialectTypes;
use crate::syntax::ast::AssignIdentP;
use crate::syntax::ast::AssignOp;
use crate::syntax::ast::AssignP;
use crate::syntax::ast::AssignTarget;
use crate::syntax::ast::AssignTargetP;
use crate::syntax::ast::AstAssignIdent;
use crate::syntax::ast::AstAssignTarget;
use crate::syntax::ast::AstExpr;
use crate::syntax::ast::AstFString;
use crate::syntax::ast::AstStmt;
use crate::syntax::ast::AstString;
use crate::syntax::ast::AstTypeExpr;
use crate::syntax::ast::Comma;
use crate::syntax::ast::Expr;
use crate::syntax::ast::ExprP;
use crate::syntax::ast::FStringP;
use crate::syntax::ast::IdentP;
use crate::syntax::ast::LoadArgP;
use crate::syntax::ast::LoadP;
use crate::syntax::ast::Stmt;
use crate::syntax::ast::StmtP;
use crate::syntax::ast::ToAst;
use crate::syntax::ast::TypeExpr;
use crate::syntax::ast::TypeExprP;
use crate::syntax::state::ParserState;
use crate::syntax::type_expr::TypeExprUnpackP;

#[derive(Debug, thiserror::Error)]
enum GrammarUtilError {
    #[error("left-hand-side of assignment must take the form `a`, `a.b` or `a[b]`")]
    InvalidLhs,
    #[error("left-hand-side of modifying assignment cannot be a list or tuple")]
    InvalidModifyLhs,
    #[error("type annotations not allowed on augmented assignments")]
    TypeAnnotationOnAssignOp,
    #[error("type annotations not allowed on multiple assignments")]
    TypeAnnotationOnTupleAssign,
    #[error("`load` statement requires at least two arguments")]
    LoadRequiresAtLeastTwoArguments,
}

/// Ensure we produce normalised Statements, rather than singleton Statements
pub fn statements(mut xs: Vec<AstStmt>, begin: usize, end: usize) -> AstStmt {
    if xs.len() == 1 {
        xs.pop().unwrap()
    } else {
        StmtP::Statements(xs).ast(begin, end)
    }
}

pub fn check_assign(codemap: &CodeMap, x: AstExpr) -> Result<AstAssignTarget, EvalException> {
    Ok(Spanned {
        span: x.span,
        node: match x.node {
            Expr::Tuple(xs) | Expr::List(xs) => {
                AssignTarget::Tuple(xs.into_try_map(|x| check_assign(codemap, x))?)
            }
            Expr::Dot(a, b) => AssignTarget::Dot(a, b),
            Expr::Index(a_b) => AssignTarget::Index(a_b),
            Expr::Identifier(x) => AssignTarget::Identifier(x.map(|s| AssignIdentP {
                ident: s.ident,
                payload: (),
            })),
            _ => {
                return Err(EvalException::new_anyhow(
                    GrammarUtilError::InvalidLhs.into(),
                    x.span,
                    codemap,
                ));
            }
        },
    })
}

pub fn check_assignment(
    codemap: &CodeMap,
    lhs: AstExpr,
    ty: Option<Box<AstTypeExpr>>,
    op: Option<AssignOp>,
    rhs: AstExpr,
) -> Result<Stmt, EvalException> {
    if op.is_some() {
        // for augmented assignment, Starlark doesn't allow tuple/list
        match &lhs.node {
            Expr::Tuple(_) | Expr::List(_) => {
                return Err(EvalException::new_anyhow(
                    GrammarUtilError::InvalidModifyLhs.into(),
                    lhs.span,
                    codemap,
                ));
            }
            _ => {}
        }
    }
    let lhs = check_assign(codemap, lhs)?;
    if let Some(ty) = &ty {
        let err = if op.is_some() {
            Some(GrammarUtilError::TypeAnnotationOnAssignOp)
        } else if matches!(lhs.node, AssignTargetP::Tuple(_)) {
            Some(GrammarUtilError::TypeAnnotationOnTupleAssign)
        } else {
            None
        };
        if let Some(err) = err {
            return Err(EvalException::new_anyhow(err.into(), ty.span, codemap));
        }
    }
    Ok(match op {
        None => Stmt::Assign(AssignP {
            lhs,
            ty: ty.map(|ty| *ty),
            rhs,
        }),
        Some(op) => Stmt::AssignModify(lhs, op, Box::new(rhs)),
    })
}

pub(crate) fn check_load_0(module: AstString, parser_state: &mut ParserState) -> Stmt {
    parser_state.errors.push(EvalException::new_anyhow(
        GrammarUtilError::LoadRequiresAtLeastTwoArguments.into(),
        module.span,
        parser_state.codemap,
    ));
    Stmt::Load(LoadP {
        module,
        args: Vec::new(),
        payload: (),
    })
}

pub(crate) fn check_load(
    module: AstString,
    args: Vec<((AstAssignIdent, AstString), Spanned<Comma>)>,
    last: Option<(AstAssignIdent, AstString)>,
    parser_state: &mut ParserState,
) -> Stmt {
    if args.is_empty() && last.is_none() {
        return check_load_0(module, parser_state);
    }

    let args = args
        .into_iter()
        .map(|((local, their), comma)| LoadArgP {
            local,
            their,
            comma: Some(comma),
        })
        .chain(last.map(|(local, their)| LoadArgP {
            local,
            their,
            comma: None,
        }))
        .collect();

    Stmt::Load(LoadP {
        module,
        args,
        payload: (),
    })
}

pub(crate) fn fstring(
    fstring: TokenFString,
    begin: usize,
    end: usize,
    parser_state: &mut ParserState,
) -> AstFString {
    if !parser_state.dialect.enable_f_strings {
        parser_state.error(
            Span::new(Pos::new(begin as _), Pos::new(end as _)),
            "Your Starlark dialect must enable f-strings to use them",
        );
    }

    let TokenFString {
        content,
        content_start_offset,
    } = fstring;

    let mut format = String::with_capacity(content.len());
    let mut expressions = Vec::new();

    let mut parser = FormatParser::new(&content);
    while let Some(res) = parser.next().transpose() {
        match res {
            Ok(FormatToken::Text(text)) => format.push_str(text),
            Ok(FormatToken::Escape(e)) => {
                // We are producing a format string here so we need to escape this back!
                format.push_str(e.back_to_escape())
            }
            Ok(FormatToken::Capture { capture, pos, conv }) => {
                let capture_begin = begin + content_start_offset + pos;
                let capture_end = capture_begin + capture.len();

                let expr = match parse_fstring_capture_identifier_expression(capture, capture_begin)
                {
                    Some(expr) => expr,
                    None => {
                        parser_state.error(
                            Span::new(Pos::new(capture_begin as _), Pos::new(capture_end as _)),
                            format_args!("Not a valid identifier: `{capture}`"),
                        );
                        // Might as well keep going here. This doesn't compromise the parsing of
                        // the rest of the format string.
                        continue;
                    }
                };

                expressions.push(expr);
                // Positional format.
                match conv {
                    FormatConv::Str => format.push_str("{}"),
                    FormatConv::Repr => format.push_str("{!r}"),
                }
            }
            Err(inner) => {
                // TODO: Reporting the exact position of the error would be better.
                parser_state.error(
                    Span::new(Pos::new(begin as _), Pos::new(end as _)),
                    format_args!("Invalid format: {inner:#}"),
                );
                break;
            }
        }
    }

    format.shrink_to_fit();

    FStringP {
        format: format.ast(begin, end),
        expressions,
    }
    .ast(begin, end)
}

fn parse_fstring_capture_identifier_expression(
    capture: &str,
    capture_begin: usize,
) -> Option<AstExpr> {
    fn parse_one_identifier(capture: &str, i: &mut usize) -> Option<(String, usize, usize)> {
        let bytes = capture.as_bytes();
        while *i < bytes.len() && bytes[*i].is_ascii_whitespace() {
            *i += 1;
        }

        let ident_begin = *i;
        while *i < bytes.len() && !bytes[*i].is_ascii_whitespace() && bytes[*i] != b'.' {
            *i += 1;
        }

        if ident_begin == *i {
            return None;
        }

        let ident = lex_exactly_one_identifier(&capture[ident_begin..*i])?;
        Some((ident, ident_begin, *i))
    }

    let mut i = 0;
    let (first_ident, first_begin, first_end) = parse_one_identifier(capture, &mut i)?;
    let mut expr = ExprP::Identifier(
        IdentP {
            ident: first_ident,
            payload: (),
        }
        .ast(capture_begin + first_begin, capture_begin + first_end),
    )
    .ast(capture_begin + first_begin, capture_begin + first_end);

    loop {
        let bytes = capture.as_bytes();
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i == bytes.len() {
            return Some(expr);
        }
        if bytes[i] != b'.' {
            return None;
        }
        i += 1;

        let (ident, ident_begin, ident_end) = parse_one_identifier(capture, &mut i)?;
        let attr = ident.ast(capture_begin + ident_begin, capture_begin + ident_end);
        let expr_begin = expr.span.begin().get() as usize;
        expr = ExprP::Dot(Box::new(expr), attr).ast(expr_begin, capture_begin + ident_end);
    }
}

#[cfg(test)]
mod tests {
    use crate::syntax::ast::ExprP;
    use crate::syntax::grammar_util::parse_fstring_capture_identifier_expression;

    #[test]
    fn fstring_capture_identifier_expression_dot() {
        let expr = parse_fstring_capture_identifier_expression("a.b", 10).unwrap();
        assert_eq!(format!("{}", expr.node), "a.b");
        assert_eq!(expr.span.begin().get(), 10);
        assert_eq!(expr.span.end().get(), 13);
        assert!(matches!(expr.node, ExprP::Dot(..)));
    }

    #[test]
    fn fstring_capture_identifier_expression_dot_with_spaces() {
        let expr = parse_fstring_capture_identifier_expression(" a . b ", 10).unwrap();
        assert_eq!(format!("{}", expr.node), "a.b");
        assert_eq!(expr.span.begin().get(), 11);
        assert_eq!(expr.span.end().get(), 16);
        assert!(matches!(expr.node, ExprP::Dot(..)));
    }

    #[test]
    fn fstring_capture_identifier_expression_rejects_non_dot_expression() {
        assert!(parse_fstring_capture_identifier_expression("a[0]", 10).is_none());
        assert!(parse_fstring_capture_identifier_expression("a.", 10).is_none());
        assert!(parse_fstring_capture_identifier_expression(".a", 10).is_none());
        assert!(parse_fstring_capture_identifier_expression("a.b c", 10).is_none());
    }
}

#[derive(thiserror::Error, Debug)]
enum DialectError {
    #[error("type annotations are not allowed in this dialect")]
    Types,
}

fn err<T>(codemap: &CodeMap, span: Span, err: DialectError) -> Result<T, EvalException> {
    Err(EvalException::new_anyhow(err.into(), span, codemap))
}

pub(crate) fn dialect_check_type(
    state: &ParserState,
    x: Spanned<Expr>,
) -> Result<Spanned<TypeExpr>, EvalException> {
    let span = x.span;
    if state.dialect.enable_types == DialectTypes::Disable {
        return err(state.codemap, x.span, DialectError::Types);
    }

    TypeExprUnpackP::unpack(&x, state.codemap).map_err(EvalException::from)?;

    Ok(x.map(|node| TypeExprP {
        expr: Spanned { node, span },
        payload: (),
    }))
}
