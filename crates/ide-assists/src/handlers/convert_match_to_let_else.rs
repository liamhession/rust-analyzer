// 9:52 - 
// next up: trying further work to bring over binders_in_pat from convert_let_else_to_match 
//     and: switching to master branch and rebuilding the whole thing, can i run the original version of this test in debug mode to step through and follow how it works?
use ide_db::defs::{Definition, NameRefClass};
use syntax::{
    ast::{self, HasName},
    ted, AstNode, SyntaxNode,
};

use crate::{
    assist_context::{AssistContext, Assists},
    AssistId, AssistKind,
};

// Given a pattern, find the name of the identifier introduced to the surrounding scope.
fn find_simple_binding(pat: ast::Pat) -> Option<ast::IdentPat> {
    if let ast::Pat::IdentPat(ident) = pat {
        Some(ident)
    } else {
        None
    }
}

// Tuple version
fn find_tuple_binding(pat: ast::Pat) -> Option<ast::TuplePat> {
    if let ast::Pat::TuplePat(tuple) = pat {
        Some(tuple)
    } else {
        None
    }
}

// Unified version, just returns a Pat no matter what
// Next time - get any idea of how better to return different Pat types
// in addition to ast::IdentPat it should also find ast::TuplePat and other patterns that makes sense
fn find_binding(pat: ast::Pat) -> Option<ast::Pat> {
    if let ast::Pat::IdentPat(ident) = pat {
        Some(ident)
    } else if let ast::Pat::TuplePat(tuple) = pat {
        Some(tuple)
    } else {
        None
    }
}

fn binders_in_pat(
    acc: &mut Vec<(Name, bool)>,
    pat: &Pat,
    sem: &Semantics<'_, RootDatabase>,
) -> Option<()> {
    use Pat::*;
    match pat {
        IdentPat(p) => {
            let ident = p.name()?;
            let ismut = p.ref_token().is_none() && p.mut_token().is_some();
            // check for const reference
            if sem.resolve_bind_pat_to_const(p).is_none() {
                acc.push((ident, ismut));
            }
            if let Some(inner) = p.pat() {
                binders_in_pat(acc, &inner, sem)?;
            }
            Some(())
        }
}

// Assist: convert_match_to_let_else
//
// Converts let statement with match initializer to let-else statement.
//
// ```
// # //- minicore: option
// fn foo(opt: Option<()>) {
//     let val = $0match opt {
//         Some(it) => it,
//         None => return,
//     };
// }
// ```
// ->
// ```
// fn foo(opt: Option<()>) {
//     let Some(val) = opt else { return };
// }
// ```
pub(crate) fn convert_match_to_let_else(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    let let_stmt: ast::LetStmt = ctx.find_node_at_offset()?;

    let pat = let_stmt.pat()?;
    println!("{}", pat);
    let mut binders = Vec::new();
    binders_in_pat(&mut binders, &pat, &ctx.sema);
    // let binding =
    // match find_simple_binding(pat) {
    //     Some(simple_identifier) => simple_identifier,
    //     None => find_tuple_binding(pat),
    // };
    

    // initializer is the expression whose value will be assigned to the identifer/tuple of identifiers on the lhs
    let initializer = match let_stmt.initializer() {
        Some(ast::Expr::MatchExpr(it)) => it,
        _ => return None, // TO TEST: if there is no match statement actually, just let v = 5; it gets in here?
    };
    let initializer_expr = initializer.expr()?;  // TO TEST: and then this fails, ending the function?

    let (extracting_arm, diverging_arm) = match find_arms(ctx, &initializer) {
        Some(it) => it,
        None => return None,
    };
    if extracting_arm.guard().is_some() {
        cov_mark::hit!(extracting_arm_has_guard); // TO TEST: Does not work for matches with guards?
        return None;
    }

    let diverging_arm_expr = diverging_arm.expr()?;  // None => return
    let extracting_arm_pat = extracting_arm.pat()?;   // Some(it) => it
    let extracted_variable = find_extracted_variable(ctx, &extracting_arm)?;  // it

    acc.add(
        AssistId("convert_match_to_let_else", AssistKind::RefactorRewrite),
        "Convert match to let-else",
        let_stmt.syntax().text_range(),
        |builder| {
            let extracting_arm_pat = rename_variable(&extracting_arm_pat, extracted_variable, binding);  // Some(val)
            builder.replace(
                let_stmt.syntax().text_range(),
                format!("let {extracting_arm_pat} = {initializer_expr} else {{ {diverging_arm_expr} }};")
            )
        },
    )
}

// Given a match expression, find extracting and diverging arms.
fn find_arms(
    ctx: &AssistContext<'_>,
    match_expr: &ast::MatchExpr,
) -> Option<(ast::MatchArm, ast::MatchArm)> {
    let arms = match_expr.match_arm_list()?.arms().collect::<Vec<_>>();
    if arms.len() != 2 {
        return None;
    }

    // TO TEST: This means that the final arm that does not return will be the "extracting" arm? Are we limited to only 2 arms?
    let mut extracting = None;
    let mut diverging = None;
    for arm in arms {
        if ctx.sema.type_of_expr(&arm.expr().unwrap()).unwrap().original().is_never() {
            diverging = Some(arm);
        } else {
            extracting = Some(arm);
        }
    }

    match (extracting, diverging) {
        (Some(extracting), Some(diverging)) => Some((extracting, diverging)),
        _ => {
            cov_mark::hit!(non_diverging_match);
            None
        }
    }
}

// Given an extracting arm, find the extracted variable.
// should probably return Vec<ast::Name> for every binding? instead of a single name
fn find_extracted_variable(ctx: &AssistContext<'_>, arm: &ast::MatchArm) -> Option<ast::Name> {
    match arm.expr()? {
        ast::Expr::PathExpr(path) => {
            let name_ref = path.syntax().descendants().find_map(ast::NameRef::cast)?;
            match NameRefClass::classify(&ctx.sema, &name_ref)? {
                NameRefClass::Definition(Definition::Local(local)) => {
                    let source = local.source(ctx.db()).value.left()?;
                    Some(source.name()?)
                }
                _ => None,
            }
        }
        _ => {
            cov_mark::hit!(extracting_arm_is_not_an_identity_expr);
            return None;
        }
    }
}

// Rename `extracted` with `binding` in `pat`.
// example: pat:= Some(it) => it     extracted:= it    binding:=  val
// should be updated according to return types of previous functions and should handle new cases
fn rename_variable(pat: &ast::Pat, extracted: ast::Name, binding: ast::IdentPat) -> SyntaxNode {
    let syntax = pat.syntax().clone_for_update();
    let extracted_syntax = syntax.covering_element(extracted.syntax().text_range());

    // If `extracted` variable is a record field, we should rename it to `binding`,
    // otherwise we just need to replace `extracted` with `binding`.

    if let Some(record_pat_field) = extracted_syntax.ancestors().find_map(ast::RecordPatField::cast)
    {
        if let Some(name_ref) = record_pat_field.field_name() {
            ted::replace(
                record_pat_field.syntax(),
                ast::make::record_pat_field(ast::make::name_ref(&name_ref.text()), binding.into())
                    .syntax()
                    .clone_for_update(),
            );
        }
    } else {
        ted::replace(extracted_syntax, binding.syntax().clone_for_update());
    }

    syntax
}

#[cfg(test)]
mod tests {
    use crate::tests::{check_assist, check_assist_not_applicable};

    use super::*;

    #[test]
    fn should_not_be_applicable_for_non_diverging_match() {
        cov_mark::check!(non_diverging_match);
        check_assist_not_applicable(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn foo(opt: Option<()>) {
    let val = $0match opt {
        Some(it) => it,
        None => (),
    };
}
"#,
        );
    }

    #[test]
    fn should_not_be_applicable_if_extracting_arm_is_not_an_identity_expr() {
        cov_mark::check_count!(extracting_arm_is_not_an_identity_expr, 2);
        check_assist_not_applicable(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn foo(opt: Option<i32>) {
    let val = $0match opt {
        Some(it) => it + 1,
        None => return,
    };
}
"#,
        );

        check_assist_not_applicable(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn foo(opt: Option<()>) {
    let val = $0match opt {
        Some(it) => {
            let _ = 1 + 1;
            it
        },
        None => return,
    };
}
"#,
        );
    }

    #[test]
    fn should_not_be_applicable_if_extracting_arm_has_guard() {
        cov_mark::check!(extracting_arm_has_guard);
        check_assist_not_applicable(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn foo(opt: Option<()>) {
    let val = $0match opt {
        Some(it) if 2 > 1 => it,
        None => return,
    };
}
"#,
        );
    }

    #[test]
    fn basic_pattern() {
        check_assist(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn foo(opt: Option<()>) {
    let val = $0match opt {
        Some(it) => it,
        None => return,
    };
}
    "#,
            r#"
fn foo(opt: Option<()>) {
    let Some(val) = opt else { return };
}
    "#,
        );
    }

    #[test]
    fn keeps_modifiers() {
        check_assist(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn foo(opt: Option<()>) {
    let ref mut val = $0match opt {
        Some(it) => it,
        None => return,
    };
}
    "#,
            r#"
fn foo(opt: Option<()>) {
    let Some(ref mut val) = opt else { return };
}
    "#,
        );
    }

    #[test]
    fn nested_pattern() {
        check_assist(
            convert_match_to_let_else,
            r#"
//- minicore: option, result
fn foo(opt: Option<Result<()>>) {
    let val = $0match opt {
        Some(Ok(it)) => it,
        _ => return,
    };
}
    "#,
            r#"
fn foo(opt: Option<Result<()>>) {
    let Some(Ok(val)) = opt else { return };
}
    "#,
        );
    }

    #[test]
    fn works_with_any_diverging_block() {
        check_assist(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn foo(opt: Option<()>) {
    loop {
        let val = $0match opt {
            Some(it) => it,
            None => break,
        };
    }
}
    "#,
            r#"
fn foo(opt: Option<()>) {
    loop {
        let Some(val) = opt else { break };
    }
}
    "#,
        );

        check_assist(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn foo(opt: Option<()>) {
    loop {
        let val = $0match opt {
            Some(it) => it,
            None => continue,
        };
    }
}
    "#,
            r#"
fn foo(opt: Option<()>) {
    loop {
        let Some(val) = opt else { continue };
    }
}
    "#,
        );

        check_assist(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn panic() -> ! {}

fn foo(opt: Option<()>) {
    loop {
        let val = $0match opt {
            Some(it) => it,
            None => panic(),
        };
    }
}
    "#,
            r#"
fn panic() -> ! {}

fn foo(opt: Option<()>) {
    loop {
        let Some(val) = opt else { panic() };
    }
}
    "#,
        );
    }

    #[test]
    fn struct_pattern() {
        check_assist(
            convert_match_to_let_else,
            r#"
//- minicore: option
struct Point {
    x: i32,
    y: i32,
}

fn foo(opt: Option<Point>) {
    let val = $0match opt {
        Some(Point { x: 0, y }) => y,
        _ => return,
    };
}
    "#,
            r#"
struct Point {
    x: i32,
    y: i32,
}

fn foo(opt: Option<Point>) {
    let Some(Point { x: 0, y: val }) = opt else { return };
}
    "#,
        );
    }

    #[test]
    fn tuple_pattern() {
        check_assist(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn foo() {
    let (val1, val2) = $0match Some((0, 1)) {
        Some(it) => it,
        None => return,
    };
}
    "#,
            r#"
fn foo() {
    let Some((x, y)) = Some((0, 1)) else { return };
}
    "#,
        );
    }

    #[test]
    fn renames_whole_binding() {
        check_assist(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn foo(opt: Option<i32>) -> Option<i32> {
    let val = $0match opt {
        it @ Some(42) => it,
        _ => return None,
    };
    val
}
    "#,
            r#"
fn foo(opt: Option<i32>) -> Option<i32> {
    let val @ Some(42) = opt else { return None };
    val
}
    "#,
        );
    }
}
