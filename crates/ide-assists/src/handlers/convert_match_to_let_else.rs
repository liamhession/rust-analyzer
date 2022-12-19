// 12:15 - 
// next up: TODO1 = try getting the tuple test towards the end of the test suite to work, by actually iterating through binders - need to make it a rename_variables function
//      your new superpower is not being afraid of using parent() and child() syntax tree functions

use ide_db::defs::{Definition, NameRefClass};
use hir::Semantics;
use ide_db::RootDatabase;
use syntax::{
    ast::{self, HasName, Name, Pat},
    ted, AstNode, SyntaxNode,
};

use crate::{AssistContext, AssistId, AssistKind, Assists};

// // Given a pattern, find the name of the identifier introduced to the surrounding scope.
// fn find_simple_binding(pat: ast::Pat) -> Option<ast::IdentPat> {
//     if let ast::Pat::IdentPat(ident) = pat {
//         Some(ident)
//     } else {
//         None
//     }
// }

// TO CHECK: can actually get rid of the "is_mutable" boolean, if going to use peek at "parent()" each time
fn binders_in_pat(
    acc: &mut Vec<Name>, // binding Identifier Pattern, and whether it is mut
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
                acc.push(ident);
            }
            if let Some(inner) = p.pat() {
                binders_in_pat(acc, &inner, sem)?;
            }
            Some(())
        }
        BoxPat(p) => p.pat().and_then(|p| binders_in_pat(acc, &p, sem)),
        RestPat(_) | LiteralPat(_) | PathPat(_) | WildcardPat(_) | ConstBlockPat(_) => Some(()),
        OrPat(p) => {
            for p in p.pats() {
                binders_in_pat(acc, &p, sem)?;
            }
            Some(())
        }
        ParenPat(p) => p.pat().and_then(|p| binders_in_pat(acc, &p, sem)),
        RangePat(p) => {
            if let Some(st) = p.start() {
                binders_in_pat(acc, &st, sem)?
            }
            if let Some(ed) = p.end() {
                binders_in_pat(acc, &ed, sem)?
            }
            Some(())
        }
        RecordPat(p) => {
            for f in p.record_pat_field_list()?.fields() {
                let pat = f.pat()?;
                binders_in_pat(acc, &pat, sem)?;
            }
            Some(())
        }
        RefPat(p) => dbg!(p.pat().and_then(|p| binders_in_pat(acc, &p, sem))),
        SlicePat(p) => {
            for p in p.pats() {
                binders_in_pat(acc, &p, sem)?;
            }
            Some(())
        }
        TuplePat(p) => {
            for p in p.fields() {
                binders_in_pat(acc, &p, sem)?;
            }
            Some(())
        }
        TupleStructPat(p) => {
            dbg!(p);
            for p in p.fields() {
                binders_in_pat(acc, &p, sem)?;
            }
            Some(())
        }
        // don't support macro pat yet
        MacroPat(_) => None,
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

    let top_level_pat = let_stmt.pat()?;
    println!("let_stmt.pat: {top_level_pat}");

    // initializer must be a MatchExpr, or this Assist does not apply
    let initializer_raw = let_stmt.initializer()?;
    println!("let_stmt.initializer(): {initializer_raw}");

    let initializer_match = match let_stmt.initializer() {
        Some(ast::Expr::MatchExpr(it)) => it,
        _ => return None,
    };
    let scrutinee_expr = initializer_match.expr()?;
    println!("scrutinee expression of match, let_stmt.initializer().expr(): {scrutinee_expr}");

    let (extracting_arm, diverging_arm) = match find_arms(ctx, &initializer_match) {
        Some(it) => it,
        None => return None,
    };
    // The assist does not work for matches with guards
    if extracting_arm.guard().is_some() {
        cov_mark::hit!(extracting_arm_has_guard);
        return None;
    }

    let diverging_arm_expr = diverging_arm.expr()?;  // return
    let extracting_arm_pat = extracting_arm.pat()?;   // Some(it)
    let extracted_variable = find_extracted_variable(ctx, &extracting_arm)?;  // it
    println!("diverging_arm_expr: {diverging_arm_expr}");
    println!("extracting_arm_pat: {extracting_arm_pat}");
    println!("extracted_variable: {extracted_variable}");

    // let mut binders = Vec::new();
    // binders_in_pat(&mut binders, &top_level_pat, &ctx.sema);

    // // let bindings = binders;
    // dbg!(binders);

    // let binding = find_simple_binding(pat)?;

    let target = let_stmt.syntax().text_range();

    let pat_in_extracting_arm_format = rename_variables(&extracting_arm_pat, extracted_variable, top_level_pat); //&binders);

    acc.add(
        AssistId("convert_match_to_let_else", AssistKind::RefactorRewrite),
        "Convert match to let-else",
        target,
        |builder| {
            builder.replace(
                target,
                format!("let {pat_in_extracting_arm_format} = {scrutinee_expr} else {{ {diverging_arm_expr} }};")
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
fn find_extracted_variable(ctx: &AssistContext<'_>, arm: &ast::MatchArm) -> Option<Name> {
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

// // Rename `extracted` with `binding` in `pat`.
// // example: pat:= Some(it) => it     extracted:= it    binding:=  val
// // should be updated according to return types of previous functions and should handle new cases
// fn rename_variable(pat: &ast::Pat, extracted: Name, binding: ast::IdentPat) -> SyntaxNode {
//     let syntax = pat.syntax().clone_for_update();
//     let extracted_syntax = syntax.covering_element(extracted.syntax().text_range());

//     // If `extracted` variable is a record field, we should rename it to `binding`,
//     // otherwise we just need to replace `extracted` with `binding`.

//     // if let Some(record_pat_field) = extracted_syntax.ancestors().find_map(ast::RecordPatField::cast)
//     // {
//     //     if let Some(name_ref) = record_pat_field.field_name() {
//     //         ted::replace(
//     //             record_pat_field.syntax(),
//     //             ast::make::record_pat_field(ast::make::name_ref(&name_ref.text()), binding.into())
//     //                 .syntax()
//     //                 .clone_for_update(),
//     //         );
//     //     }
//     // } else {
//         ted::replace(extracted_syntax, binding.syntax().clone_for_update());
//     // }

//     syntax
// }

fn rename_variables(pat: &ast::Pat, extracted: Name, let_stmt_pat: Pat) -> SyntaxNode {
    let syntax = pat.syntax().clone_for_update();
    dbg!(extracted.syntax().parent());
    let extracted_syntax = syntax.covering_element(extracted.syntax().text_range());
    println!("syntax: {syntax}, extracted_syntax: {extracted_syntax}");

    // If `extracted` variable is a record field, we should rename it to `binding`,
    // otherwise we just need to replace `extracted` with `binding`.

    if let Some(record_pat_field) = extracted_syntax.ancestors().find_map(ast::RecordPatField::cast)
    {
        if let Some(name_ref) = record_pat_field.field_name() {
            ted::replace(
                record_pat_field.syntax(),
                ast::make::record_pat_field(ast::make::name_ref(&name_ref.text()), let_stmt_pat.into())
                    .syntax()
                    .clone_for_update(),
            );
        }
    } else {
    // } else {
        // let (binding_name, is_binding_mut) = binding_and_mutability;
        // let bindings_str = if *is_binding_mut { format!("mut {binding_name}") } else { format!("{binding_name}") }; 
        // parent of binding is the node that includes "ref" and "mut" if it had them
        // TODO1: will need to iterate through extracted as well when it's a tuple, and put each binder in the place of its corresponding extracted thing
        // for (binder) in binders.iter() {
        //     let binding_with_modifiers = match binder.syntax().parent() {
        //         Some(parent_ident) => parent_ident,
        //         None => binder.syntax().to_owned(),
        //     };
        //     ted::replace(extracted_syntax, binding_with_modifiers.clone_for_update()); // is this necessary, what other unnecessary deref stuff is in preceding lines?
        // }
    // }

        ted::replace(extracted_syntax, let_stmt_pat.syntax().clone_for_update()); // is this necessary, what other unnecessary deref stuff is in preceding lines?
    }

    syntax //.text().to_string().replace(&extracted_syntax.to_string(), &dbg!(bindings_str))
}

#[cfg(test)]
mod tests {
    use crate::tests::{check_assist, check_assist_not_applicable};

    use super::*;

    #[test]
    fn should_not_be_applicable_for_non_match_initializer() {
        check_assist_not_applicable(
            convert_match_to_let_else,
            r#"
//- minicore: option
fn foo(opt: Option<()>) {
    let val = $05;
}
"#,
        );
    }

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
    fn struct_pattern() {   // FAILS - was this covered by the "RecordPatField" case in the original?
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
    let (x, y) = $0match Some((0, 1)) {
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
