//! This example implements a small transpiler from Rust to Python. For the example, we run it on
//! the standard library code for multiplying two `u128`s.
#[path = "../common/mod.rs"]
mod common;

use anyhow::Result;
use indoc::{formatdoc, indoc};
use itertools::Itertools;
use std::io::Write;
use std::path::Path;
use std::process::Command;

use charon_lib::llbc_ast::*;

// Carries the data needed to transpile a function to Python.
struct PythonTranspiler<'a> {
    // Reference to the whole crate.
    krate: &'a TranslatedCrate,
    // The local variables of the function being translated.
    locals: Option<&'a Locals>,
}

// Logic to turn an llbc `Statement` to python.
impl<'a> PythonTranspiler<'a> {
    fn function_name(&self, function_id: FunDeclId) -> String {
        let function = &self.krate.fun_decls[function_id];
        match &function.src {
            // Functions that initialize constants are named init_CONSTANT.
            FunSource::GlobalInitializer(global) => format!(
                "init_{}",
                self.krate.item_name(global.id).short_str().unwrap()
            ),
            // Other functions have their normal name.
            _ => self
                .krate
                .item_name(function_id)
                .short_str()
                .unwrap()
                .to_string(),
        }
    }

    fn local(&self, id: LocalId) -> String {
        self.locals.unwrap().locals[id]
            .name
            .clone()
            .unwrap_or_else(|| format!("_{id}"))
    }

    fn place(&self, place: &Place) -> String {
        match &place.kind {
            PlaceKind::Local(id) => self.local(*id),
            PlaceKind::Global(global) => self
                .krate
                .item_name(global.id)
                .short_str()
                .unwrap()
                .to_owned(),
            PlaceKind::Projection(place, ProjectionElem::Field(_, field)) => {
                format!("{}[{}]", self.place(place), field.index())
            }
            PlaceKind::Projection(
                place,
                ProjectionElem::Index {
                    offset,
                    from_end: false,
                },
            ) => {
                format!("{}[{}]", self.place(place), self.operand(offset))
            }
            projection => panic!("unsupported place: {projection:?}"),
        }
    }

    fn constant(&self, constant: &ConstantExpr) -> String {
        match constant.kind() {
            ConstantExprKind::Bool(value) => if *value { "True" } else { "False" }.to_owned(),
            ConstantExprKind::Integer(IntegerValue::Unsigned(_, value)) => value.to_string(),
            ConstantExprKind::Integer(IntegerValue::Signed(_, value)) => value.to_string(),
            ConstantExprKind::Global(global) => self
                .krate
                .item_name(global.id)
                .short_str()
                .unwrap()
                .to_owned(),
            ConstantExprKind::Call(function, arguments) => {
                if let FnPtrKind::Fun(function) = function.kind.as_ref() {
                    format!(
                        "{}({})",
                        self.function_name(*function),
                        arguments
                            .iter()
                            .map(|argument| self.constant(argument))
                            .format(", ")
                    )
                } else {
                    panic!("unsupported constant function call: {function:?}")
                }
            }
            kind => panic!("unsupported constant: {kind:?}"),
        }
    }

    fn operand(&self, operand: &Operand) -> String {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place(place),
            Operand::Const(constant) => self.constant(constant),
        }
    }

    fn rvalue(&self, rvalue: &Rvalue) -> String {
        match rvalue {
            Rvalue::Use(operand, _) => self.operand(operand),
            Rvalue::BinaryOp(operation, left, right) => {
                let left = self.operand(left);
                let right = self.operand(right);
                match operation {
                    BinOp::BitAnd => format!("{left} & {right}"),
                    BinOp::BitOr => format!("{left} | {right}"),
                    BinOp::Eq => format!("{left} == {right}"),
                    BinOp::Lt => format!("{left} < {right}"),
                    // These are functions we added ourselves
                    BinOp::AddChecked => format!("checked_add_u128({left}, {right})"),
                    BinOp::MulChecked => format!("checked_mul_u128({left}, {right})"),
                    BinOp::Shl(_) => format!("{left} << {right}"),
                    BinOp::Shr(_) => format!("{left} >> {right}"),
                    operation => panic!("unsupported binary operation: {operation:?}"),
                }
            }
            Rvalue::UnaryOp(UnOp::Not, operand) => {
                let bits = match operand.ty().kind() {
                    TyKind::Scalar(ScalarTy::Integer(IntegerTy::Unsigned(UIntTy::U64))) => 64,
                    ty => panic!("unsupported bitwise-not type: {ty:?}"),
                };
                format!("(~{}) & ((1 << {bits}) - 1)", self.operand(operand))
            }
            Rvalue::UnaryOp(UnOp::Cast(_), operand) => {
                format!("int({})", self.operand(operand))
            }
            Rvalue::Aggregate(AggregateKind::Array(..), operands) => {
                let fields = operands.iter().map(|operand| self.operand(operand));
                format!("[{}]", fields.collect::<Vec<_>>().join(", "))
            }
            Rvalue::Aggregate(AggregateKind::Adt(adt, None, None), operands)
                if adt.as_builtin() == Some(BuiltinAdt::Tuple) =>
            {
                let fields = operands.iter().map(|operand| self.operand(operand));
                format!("({})", fields.collect::<Vec<_>>().join(", "))
            }
            rvalue => panic!("unsupported rvalue: {rvalue:?}"),
        }
    }

    fn write_statement(&self, output: &mut dyn Write, statement: &Statement, indent: usize) {
        let indent = "    ".repeat(indent);
        match &statement.kind {
            StatementKind::Assign(place, rvalue) => {
                writeln!(
                    output,
                    "{indent}{} = {}",
                    self.place(place),
                    self.rvalue(rvalue)
                )
                .unwrap();
            }
            StatementKind::Call { call, .. } => {
                if let FnOperand::Regular(function) = &call.func
                    && let FnPtrKind::Fun(function) = function.kind.as_ref()
                {
                    let function = self.function_name(*function);
                    let arguments = call.args.iter().map(|operand| self.operand(operand));
                    writeln!(
                        output,
                        "{indent}{} = {function}({})",
                        self.place(&call.dest),
                        arguments.collect::<Vec<_>>().join(", ")
                    )
                    .unwrap();
                } else {
                    panic!("unsupported function call: {:?}", call.func)
                }
            }
            StatementKind::Assert { assert, .. } => {
                writeln!(
                    output,
                    "{indent}assert {} == {}",
                    self.operand(&assert.cond),
                    if assert.expected { "True" } else { "False" }
                )
                .unwrap();
            }
            StatementKind::Return => writeln!(output, "{indent}return _0").unwrap(),
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Borrowck(_)
            | StatementKind::Nop => {}
            statement => panic!("unsupported statement: {statement:?}"),
        }
    }

    fn write_block(&self, output: &mut dyn Write, block: &Block, indent: usize) {
        for statement in &block.statements {
            self.write_statement(output, statement, indent + 1);
        }
    }

    fn write_function(&mut self, output: &mut dyn Write, function: &'a FunDecl) {
        // We only support functions that have a structured body; unstructured bodies won't happen
        // because of the options passed to Charon, and other bodies are for builtin or extern or other
        // weird functions.
        let body = function.body.as_structured().unwrap();
        self.locals = Some(&body.locals);

        // List the function arguments.
        let parameters = body
            .locals
            .locals
            .iter_enumerated()
            .skip(1)
            .take(body.locals.arg_count)
            .map(|(id, _)| self.local(id))
            .format(", ");
        writeln!(
            output,
            "def {}({}):",
            self.function_name(function.def_id),
            parameters
        )
        .unwrap();

        // Write the function body.
        self.write_block(output, &body.body, 0);
        writeln!(output).unwrap();
    }

    fn write_global(&mut self, output: &mut dyn Write, global: &GlobalDecl) {
        // A global means a constant or a static.
        writeln!(
            output,
            "{} = {}\n",
            global.item_meta.name.short_str().unwrap(),
            self.constant(&global.value)
        )
        .unwrap();
    }
}

fn main() -> Result<()> {
    let example_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/transpile_u128_to_python");
    let output_path = example_dir.join("output.py");

    // Translate the crate using Charon and parse the result.
    let krate: TranslatedCrate = {
        let input_path = example_dir.join("input.rs");
        let llbc_path =
            common::run_charon_on(&input_path, &["--extract-opaque-bodies", "--monomorphize"])?;
        charon_lib::deserialize_llbc(&llbc_path).unwrap()
    };

    // Start with helper functions that implement a builtin operation.
    let mut output = std::fs::File::create(&output_path)?;
    write!(
        output,
        "{}",
        indoc!(
            "
            U128_MASK = (1 << 128) - 1

            def checked_add_u128(left, right):
                result = left + right
                return result & U128_MASK, result > U128_MASK

            def checked_mul_u128(left, right):
                result = left * right
                return result & U128_MASK, result > U128_MASK

        "
        )
    )?;

    // Iterate over all functions and constants in dependency order, and print them in Python.
    let mut transpiler = PythonTranspiler {
        krate: &krate,
        locals: None,
    };
    for item_id in krate.in_dependency_order() {
        match item_id {
            ItemId::Fun(function_id) => {
                transpiler.write_function(&mut output, &krate.fun_decls[function_id]);
            }
            ItemId::Global(global_id) => {
                transpiler.write_global(&mut output, &krate.global_decls[global_id]);
            }
            _ => {}
        }
    }

    // Close the file
    drop(output);
    println!("Wrote the python code to {}", output_path.display());

    // Check that the python works correctly.
    let a = (1_u128 << 127) + 1;
    let b = 3_u128;
    let expected = a.wrapping_mul(b);
    let test = formatdoc!(
        "
        from output import mult_u128
        a = {a}
        b = {b}
        result = mult_u128(a, b)
        assert result == {expected}
    "
    );
    let status = Command::new("python3")
        .current_dir(&example_dir)
        .arg("-c")
        .arg(test)
        .status()
        .unwrap();
    assert!(status.success());

    Ok(())
}
