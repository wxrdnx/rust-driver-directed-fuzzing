#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

mod util;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::LangItem;
use rustc_interface::interface;
use rustc_middle::mir::{
    AssertKind, Body, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use serde_json::{json, Value};
use std::collections::{BTreeSet, HashMap};
use std::env;
use std::fs::{self, File};
use std::io::{self, BufWriter, Write};
use std::path::PathBuf;
use util::{push_edge, sanitize, source_span, span_json, type_json, unwind_target, SourceSpan};

struct Analysis {
    crate_name: String,
    compiler: Compiler,
    panic_sites: Vec<PanicSite>,
    unsafe_blocks: Vec<UnsafeBlock>,
    calls: Vec<CallSite>,
    functions: Vec<FunctionAnalysis>,
}

struct Compiler {
    release: String,
    commit: String,
}

struct PanicSite {
    id: String,
    kind: String,
    function: String,
    span: SourceSpan,
    mir_location: MirLocation,
    condition: Option<String>,
    expected: Option<bool>,
    callee: Option<String>,
}

struct UnsafeBlock {
    id: String,
    function: String,
    hir_id: String,
    span: SourceSpan,
}

struct MirLocation {
    basic_block: usize,
    terminator: bool,
}

struct CallSite {
    id: String,
    caller: String,
    call_kind: String,
    callee: Option<String>,
    function_operand: String,
    arguments: Vec<String>,
    destination: String,
    target: Option<usize>,
    unwind: String,
    is_panic_sink: bool,
    span: SourceSpan,
    mir_location: MirLocation,
}

struct FunctionAnalysis {
    function: String,
    may_panic: bool,
    panic_path: Vec<String>,
}

struct Analyzer {
    output_dir: PathBuf,
    error: Option<io::Error>,
}

struct EmptyCallbacks;

// Explicit unsafe blocks exist in HIR
// So we need an visitor to record them
struct UnsafeBlockVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    function: &'a str,
    blocks: &'a mut Vec<UnsafeBlock>,
}

impl<'tcx> Visitor<'tcx> for UnsafeBlockVisitor<'tcx, '_> {
    fn visit_block(&mut self, block: &'tcx rustc_hir::Block<'tcx>) {
        if matches!(
            block.rules,
            rustc_hir::BlockCheckMode::UnsafeBlock(rustc_hir::UnsafeSource::UserProvided)
        ) {
            self.blocks.push(UnsafeBlock {
                id: String::new(),
                function: self.function.into(),
                hir_id: format!("{:?}", block.hir_id),
                span: source_span(self.tcx, block.span),
            });
        }
        intravisit::walk_block(self, block);
    }
}

impl Callbacks for Analyzer {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        if let Err(error) = analyze(tcx, &self.output_dir) {
            self.error = Some(error);
        }
        Compilation::Continue
    }
}

impl Callbacks for EmptyCallbacks {}

fn main() -> io::Result<()> {
    let arguments: Vec<String> = env::args().collect();
    let output_dir = env::var_os("RUST_KERNEL_ANALYSIS_OUTPUT")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("rust-kernel-analysis"));
    let mut analyzer = Analyzer {
        output_dir,
        error: None,
    };

    if is_kernel_crate(&arguments) {
        rustc_driver::run_compiler(&arguments, &mut analyzer);
    } else {
        rustc_driver::run_compiler(&arguments, &mut EmptyCallbacks);
    }

    match analyzer.error {
        Some(error) => Err(error),
        None => Ok(()),
    }
}

fn is_kernel_crate(arguments: &[String]) -> bool {
    let Some(input) = arguments.iter().find(|argument| argument.ends_with(".rs")) else {
        return false;
    };
    let input = input.replace('\\', "/");
    input.contains("/common/rust/")
        || input.contains("/common/drivers/")
        || input.starts_with("rust/")
        || input.starts_with("drivers/")
}

fn analyze(tcx: TyCtxt<'_>, output_dir: &PathBuf) -> io::Result<()> {
    let mut panic_sites = Vec::new();
    let mut unsafe_blocks = Vec::new();
    let mut calls = Vec::new();
    let mut cfgs = Vec::new();
    let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();

    // HIR + MIR traversal
    for def_id in tcx.hir_body_owners() {
        let function = tcx.def_path_str(def_id.to_def_id());

        // HIR pass: collect unsafe blocks
        UnsafeBlockVisitor {
            tcx,
            function: &function,
            blocks: &mut unsafe_blocks,
        }
        .visit_body(tcx.hir_body_owned_by(def_id));
        // MIR pass: for function-like bodies like fns, methods, and closures
        if tcx.def_kind(def_id).is_fn_like() {
            // Panic and calls are in the optimized MIR
            let body = tcx.optimized_mir(def_id.to_def_id());
            // Record the CFG
            cfgs.push(mir_cfg(
                tcx,
                body,
                &crate_name,
                &function,
                def_id.local_def_index.as_u32(),
            ));
            // Then, scan the MIR for panic and call sites
            analyze_body(tcx, body, &function, &mut panic_sites, &mut calls);
        }
    }

    for (index, site) in panic_sites.iter_mut().enumerate() {
        site.id = format!("panic-{}", index + 1);
    }
    for (index, call) in calls.iter_mut().enumerate() {
        call.id = format!("call-{}", index + 1);
    }
    for (index, block) in unsafe_blocks.iter_mut().enumerate() {
        block.id = format!("unsafe-block-{}", index + 1);
    }

    let functions = propagate_panics(&panic_sites, &calls);
    let analysis = Analysis {
        crate_name,
        compiler: compiler_info(),
        panic_sites,
        unsafe_blocks,
        calls,
        functions,
    };

    fs::create_dir_all(output_dir)?;
    let cfg_path = output_dir.join(format!("{}.cfg.jsonl", sanitize(&analysis.crate_name)));
    let mut cfg_output = BufWriter::new(File::create(cfg_path)?);
    for cfg in cfgs {
        serde_json::to_writer(&mut cfg_output, &cfg).map_err(io::Error::other)?;
        writeln!(cfg_output)?;
    }
    let path = output_dir.join(format!("{}.json", sanitize(&analysis.crate_name)));
    serde_json::to_writer_pretty(File::create(path)?, &analysis_json(&analysis))
        .map_err(io::Error::other)
}

fn mir_cfg<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    crate_name: &str,
    function: &str,
    def_index: u32,
) -> Value {
    let mut blocks = Vec::new();
    let mut edges = Vec::new();
    let mut definitions = Vec::new();
    let mut uses = Vec::new();
    let mut memory_accesses = Vec::new();
    let function_id = format!("rust:{crate_name}:{def_index}:{function}");

    for (block, data) in body.basic_blocks.iter_enumerated() {
        let terminator = data.terminator();
        let span = source_span(tcx, terminator.source_info.span);
        let statements = data
            .statements
            .iter()
            .enumerate()
            .map(|(index, statement)| {
                statement_json(
                    tcx,
                    body,
                    &function_id,
                    block.index(),
                    index,
                    statement,
                    &mut definitions,
                    &mut uses,
                    &mut memory_accesses,
                )
            })
            .collect::<Vec<_>>();
        let terminator_record = terminator_json(
            tcx,
            body,
            &function_id,
            block.index(),
            terminator,
            &mut definitions,
            &mut uses,
            &mut memory_accesses,
        );
        blocks.push(json!({
            "id": format!("bb{}", block.index()),
            "index": block.index(),
            "is_cleanup": data.is_cleanup,
            "statements": statements,
            "terminator": terminator_record,
            "span": span_json(&span),
        }));

        match &terminator.kind {
            TerminatorKind::Goto { target } => {
                push_edge(&mut edges, block.index(), target.index(), "goto", None)
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                for (value, target) in targets.iter() {
                    edges.push(json!({
                        "source": format!("bb{}", block.index()),
                        "target": format!("bb{}", target.index()),
                        "kind": "switch_case",
                        "value": value.to_string(),
                        "condition": operand_json(tcx, body, discr),
                    }));
                }
                edges.push(json!({
                    "source": format!("bb{}", block.index()),
                    "target": format!("bb{}", targets.otherwise().index()),
                    "kind": "switch_default",
                    "condition": operand_json(tcx, body, discr),
                }));
            }
            TerminatorKind::Call { target, unwind, .. } => {
                if let Some(target) = target {
                    push_edge(
                        &mut edges,
                        block.index(),
                        target.index(),
                        "call_return",
                        None,
                    );
                }
                if let Some(target) = unwind_target(unwind) {
                    push_edge(&mut edges, block.index(), target.index(), "unwind", None);
                }
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                unwind,
                ..
            } => {
                let condition =
                    Some(json!({"condition": operand_json(tcx, body, cond), "expected": expected}));
                push_edge(
                    &mut edges,
                    block.index(),
                    target.index(),
                    "assert_success",
                    condition,
                );
                if let Some(target) = unwind_target(unwind) {
                    push_edge(&mut edges, block.index(), target.index(), "unwind", None);
                }
            }
            TerminatorKind::Drop { target, unwind, .. } => {
                push_edge(
                    &mut edges,
                    block.index(),
                    target.index(),
                    "drop_return",
                    None,
                );
                if let Some(target) = unwind_target(unwind) {
                    push_edge(&mut edges, block.index(), target.index(), "unwind", None);
                }
            }
            _ => {
                for target in terminator.successors() {
                    push_edge(&mut edges, block.index(), target.index(), "successor", None);
                }
            }
        }
    }

    json!({
        "record": "function_cfg",
        "schema_version": 1,
        "function": {
            "id": function_id,
            "name": function,
            "compiler_id": format!("DefIndex({def_index})"),
            "linkage_name": null,
            "language": "rust",
            "representation": "mir",
            "module": crate_name,
            "entry_block": "bb0",
        },
        "blocks": blocks,
        "edges": edges,
        "locals": locals_json(tcx, body),
        "definitions": definitions,
        "uses": uses,
        "memory_accesses": memory_accesses,
    })
}

fn terminator_kind(terminator: &rustc_middle::mir::Terminator<'_>) -> &'static str {
    match &terminator.kind {
        TerminatorKind::Goto { .. } => "goto",
        TerminatorKind::SwitchInt { .. } => "switch",
        TerminatorKind::Call { .. } => "call",
        TerminatorKind::Assert { .. } => "assert",
        TerminatorKind::Drop { .. } => "drop",
        TerminatorKind::Return => "return",
        TerminatorKind::Unreachable => "unreachable",
        TerminatorKind::InlineAsm { .. } => "inline_asm",
        _ => "other",
    }
}

fn locals_json(tcx: TyCtxt<'_>, body: &Body<'_>) -> Vec<Value> {
    body.local_decls
        .iter_enumerated()
        .map(|(local, declaration)| {
            let index = local.index();
            let argument_index = if index > 0 && index <= body.arg_count { Some(index - 1) } else { None };
            json!({
                "id": format!("_{index}"),
                "kind": if index == 0 { "return" } else if index <= body.arg_count { "argument" } else { "local" },
                "argument_index": argument_index,
                "type": type_json(tcx, declaration.ty),
                "span": span_json(&source_span(tcx, declaration.source_info.span)),
            })
        })
        .collect()
}

fn statement_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    function: &str,
    block: usize,
    index: usize,
    statement: &rustc_middle::mir::Statement<'tcx>,
    definitions: &mut Vec<Value>,
    uses: &mut Vec<Value>,
    memory_accesses: &mut Vec<Value>,
) -> Value {
    let id = format!("{function}:bb{block}:stmt{index}");
    let span = span_json(&source_span(tcx, statement.source_info.span));
    let assignment = match &statement.kind {
        StatementKind::Assign(assignment) => assignment,
        StatementKind::StorageLive(local) => {
            return json!({"id": id, "kind": "storage_live", "local": format!("_{}", local.index()), "span": span});
        }
        StatementKind::StorageDead(local) => {
            return json!({"id": id, "kind": "storage_dead", "local": format!("_{}", local.index()), "span": span});
        }
        StatementKind::Intrinsic(intrinsic) => {
            if let NonDivergingIntrinsic::Assume(operand) = &**intrinsic {
                let mut operation_uses = Vec::new();
                record_operand_use(
                    tcx,
                    body,
                    operand,
                    &id,
                    "condition",
                    uses,
                    memory_accesses,
                    &mut operation_uses,
                );
                return json!({"id": id, "kind": "assume", "uses": operation_uses, "span": span});
            }
            return json!({"id": id, "kind": "unsupported", "mir_kind": format!("{:?}", statement.kind), "span": span});
        }
        _ => {
            return json!({"id": id, "kind": "unsupported", "mir_kind": format!("{:?}", statement.kind), "span": span});
        }
    };
    let (destination, rvalue) = &**assignment;
    let definition = json!({
        "id": format!("{id}:def"),
        "operation": id,
        "place": place_json(tcx, body, *destination),
        "role": "assignment",
    });
    definitions.push(definition.clone());
    record_memory_access(tcx, body, *destination, &id, "write", memory_accesses);
    let mut operation_uses = Vec::new();
    collect_rvalue_uses(
        tcx,
        body,
        rvalue,
        &id,
        uses,
        memory_accesses,
        &mut operation_uses,
    );
    json!({
        "id": id,
        "kind": "assignment",
        "position": index,
        "defines": [definition],
        "expression": rvalue_json(tcx, body, rvalue),
        "uses": operation_uses,
        "span": span,
    })
}

fn terminator_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    function: &str,
    block: usize,
    terminator: &rustc_middle::mir::Terminator<'tcx>,
    definitions: &mut Vec<Value>,
    uses: &mut Vec<Value>,
    memory_accesses: &mut Vec<Value>,
) -> Value {
    let id = format!("{function}:bb{block}:term");
    let mut operation_uses = Vec::new();
    let mut operation_definitions = Vec::new();
    let mut data = Value::Null;
    match &terminator.kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => {
            data = json!({
                "callee": operand_json(tcx, body, func),
                "arguments": args.iter().map(|argument| operand_json(tcx, body, &argument.node)).collect::<Vec<_>>(),
                "destination": place_json(tcx, body, *destination),
            });
            record_operand_use(
                tcx,
                body,
                func,
                &id,
                "callee",
                uses,
                memory_accesses,
                &mut operation_uses,
            );
            for (index, argument) in args.iter().enumerate() {
                record_operand_use(
                    tcx,
                    body,
                    &argument.node,
                    &id,
                    &format!("argument_{index}"),
                    uses,
                    memory_accesses,
                    &mut operation_uses,
                );
            }
            if target.is_some() {
                let definition = json!({
                    "id": format!("{id}:def"),
                    "operation": id,
                    "place": place_json(tcx, body, *destination),
                    "role": "return_value",
                });
                definitions.push(definition.clone());
                operation_definitions.push(definition);
                record_memory_access(tcx, body, *destination, &id, "write", memory_accesses);
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => {
            data = json!({"discriminant": operand_json(tcx, body, discr)});
            record_operand_use(
                tcx,
                body,
                discr,
                &id,
                "discriminant",
                uses,
                memory_accesses,
                &mut operation_uses,
            );
        }
        TerminatorKind::Assert {
            cond,
            expected,
            msg,
            ..
        } => {
            data = json!({
                "condition": operand_json(tcx, body, cond),
                "expected": expected,
                "failure_kind": classify_assert(msg),
            });
            record_operand_use(
                tcx,
                body,
                cond,
                &id,
                "condition",
                uses,
                memory_accesses,
                &mut operation_uses,
            );
        }
        TerminatorKind::Drop { place, .. } => {
            record_place_use(
                tcx,
                body,
                *place,
                &id,
                "drop",
                uses,
                memory_accesses,
                &mut operation_uses,
            );
        }
        _ => {}
    }
    json!({
        "id": id,
        "kind": terminator_kind(terminator),
        "defines": operation_definitions,
        "uses": operation_uses,
        "data": data,
    })
}

fn place_json<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, place: Place<'tcx>) -> Value {
    let projections = place
        .projection
        .iter()
        .map(|projection| match projection {
            ProjectionElem::Deref => json!({"kind": "deref"}),
            ProjectionElem::Field(field, ty) => json!({
                "kind": "field",
                "index": field.index(),
                "type": type_json(tcx, ty),
            }),
            ProjectionElem::Index(local) => json!({"kind": "index", "local": format!("_{}", local.index())}),
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => json!({
                "kind": "constant_index", "offset": offset, "min_length": min_length, "from_end": from_end,
            }),
            ProjectionElem::Subslice { from, to, from_end } => json!({
                "kind": "subslice", "from": from, "to": to, "from_end": from_end,
            }),
            ProjectionElem::Downcast(name, variant) => json!({
                "kind": "downcast", "name": name.map(|name| name.to_string()), "variant": variant.index(),
            }),
            ProjectionElem::OpaqueCast(ty) => json!({"kind": "opaque_cast", "type": type_json(tcx, ty)}),
            ProjectionElem::UnwrapUnsafeBinder(ty) => {
                json!({"kind": "unwrap_unsafe_binder", "type": type_json(tcx, ty)})
            }
        })
        .collect::<Vec<_>>();
    json!({
        "kind": "place",
        "local": format!("_{}", place.local.index()),
        "projections": projections,
        "type": type_json(tcx, place.ty(body, tcx).ty),
    })
}

fn operand_json<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, operand: &Operand<'tcx>) -> Value {
    match operand {
        Operand::Copy(place) => json!({"kind": "copy", "place": place_json(tcx, body, *place)}),
        Operand::Move(place) => json!({"kind": "move", "place": place_json(tcx, body, *place)}),
        Operand::Constant(constant) => json!({
            "kind": "constant",
            "type": type_json(tcx, constant.const_.ty()),
            "value": format!("{:?}", constant.const_),
        }),
        Operand::RuntimeChecks(checks) => {
            json!({"kind": "runtime_checks", "value": format!("{checks:?}")})
        }
    }
}

fn rvalue_json<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, rvalue: &Rvalue<'tcx>) -> Value {
    match rvalue {
        Rvalue::Use(operand, retag) => json!({
            "kind": "use", "operand": operand_json(tcx, body, operand), "retag": format!("{retag:?}"),
        }),
        Rvalue::Repeat(operand, count) => json!({
            "kind": "repeat", "operand": operand_json(tcx, body, operand), "count": format!("{count}"),
        }),
        Rvalue::BinaryOp(operation, operands) => json!({
            "kind": if operation.is_overflowing() { "checked_binary" } else { "binary" },
            "operation": format!("{operation:?}").to_lowercase(),
            "result_projection": operation.is_overflowing().then_some(0),
            "overflow_projection": operation.is_overflowing().then_some(1),
            "operands": [operand_json(tcx, body, &operands.0), operand_json(tcx, body, &operands.1)],
        }),
        Rvalue::UnaryOp(operation, operand) => json!({
            "kind": "unary",
            "operation": format!("{operation:?}").to_lowercase(),
            "operand": operand_json(tcx, body, operand),
        }),
        Rvalue::Cast(kind, operand, ty) => json!({
            "kind": "cast",
            "cast_kind": format!("{kind:?}"),
            "operand": operand_json(tcx, body, operand),
            "type": type_json(tcx, *ty),
        }),
        Rvalue::Ref(_, kind, place) => json!({
            "kind": "reference",
            "borrow_kind": format!("{kind:?}"),
            "place": place_json(tcx, body, *place),
        }),
        Rvalue::RawPtr(kind, place) => json!({
            "kind": "raw_pointer",
            "mutability": format!("{kind:?}"),
            "place": place_json(tcx, body, *place),
        }),
        Rvalue::Discriminant(place) => {
            json!({"kind": "discriminant", "place": place_json(tcx, body, *place)})
        }
        Rvalue::CopyForDeref(place) => {
            json!({"kind": "copy_for_deref", "place": place_json(tcx, body, *place)})
        }
        Rvalue::WrapUnsafeBinder(operand, ty) => json!({
            "kind": "wrap_unsafe_binder", "operand": operand_json(tcx, body, operand), "type": type_json(tcx, *ty),
        }),
        Rvalue::Reborrow(ty, mutability, place) => json!({
            "kind": "reborrow",
            "type": type_json(tcx, *ty),
            "mutability": format!("{mutability:?}"),
            "place": place_json(tcx, body, *place),
        }),
        Rvalue::Aggregate(kind, operands) => json!({
            "kind": "aggregate",
            "aggregate_kind": format!("{kind:?}"),
            "operands": operands.iter().map(|operand| operand_json(tcx, body, operand)).collect::<Vec<_>>(),
        }),
        _ => json!({"kind": "unsupported", "mir_kind": format!("{rvalue:?}")}),
    }
}

fn collect_rvalue_uses<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rvalue: &Rvalue<'tcx>,
    operation: &str,
    uses: &mut Vec<Value>,
    memory_accesses: &mut Vec<Value>,
    operation_uses: &mut Vec<Value>,
) {
    match rvalue {
        Rvalue::Use(operand, _)
        | Rvalue::Repeat(operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(_, operand, _)
        | Rvalue::WrapUnsafeBinder(operand, _) => {
            record_operand_use(
                tcx,
                body,
                operand,
                operation,
                "operand",
                uses,
                memory_accesses,
                operation_uses,
            );
        }
        Rvalue::BinaryOp(_, operands) => {
            record_operand_use(
                tcx,
                body,
                &operands.0,
                operation,
                "left_operand",
                uses,
                memory_accesses,
                operation_uses,
            );
            record_operand_use(
                tcx,
                body,
                &operands.1,
                operation,
                "right_operand",
                uses,
                memory_accesses,
                operation_uses,
            );
        }
        Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::CopyForDeref(place)
        | Rvalue::Reborrow(_, _, place) => {
            record_place_use(
                tcx,
                body,
                *place,
                operation,
                "place",
                uses,
                memory_accesses,
                operation_uses,
            );
        }
        Rvalue::Aggregate(_, operands) => {
            for (index, operand) in operands.iter().enumerate() {
                record_operand_use(
                    tcx,
                    body,
                    operand,
                    operation,
                    &format!("field_{index}"),
                    uses,
                    memory_accesses,
                    operation_uses,
                );
            }
        }
        _ => {}
    }
}

fn record_operand_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
    operation: &str,
    role: &str,
    uses: &mut Vec<Value>,
    memory_accesses: &mut Vec<Value>,
    operation_uses: &mut Vec<Value>,
) {
    if let Operand::Copy(place) | Operand::Move(place) = operand {
        record_place_use(
            tcx,
            body,
            *place,
            operation,
            role,
            uses,
            memory_accesses,
            operation_uses,
        );
    }
}

fn record_place_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: Place<'tcx>,
    operation: &str,
    role: &str,
    uses: &mut Vec<Value>,
    memory_accesses: &mut Vec<Value>,
    operation_uses: &mut Vec<Value>,
) {
    let record = json!({
        "id": format!("{operation}:use{}", operation_uses.len()),
        "operation": operation,
        "place": place_json(tcx, body, place),
        "role": role,
    });
    uses.push(record.clone());
    operation_uses.push(record);
    record_memory_access(tcx, body, place, operation, "read", memory_accesses);
}

fn record_memory_access<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: Place<'tcx>,
    operation: &str,
    kind: &str,
    memory_accesses: &mut Vec<Value>,
) {
    if !place.projection.is_empty() {
        memory_accesses.push(json!({
            "id": format!("{operation}:memory{}", memory_accesses.len()),
            "operation": operation,
            "kind": kind,
            "place": place_json(tcx, body, place),
        }));
    }
}

fn propagate_panics(panic_sites: &[PanicSite], calls: &[CallSite]) -> Vec<FunctionAnalysis> {
    let mut paths = HashMap::new();

    for site in panic_sites {
        paths.entry(site.function.clone()).or_insert_with(|| {
            let target = site.callee.clone().unwrap_or_else(|| site.kind.clone());
            vec![site.function.clone(), target]
        });
    }
    for call in calls {
        let Some(callee) = &call.callee else {
            continue;
        };
        // Dependency MIR is unavailable here, so known helpers rely on exact names.
        // This can miss other helpers or break when compiler names change.
        // TODO: Import dependency panic summaries keyed by compiler identities.
        if call.is_panic_sink || is_known_panic_helper(callee) {
            paths
                .entry(call.caller.clone())
                .or_insert_with(|| vec![call.caller.clone(), callee.clone()]);
        }
    }

    // Propagate panic reachability backward through direct calls.
    loop {
        let mut changed = false;
        for call in calls {
            let Some(callee) = &call.callee else {
                continue;
            };
            let Some(callee_path) = paths.get(callee).cloned() else {
                continue;
            };
            if !paths.contains_key(&call.caller) {
                let mut path = vec![call.caller.clone()];
                path.extend(callee_path);
                paths.insert(call.caller.clone(), path);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut functions = BTreeSet::new();
    for call in calls {
        functions.insert(call.caller.clone());
    }
    for site in panic_sites {
        functions.insert(site.function.clone());
    }
    functions
        .into_iter()
        .map(|function| FunctionAnalysis {
            panic_path: paths.get(&function).cloned().unwrap_or_default(),
            may_panic: paths.contains_key(&function),
            function,
        })
        .collect()
}

fn is_known_panic_helper(callee: &str) -> bool {
    matches!(
        callee,
        "core::panicking::assert_failed"
            | "core::option::unwrap_failed"
            | "core::result::unwrap_failed"
            | "core::panicking::panic"
            | "core::panicking::panic_fmt"
    )
}

fn is_panic_sink(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    matches!(
        tcx.as_lang_item(def_id),
        Some(
            LangItem::Panic
                | LangItem::PanicNounwind
                | LangItem::PanicFmt
                | LangItem::PanicDisplay
                | LangItem::ConstPanicFmt
                | LangItem::PanicBoundsCheck
                | LangItem::PanicMisalignedPointerDereference
                | LangItem::PanicImpl
                | LangItem::PanicCannotUnwind
                | LangItem::PanicInCleanup
                | LangItem::PanicAddOverflow
                | LangItem::PanicSubOverflow
                | LangItem::PanicMulOverflow
                | LangItem::PanicDivOverflow
                | LangItem::PanicRemOverflow
                | LangItem::PanicNegOverflow
                | LangItem::PanicShrOverflow
                | LangItem::PanicShlOverflow
                | LangItem::PanicDivZero
                | LangItem::PanicRemZero
                | LangItem::PanicCoroutineResumed
                | LangItem::PanicAsyncFnResumed
                | LangItem::PanicAsyncGenFnResumed
                | LangItem::PanicGenFnNone
                | LangItem::PanicCoroutineResumedPanic
                | LangItem::PanicAsyncFnResumedPanic
                | LangItem::PanicAsyncGenFnResumedPanic
                | LangItem::PanicGenFnNonePanic
                | LangItem::PanicNullPointerDereference
                | LangItem::PanicInvalidEnumConstruction
                | LangItem::PanicCoroutineResumedDrop
                | LangItem::PanicAsyncFnResumedDrop
                | LangItem::PanicAsyncGenFnResumedDrop
                | LangItem::PanicGenFnNoneDrop
                | LangItem::BeginPanic
        )
    )
}

fn compiler_info() -> Compiler {
    let version = rustc_interface::util::rustc_version_str().unwrap_or("unknown");
    let release = version
        .split_whitespace()
        .next()
        .unwrap_or("unknown")
        .into();
    let commit = version
        .split_once('(')
        .and_then(|(_, value)| value.split_whitespace().next())
        .unwrap_or("")
        .into();
    Compiler { release, commit }
}

fn analysis_json(analysis: &Analysis) -> Value {
    let panic_sites: Vec<Value> = analysis
        .panic_sites
        .iter()
        .map(|site| {
            json!({
                "id": site.id,
                "kind": site.kind,
                "function": site.function,
                "span": {
                    "file": site.span.file,
                    "line": site.span.line,
                    "column": site.span.column,
                },
                "mir_location": {
                    "basic_block": site.mir_location.basic_block,
                    "terminator": site.mir_location.terminator,
                },
                "condition": site.condition,
                "expected": site.expected,
                "callee": site.callee,
            })
        })
        .collect();
    let unsafe_blocks: Vec<Value> = analysis
        .unsafe_blocks
        .iter()
        .map(|block| {
            json!({
                "id": block.id,
                "kind": "explicit_unsafe_block",
                "function": block.function,
                "hir_id": block.hir_id,
                "span": {
                    "file": block.span.file,
                    "line": block.span.line,
                    "column": block.span.column,
                },
            })
        })
        .collect();
    let calls: Vec<Value> = analysis
        .calls
        .iter()
        .map(|call| {
            json!({
                "id": call.id,
                "caller": call.caller,
                "call_kind": call.call_kind,
                "callee": call.callee,
                "function_operand": call.function_operand,
                "arguments": call.arguments,
                "destination": call.destination,
                "target": call.target,
                "unwind": call.unwind,
                "is_panic_sink": call.is_panic_sink,
                "span": {
                    "file": call.span.file,
                    "line": call.span.line,
                    "column": call.span.column,
                },
                "mir_location": {
                    "basic_block": call.mir_location.basic_block,
                    "terminator": call.mir_location.terminator,
                },
            })
        })
        .collect();
    let functions: Vec<Value> = analysis
        .functions
        .iter()
        .map(|function| {
            json!({
                "function": function.function,
                "may_panic": function.may_panic,
                "panic_path": function.panic_path,
            })
        })
        .collect();
    json!({
        "crate": analysis.crate_name,
        "compiler": {
            "release": analysis.compiler.release,
            "commit": analysis.compiler.commit,
        },
        "panic_sites": panic_sites,
        "unsafe_blocks": unsafe_blocks,
        "calls": calls,
        "functions": functions,
    })
}

fn analyze_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    function: &str,
    sites: &mut Vec<PanicSite>,
    calls: &mut Vec<CallSite>,
) {
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let Some(terminator) = &data.terminator else {
            continue;
        };

        match &terminator.kind {
            TerminatorKind::Assert {
                cond,
                expected,
                msg,
                ..
            } => sites.push(PanicSite {
                id: String::new(),
                kind: classify_assert(msg).into(),
                function: function.into(),
                span: source_span(tcx, terminator.source_info.span),
                mir_location: MirLocation {
                    basic_block: block.index(),
                    terminator: true,
                },
                condition: Some(format!("{cond:?}")),
                expected: Some(*expected),
                callee: None,
            }),
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => {
                let callee = direct_callee(tcx, body, func);
                let is_panic_sink = callee.is_some_and(|def_id| is_panic_sink(tcx, def_id));
                let callee = callee.map(|def_id| tcx.def_path_str(def_id));
                calls.push(CallSite {
                    id: String::new(),
                    caller: function.into(),
                    call_kind: if callee.is_some() {
                        "direct"
                    } else {
                        "indirect"
                    }
                    .into(),
                    callee: callee.clone(),
                    function_operand: format!("{func:?}"),
                    arguments: args
                        .iter()
                        .map(|argument| format!("{:?}", argument.node))
                        .collect(),
                    destination: format!("{destination:?}"),
                    target: target.map(|block| block.index()),
                    unwind: format!("{unwind:?}"),
                    is_panic_sink,
                    span: source_span(tcx, terminator.source_info.span),
                    mir_location: MirLocation {
                        basic_block: block.index(),
                        terminator: true,
                    },
                });
                if is_panic_sink {
                    sites.push(PanicSite {
                        id: String::new(),
                        kind: "explicit_panic".into(),
                        function: function.into(),
                        span: source_span(tcx, terminator.source_info.span),
                        mir_location: MirLocation {
                            basic_block: block.index(),
                            terminator: true,
                        },
                        condition: None,
                        expected: None,
                        callee,
                    });
                }
            }
            _ => {}
        }
    }
}

fn direct_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<rustc_span::def_id::DefId> {
    match operand.ty(body, tcx).kind() {
        ty::FnDef(def_id, _) => Some(*def_id),
        _ => None,
    }
}

fn classify_assert<O>(message: &AssertKind<O>) -> &'static str {
    match message {
        AssertKind::BoundsCheck { .. } => "bounds_check",
        AssertKind::Overflow(..) | AssertKind::OverflowNeg(..) => "arithmetic_overflow",
        AssertKind::DivisionByZero(..) => "division_by_zero",
        AssertKind::RemainderByZero(..) => "remainder_by_zero",
        AssertKind::MisalignedPointerDereference { .. } => "misaligned_pointer_dereference",
        AssertKind::NullPointerDereference => "null_pointer_dereference",
        _ => "assertion",
    }
}
