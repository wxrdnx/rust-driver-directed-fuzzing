use super::*;
use crate::util::unwind_target;
use rustc_middle::ty::{IntTy, Ty, TyKind, UintTy};
use serde_json::{json, Value};

fn span_json(span: &SourceSpan) -> Value {
    json!({"file": span.file, "line": span.line, "column": span.column})
}

fn type_json(tcx: TyCtxt<'_>, ty: Ty<'_>) -> Value {
    let integer = match ty.kind() {
        TyKind::Int(kind) => Some((true, int_bits(tcx, *kind))),
        TyKind::Uint(kind) => Some((false, uint_bits(tcx, *kind))),
        _ => None,
    };

    if let Some((signed, bits)) = integer {
        return json!({"kind": "integer", "signed": signed, "bits": bits, "rust": format!("{ty}")});
    }

    match ty.kind() {
        TyKind::Bool => json!({"kind": "boolean", "rust": format!("{ty}")}),
        TyKind::RawPtr(pointer, mutability) => json!({
            "kind": "raw_pointer",
            "bits": tcx.data_layout.pointer_size().bits(),
            "mutable": mutability.is_mut(),
            "pointee": format!("{pointer}"),
            "rust": format!("{ty}"),
        }),
        TyKind::Ref(_, pointee, mutability) => json!({
            "kind": "reference",
            "bits": tcx.data_layout.pointer_size().bits(),
            "mutable": mutability.is_mut(),
            "pointee": format!("{pointee}"),
            "rust": format!("{ty}"),
        }),
        _ => json!({"kind": "other", "rust": format!("{ty}")}),
    }
}

fn add_cfg_edge(edges: &mut Vec<Value>, source: usize, target: usize, kind: &str, fields: Option<Value>) {
    let mut edge = json!({
        "source": format!("bb{source}"),
        "target": format!("bb{target}"),
        "kind": kind,
    });

    if let Some(Value::Object(fields)) = fields {
        if let Value::Object(edge) = &mut edge {
            edge.extend(fields);
        }
    }

    edges.push(edge);
}

fn int_bits(tcx: TyCtxt<'_>, kind: IntTy) -> u64 {
    match kind {
        IntTy::I8 => 8,
        IntTy::I16 => 16,
        IntTy::I32 => 32,
        IntTy::I64 => 64,
        IntTy::I128 => 128,
        IntTy::Isize => tcx.data_layout.pointer_size().bits(),
    }
}

fn uint_bits(tcx: TyCtxt<'_>, kind: UintTy) -> u64 {
    match kind {
        UintTy::U8 => 8,
        UintTy::U16 => 16,
        UintTy::U32 => 32,
        UintTy::U64 => 64,
        UintTy::U128 => 128,
        UintTy::Usize => tcx.data_layout.pointer_size().bits(),
    }
}

pub(super) fn mir_cfg<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, function: &str, def_id: DefId) -> Value {

    let mut blocks = Vec::new();
    let mut edges = Vec::new();
    let mut definitions = Vec::new();
    let mut uses = Vec::new();
    let mut memory_accesses = Vec::new();
    // This CFG function ID has the same format as the call record's callee ID
    let function_id = function_id(tcx, def_id);
    let def_index = def_id.index.as_u32();
    let crate_name = tcx.crate_name(def_id.krate).to_string();

    // For generic functions, each one has a different linkage symbol
    // So asking for the symbol of unresolved functions would be ambiguous
    // For this case linkage_name is set to None

    // The function requires_monomorphization checks whether there are definitions that contains
    // generic parameters that need to be replaced with concrete types
    let linkage_name = if tcx.generics_of(def_id).requires_monomorphization(tcx) {
        None
    } else {
        Some(tcx.symbol_name(ty::Instance::mono(tcx, def_id)).name.to_string())
    };

    let locals = locals_json(tcx, body);

    for (block, data) in body.basic_blocks.iter_enumerated() {
        let terminator = data.terminator();
        let span = source_span(tcx, terminator.source_info.span);
        let statements: Vec<_> = data
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
            .collect();

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

        // CFG edges
        match &terminator.kind {
            TerminatorKind::Goto { target } => {
                add_cfg_edge(&mut edges, block.index(), target.index(), "goto", None)
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                // SwitchInt follows the matching value, or otherwise when no value matches
                // e.g. switchInt(value) -> [0: bb1, 1: bb2, otherwise: bb3]
                // value 0 follows bb1, value 1 follows bb2, and every other value follows bb3

                // Handle explicit definitions (the non-otherwise case)
                for (value, target) in targets.iter() {
                    edges.push(json!({
                        "source": format!("bb{}", block.index()),
                        "target": format!("bb{}", target.index()),
                        "kind": "switch_case",
                        "value": value.to_string(),
                        "condition": operand_json(tcx, body, discr),
                    }));
                }

                // Handle the fallback definition (the otherwise case)
                edges.push(json!({
                    "source": format!("bb{}", block.index()),
                    "target": format!("bb{}", targets.otherwise().index()),
                    "kind": "switch_default",
                    "condition": operand_json(tcx, body, discr),
                }));
            }
            TerminatorKind::Call { target, unwind, .. } => {
                // Here we handle functions that return normally
                // e.g.
                // bb0 call helper() -> helper returns -> bb1 follows after bb0
                // Then it adds
                // {
                //     "source": "bb0",
                //     "target": "bb1",
                //     "kind": "call_return" ,
                // }
                if let Some(target) = target {
                    add_cfg_edge(
                        &mut edges,
                        block.index(),
                        target.index(),
                        "call_return",
                        None,
                    );
                }
                // Some functions never return
                // e.g.
                // bb0 call helper() -> helper panics -> bb2 cleanup local variables
                // Then it adds
                // {
                //     "source": "bb0",
                //     "target": "bb2",
                //     "kind": "unwind" ,
                // }
                if let Some(target) = unwind_target(unwind) {
                    add_cfg_edge(&mut edges, block.index(), target.index(), "unwind", None);
                }
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                unwind,
                ..
            } => {
                // Assert is similar to
                // if condition == expected {
                //     // continue
                // }
                // else {
                //     // panic
                // }
                // e.g. assert!(size > 0)
                // produces MIR similar to
                // assert(_1 > 0) -> [success: bb1, unwind: bb2]
                let condition =
                    Some(json!({"condition": operand_json(tcx, body, cond), "expected": expected}));
                add_cfg_edge(
                    &mut edges,
                    block.index(),
                    target.index(),
                    "assert_success",
                    condition,
                );
                if let Some(target) = unwind_target(unwind) {
                    add_cfg_edge(&mut edges, block.index(), target.index(), "unwind", None);
                }
            }
            TerminatorKind::Drop { target, unwind, .. } => {
                // Drop runs the value's destructor and then follows the return target
                // e.g. drop(_1) -> [return: bb1, unwind: bb2]
                // bb1 follows when the destructor finishes, while bb2 handles a panic during drop
                add_cfg_edge(
                    &mut edges,
                    block.index(),
                    target.index(),
                    "drop_return",
                    None,
                );

                if let Some(target) = unwind_target(unwind) {
                    add_cfg_edge(&mut edges, block.index(), target.index(), "unwind", None);
                }
            }
            _ => {
                for target in terminator.successors() {
                    add_cfg_edge(&mut edges, block.index(), target.index(), "successor", None);
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
            "linkage_name": linkage_name,
            "language": "rust",
            "representation": "mir",
            "module": crate_name,
            "entry_block": "bb0",
        },
        "blocks": blocks,
        "edges": edges,
        "locals": locals,
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
            let argument_index = match index {
                // MIR starts at index 1
                index if index > 0 && index <= body.arg_count => Some(index - 1),
                _ => None,
            };
            let kind = if index == 0 { "return" } else if index <= body.arg_count { "argument" } else { "local" };
            let local_type = type_json(tcx, declaration.ty);
            let span = span_json(&source_span(tcx, declaration.source_info.span));

            json!({
                "id": format!("_{index}"),
                "kind": kind,
                "argument_index": argument_index,
                "type": local_type,
                "span": span,
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
        // StorageLive means rustc started the lifetime
        // It is used in use-def analyis to clear old definitions
        StatementKind::StorageLive(local) => {
            return json!({"id": id, "kind": "storage_live", "local": format!("_{}", local.index()), "span": span});
        }
        // StorageDead means the storage lifetime has ended
        // It is used in use-def analysis to clear definitions after a lifetime ends
        StatementKind::StorageDead(local) => {
            return json!({"id": id, "kind": "storage_dead", "local": format!("_{}", local.index()), "span": span});
        }
        // Intrinsic are special operations used by rustc internally

        // This information is not used in def-use analysis
        // But we still keep it in case it'll be used in the future
        StatementKind::Intrinsic(intrinsic) => {
            if let NonDivergingIntrinsic::Assume(operand) = intrinsic.as_ref() {
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

    let (destination, rvalue) = assignment.as_ref();
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
        // Call reads callee and arguments and define the destination
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => {
            let callee = direct_instance(tcx, body, func);
            let callee_id = callee.map(|instance| function_id(tcx, instance.def_id()));

            let callee_instance =
                callee.map(|instance| tcx.def_path_str_with_args(instance.def_id(), instance.args));

            let intrinsic = callee
                .and_then(|instance| tcx.intrinsic(instance.def_id()))
                .map(|intrinsic| intrinsic.name.to_string());

            data = json!({
                "callee": operand_json(tcx, body, func),
                "callee_id": callee_id,
                "callee_instance": callee_instance,
                "intrinsic": intrinsic,
                "arguments": args.iter().map(|argument| operand_json(tcx, body, &argument.node)).collect::<Vec<Value>>(),
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
        // SwitchInt reads discriminant that choose the next basic blocks
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
        // Assert continues only the condition holds
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
        // Drop reads the value before being destroyed
        // This happens before moving to the target block
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
        // Return reads _0 because MIR stores the return value in _0
        // Use !body.return_ty().is_unit() to not treat a unit return value () as a meaningful data
        TerminatorKind::Return if !body.return_ty().is_unit() => {
            record_place_use(
                tcx,
                body,
                Place::from(RETURN_PLACE),
                &id,
                "return_value",
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
    let projections: Vec<Value> = place
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

            // Const indices may count from either end 
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => json!({
                "kind": "constant_index", "offset": offset, "min_length": min_length, "from_end": from_end,
            }),

            // Subslice bounds may also count backwards from the end
            ProjectionElem::Subslice { from, to, from_end } => json!({
                "kind": "subslice", "from": from, "to": to, "from_end": from_end,
            }),

            // Downcast selects one enum or one of the coroutine
            ProjectionElem::Downcast(name, variant) => json!({
                "kind": "downcast", "name": name.map(|name| name.to_string()), "variant": variant.index(),
            }),

            // Opaque casts changes opaque typed to known type
            // It does not change the storage
            // So we only record the new type
            ProjectionElem::OpaqueCast(ty) => json!({"kind": "opaque_cast", "type": type_json(tcx, ty)}),

            // UnsafeBinder is experimental
            // Currently UnsafeBinder is not used in our analysis
            // But we still record it in case it is used in the future
            ProjectionElem::UnwrapUnsafeBinder(ty) => {
                json!({"kind": "unwrap_unsafe_binder", "type": type_json(tcx, ty)})
            }
            // A phantom dereference represents an indirect place used during reborrowing
            ProjectionElem::PhantomDeref => json!({"kind": "phantom_deref"}),
        })
        .collect();
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
        // Constants may contain either ordinary values or function identities
        Operand::Constant(constant) => {
            let ty = constant.const_.ty();
            let function = match ty.kind() {
                ty::FnDef(def_id, _) => Some(function_id(tcx, *def_id)),
                _ => None,
            };

            // Only scalar types can be represented here
            let scalar = match ty.kind() {
                ty::Bool | ty::Int(_) | ty::Uint(_) | ty::RawPtr(_, _) | ty::Ref(_, _, _) => {
                    constant.const_.try_to_scalar_int().or_else(|| {
                        constant
                            .const_
                            .eval(tcx, body.typing_env(tcx), constant.span)
                            .ok()
                            .and_then(|value| value.try_to_scalar_int())
                    })
                }
                _ => None,
            };

            // Preserve the type even when rustc cant evaluate the value
            let value = match ty.kind() {
                ty::Bool => match scalar.and_then(|value| value.try_to_bool().ok()) {
                    Some(value) => json!({"kind": "boolean", "value": value}),
                    None => json!({"kind": "opaque"}),
                },
                ty::Int(_) => match scalar {
                    Some(value) => json!({
                        "kind": "integer",
                        "bits": value.size().bits(),
                        "signed": true,
                        "value": value.to_int(value.size()).to_string(),
                    }),
                    None => json!({"kind": "opaque"}),
                },
                ty::Uint(_) => match scalar {
                    Some(value) => json!({
                        "kind": "integer",
                        "bits": value.size().bits(),
                        "signed": false,
                        "value": value.to_uint(value.size()).to_string(),
                    }),
                    None => json!({"kind": "opaque"}),
                },
                ty::RawPtr(_, _) | ty::Ref(_, _, _) => match scalar {
                    Some(value) => json!({
                        "kind": "pointer",
                        "bits": value.size().bits(),
                        "value": value.to_uint(value.size()).to_string(),
                    }),
                    None => json!({"kind": "opaque"}),
                },
                _ => json!({"kind": "opaque"}),
            };

            json!({
                "kind": "constant",
                "type": type_json(tcx, ty),
                "value": value,
                "debug": format!("{:?}", constant.const_),
                "function_id": function,
            })
        }

        // Runtime checks are compiler generated checks
        // This information is currently not used in our analysis
        // We simply store the debug string
        // TODO: may be redundant, perhaps we can remove it

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
        // Checked arithmetic returns both the result and an overflow flag
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

        // Discriminant identifies the enum or coroutine
        Rvalue::Discriminant(place) => {
            json!({"kind": "discriminant", "place": place_json(tcx, body, *place)})
        }

        // Rustc uses this temporary copy before dereferencing
        Rvalue::CopyForDeref(place) => {
            json!({"kind": "copy_for_deref", "place": place_json(tcx, body, *place)})
        }

        // UnsafeBinder is experimental
        // Currently UnsafeBinder is not used in our analysis
        // But we still record it in case it is used in the future
        Rvalue::WrapUnsafeBinder(operand, ty) => json!({
            "kind": "wrap_unsafe_binder", "operand": operand_json(tcx, body, operand), "type": type_json(tcx, *ty),
        }),

        // Reborrow creates a new borrow
        // The original place is preserved
        Rvalue::Reborrow(ty, mutability, place) => json!({
            "kind": "reborrow",
            "type": type_json(tcx, *ty),
            "mutability": format!("{mutability:?}"),
            "place": place_json(tcx, body, *place),
        }),

        // Aggregates combine operands into struct, tuple, array, or enum value
        Rvalue::Aggregate(kind, operands) => json!({
            "kind": "aggregate",
            "aggregate_kind": format!("{kind:?}"),
            "operands": operands.iter().map(|operand| operand_json(tcx, body, operand)).collect::<Vec<Value>>(),
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
    // Finds MIR on the right hand side and record them as being used
    // e.g.,
    //     _3 = _1 + _2
    // The rvalue reads _1 and _2
    // The result would be something like:
    //     use of _1 with role left_operand
    //     use of _2 with role right_operand

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
    let place_value = place_json(tcx, body, place);

    let record = json!({
        "id": format!("{operation}:use{}", operation_uses.len()),
        "operation": operation,
        "place": place_value,
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
        let place = place_json(tcx, body, place);

        memory_accesses.push(json!({
            "id": format!("{operation}:memory{}", memory_accesses.len()),
            "operation": operation,
            "kind": kind,
            "place": place,
        }));
    }
}

pub(super) fn analysis_json(analysis: &Analysis) -> Value {
    let panic_sites: Vec<Value> = analysis
        .panic_sites
        .iter()
        .map(|site| {
            json!({
                "id": site.id,
                "kind": site.kind,
                "function": site.function,
                "function_id": site.function_id,
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
                "caller_id": call.caller_id,
                "call_kind": call.call_kind,
                "callee": call.callee,
                "callee_id": call.callee_id,
                "callee_instance": call.callee_instance,
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
                "function_id": function.function_id,
                "may_panic": function.may_panic,
                "panic_path": function.panic_path,
            })
        })
        .collect();

    let callback_registrations: Vec<Value> = analysis
        .callback_registrations
        .iter()
        .map(|registration| {
            json!({
                "owner": registration.owner,
                "owner_id": registration.owner_id,
                "interface": registration.interface,
                "field": registration.field,
                "field_index": registration.field_index,
                "callback": registration.callback,
                "callback_id": registration.callback_id,
                "callback_instance": registration.callback_instance,
                "linkage_name": registration.linkage_name,
            })
        })
        .collect();

    json!({
        "crate": analysis.crate_name,
        "panic_sites": panic_sites,
        "unsafe_blocks": unsafe_blocks,
        "calls": calls,
        "callback_registrations": callback_registrations,
        "functions": functions,
    })
}
