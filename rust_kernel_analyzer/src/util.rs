use rustc_middle::mir::{BasicBlock, UnwindAction};
use rustc_middle::ty::{IntTy, Ty, TyCtxt, TyKind, UintTy};
use rustc_span::def_id::DefId;
use rustc_span::{Pos, Span};
use serde_json::{json, Value};

pub(crate) struct SourceSpan {
    pub(crate) file: String,
    pub(crate) line: usize,
    pub(crate) column: usize,
}

pub(crate) fn source_span(tcx: TyCtxt<'_>, span: Span) -> SourceSpan {
    let source_map = tcx.sess.source_map();
    let location = source_map.lookup_char_pos(span.source_callsite().lo());
    SourceSpan {
        file: source_map
            .filename_for_diagnostics(&location.file.name)
            .to_string(),
        line: location.line,
        column: location.col.to_usize() + 1,
    }
}

pub(crate) fn span_json(span: &SourceSpan) -> Value {
    json!({"file": span.file, "line": span.line, "column": span.column})
}

// This ID has the same format as the CFG function ID
pub(crate) fn function_id(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    let crate_name = tcx.crate_name(def_id.krate);
    let def_index = def_id.index.as_u32();
    let function = tcx.def_path_str(def_id);
    format!("rust:{crate_name}:{def_index}:{function}")
}

pub(crate) fn type_json(tcx: TyCtxt<'_>, ty: Ty<'_>) -> Value {
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

pub(crate) fn unwind_target(unwind: &UnwindAction) -> Option<BasicBlock> {
    match unwind {
        UnwindAction::Cleanup(target) => Some(*target),
        _ => None,
    }
}

pub(crate) fn push_edge(
    edges: &mut Vec<Value>,
    source: usize,
    target: usize,
    kind: &str,
    fields: Option<Value>,
) {
    let mut edge = json!({
        "source": format!("bb{source}"),
        "target": format!("bb{target}"),
        "kind": kind,
    });
    if let (Value::Object(edge), Some(Value::Object(fields))) = (&mut edge, fields) {
        edge.extend(fields);
    }
    edges.push(edge);
}

pub(crate) fn sanitize(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '-' || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect()
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
