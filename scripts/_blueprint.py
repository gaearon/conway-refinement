#!/usr/bin/env python3
"""Internal source extractor for scripts/blueprint.sh."""

from __future__ import annotations

import argparse
import heapq
import json
import re
from dataclasses import dataclass
from pathlib import Path

from _blueprint_phases import PHASE_BY_KEY, PHASE_METADATA, PHASES, validate_lean_keys


ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / ".lake/build/blueprint/nodes.json"
CONTENT = ROOT / "blueprint/src/content.tex"

REF_RE = re.compile(r"\\(?:[Cc]ref|ref)\{([^{}]*)\}")
DEPENDENCY_TODO_PARAM = "FIXME_blueprint_review_why_does_proof_depend_on"

def tex_identifier(value: str) -> str:
    """Render a Lean identifier with safe, useful line-break opportunities in TeX."""

    escapes = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "#": r"\#",
        "$": r"\$",
        "_": r"\_\allowbreak{}",
        "{": r"\{",
        "}": r"\}",
        ".": r".\allowbreak{}",
        "₀": r"\ensuremath{_0}",
    }
    return "".join(escapes.get(character, character) for character in value)


@dataclass(frozen=True)
class Node:
    label: str
    declarations: tuple[str, ...]
    dependencies: frozenset[str]
    module: str
    source: Path
    source_line: int
    source_end_line: int
    source_order: int
    title: str | None
    phase: str
    has_proof_prose: bool
    proof_references: frozenset[str]
    statement: str
    proof: str
    highlight: bool


def shallow_dependencies(nodes: dict[str, Node]) -> dict[str, frozenset[str]]:
    """Dependencies left after contracting every path through another selected node."""

    def ancestors(label: str) -> set[str]:
        seen: set[str] = set()
        pending = list(nodes[label].dependencies)
        while pending:
            dependency = pending.pop()
            if dependency in seen:
                continue
            seen.add(dependency)
            pending.extend(nodes[dependency].dependencies)
        return seen

    ancestor_sets = {label: ancestors(label) for label in nodes}
    return {
        label: frozenset(
            dependency
            for dependency in node.dependencies
            if not any(
                dependency in ancestor_sets[other]
                for other in node.dependencies
                if other != dependency
            )
        )
        for label, node in nodes.items()
    }


def read_nodes() -> dict[str, Node]:
    validate_lean_keys(PHASE_METADATA)
    if not DATA.exists():
        raise SystemExit("blueprint: run `scripts/export-blueprint-data.py` first")

    records = json.loads(DATA.read_text())
    unknown_phases = sorted(
        {record["phase"] for record in records}.difference(PHASES)
    )
    if unknown_phases:
        raise SystemExit(
            "blueprint: selected declarations use unknown phases: "
            + ", ".join(unknown_phases)
        )
    names = {record["name"]: record["label"] for record in records}
    nodes: dict[str, Node] = {}
    ordered_records = sorted(
        records,
        key=lambda record: (
            PHASES.index(record["phase"]),
            record["source"],
            record["range"]["start"]["line"],
            record["name"],
        ),
    )
    for source_order, record in enumerate(ordered_records):
        label = record["label"]
        source = Path(record["source"])
        if not (ROOT / source).is_file():
            raise SystemExit(f"blueprint: node {label!r} points to missing Lean source: {source}")
        dependencies = frozenset(
            names[name]
            for name in record["statementDependencies"] + record["proofDependencies"]
        )
        proof = record["proof"]
        proof_references = frozenset(
            reference.strip()
            for group in REF_RE.findall(proof)
            for reference in group.split(",")
            if reference.strip()
        )
        if label in nodes:
            raise SystemExit(f"blueprint: duplicate label {label!r}")
        nodes[label] = Node(
            label=label,
            declarations=(record["name"],),
            dependencies=dependencies,
            module=record["module"],
            source=source,
            source_line=record["range"]["start"]["line"],
            source_end_line=record["range"]["end"]["line"],
            source_order=source_order,
            title=record["title"],
            phase=record["phase"],
            has_proof_prose=bool(proof.strip()),
            proof_references=proof_references,
            statement=record["statement"],
            proof=proof,
            highlight=record.get("highlight", False),
        )

    if not nodes:
        raise SystemExit("blueprint: checked metadata contains no selected nodes")
    unknown = sorted(
        dependency
        for node in nodes.values()
        for dependency in node.dependencies
        if dependency not in nodes
    )
    if unknown:
        raise SystemExit(
            f"blueprint: dependencies have no node: {', '.join(sorted(set(unknown)))}"
        )
    merged = sorted(
        (node.label, node.declarations)
        for node in nodes.values()
        if len(node.declarations) != 1
    )
    if merged:
        details = "; ".join(
            f"{label}: {', '.join(declarations) if declarations else 'no declaration'}"
            for label, declarations in merged
        )
        raise SystemExit(
            "blueprint: every node must contain exactly one Lean declaration: " + details
        )
    missing_proofs = sorted(
        node.label for node in nodes.values() if not node.has_proof_prose
    )
    if missing_proofs:
        raise SystemExit(
            "blueprint: nodes have no proof prose: " + ", ".join(missing_proofs)
        )
    return nodes


def project_imports() -> dict[str, frozenset[str]]:
    """Read the direct imports between modules in this repository."""

    import_pattern = re.compile(
        r"^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import"
        r"(?:[ \t]+|\r?\n[ \t]+)"
        r"(ConwayRefinement(?:\.[A-Za-z0-9_']+)*)[ \t]*\r?$",
        re.MULTILINE,
    )
    source_files = list((ROOT / "ConwayRefinement").rglob("*.lean"))
    source_files.extend(ROOT.glob("ConwayRefinement*.lean"))
    imports: dict[str, frozenset[str]] = {}
    for source in source_files:
        module = ".".join(source.relative_to(ROOT).with_suffix("").parts)
        imports[module] = frozenset(
            match.group(1) for match in import_pattern.finditer(source.read_text())
        )
    return imports


def later_phase_import_paths(
    module_phase: dict[str, str], phase_index: dict[str, int]
) -> list[tuple[tuple[str, ...], str, str]]:
    """Find paths by which a selected module imports a later selected phase."""

    imports = project_imports()
    backwards: list[tuple[tuple[str, ...], str, str]] = []
    for target, target_phase in module_phase.items():
        pending = [
            (dependency, (target, dependency))
            for dependency in imports.get(target, frozenset())
        ]
        seen: set[str] = set()
        while pending:
            source, path = pending.pop()
            if source in seen:
                continue
            seen.add(source)
            source_phase = module_phase.get(source)
            if (
                source_phase is not None
                and phase_index[source_phase] > phase_index[target_phase]
            ):
                backwards.append((path, target_phase, source_phase))
            pending.extend(
                (dependency, (*path, dependency))
                for dependency in imports.get(source, frozenset())
                if dependency not in seen
            )
    return sorted(backwards)


def validate_phase_contract(nodes: dict[str, Node]) -> None:
    """Enforce the linear reading order on declarations and project modules."""
    phases = {node.phase for node in nodes.values()}
    missing = [phase for phase in PHASES if phase not in phases]
    if missing:
        raise SystemExit(
            "blueprint: phases contain no selected declarations: " + ", ".join(missing)
        )
    phase_index = {phase: index for index, phase in enumerate(PHASES)}
    phases_by_module: dict[str, set[str]] = {}
    for node in nodes.values():
        phases_by_module.setdefault(node.module, set()).add(node.phase)
    split_modules = sorted(
        (module, sorted(phases, key=phase_index.__getitem__))
        for module, phases in phases_by_module.items()
        if len(phases) > 1
    )
    if split_modules:
        details = "; ".join(
            f"{module}: {', '.join(phases)}" for module, phases in split_modules
        )
        raise SystemExit("blueprint: selected modules are split between phases: " + details)
    backwards = sorted(
        (dependency, label)
        for label, node in nodes.items()
        for dependency in node.dependencies
        if phase_index[nodes[dependency].phase] > phase_index[node.phase]
    )
    if backwards:
        details = "; ".join(
            f"{dependency} ({nodes[dependency].phase}) -> {label} ({nodes[label].phase})"
            for dependency, label in backwards
        )
        raise SystemExit("blueprint: dependencies run backwards between phases: " + details)
    module_phase = {
        module: next(iter(phases)) for module, phases in phases_by_module.items()
    }
    backwards_imports = later_phase_import_paths(module_phase, phase_index)
    if backwards_imports:
        details = "; ".join(
            f"{' -> '.join(path)} imports {source_phase} from {target_phase}"
            for path, target_phase, source_phase in backwards_imports
        )
        raise SystemExit(
            "blueprint: project imports run backwards between phases: " + details
        )


def reference_mismatches(
    nodes: dict[str, Node],
) -> tuple[list[tuple[str, list[str]]], list[tuple[str, list[str]]]]:
    shallow = shallow_dependencies(nodes)
    missing_references = sorted(
        (node.label, sorted(shallow[node.label] - node.proof_references))
        for node in nodes.values()
        if shallow[node.label] - node.proof_references
    )
    unexpected_references = sorted(
        (node.label, sorted(node.proof_references - shallow[node.label]))
        for node in nodes.values()
        if node.proof_references - shallow[node.label]
    )
    return missing_references, unexpected_references


def annotation_bounds(node: Node, text: str) -> tuple[int, int, int, int]:
    """Return the annotation start, proof start, proof-comment end, and attribute end."""

    needle = f'blueprint "{node.label}"'
    marker = text.find(needle)
    if marker < 0:
        raise SystemExit(
            f"blueprint: cannot find source annotation for {node.label} in {node.source}"
        )
    start = text.rfind("@[", 0, marker)
    if start < 0:
        raise SystemExit(
            f"blueprint: cannot find start of source annotation for {node.label} in {node.source}"
        )
    proof_start = text.find("(proof := /--", start)
    if proof_start < 0:
        raise SystemExit(
            f"blueprint: cannot find source proof prose for {node.label} in {node.source}"
        )
    proof_end = text.find("-/", proof_start)
    if proof_end < 0:
        raise SystemExit(
            f"blueprint: cannot find end of source proof prose for {node.label} in {node.source}"
        )
    attribute_end = text.find("]", proof_end)
    if attribute_end < 0:
        raise SystemExit(
            f"blueprint: cannot find end of source annotation for {node.label} in {node.source}"
        )
    return start, proof_start, proof_end, attribute_end


def unresolved_reference_todo_files() -> list[str]:
    return sorted(
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "ConwayRefinement").rglob("*.lean")
        if DEPENDENCY_TODO_PARAM in path.read_text()
    )


def insert_reference_todos(
    nodes: dict[str, Node], missing_references: list[tuple[str, list[str]]]
) -> list[str]:
    """Insert durable review markers for missing immediate dependency explanations."""

    by_source: dict[Path, list[tuple[Node, list[str]]]] = {}
    for label, references in missing_references:
        by_source.setdefault(nodes[label].source, []).append((nodes[label], references))

    changed: list[str] = []
    for source, entries in by_source.items():
        path = ROOT / source
        text = path.read_text()
        insertions: list[tuple[int, str, str]] = []
        for node, references in entries:
            start, _, _, attribute_end = annotation_bounds(node, text)
            if DEPENDENCY_TODO_PARAM in text[start:attribute_end]:
                continue
            labels = ", ".join(references)
            marker = f'\n  ({DEPENDENCY_TODO_PARAM} := "{labels}")'
            insertions.append((attribute_end, marker, node.label))
        for position, marker, label in sorted(insertions, reverse=True):
            text = text[:position] + marker + text[position:]
            changed.append(label)
        if insertions:
            path.write_text(text)
    return sorted(changed)


def validate_reference_contract(nodes: dict[str, Node]) -> None:
    unresolved = unresolved_reference_todo_files()
    if unresolved:
        raise SystemExit(
            "blueprint: unresolved dependency TODO parameters in source: "
            + ", ".join(unresolved)
        )

    missing_references, unexpected_references = reference_mismatches(nodes)
    if not missing_references and not unexpected_references:
        return
    inserted = insert_reference_todos(nodes, missing_references)
    details = []
    details.extend(
        f"{label} misses {', '.join(references)}"
        for label, references in missing_references
    )
    details.extend(
        f"{label} cites non-dependencies {', '.join(references)}"
        for label, references in unexpected_references
    )
    raise SystemExit(
        "blueprint: proof references must equal shallow blueprint dependencies: "
        + "; ".join(details)
        + (
            "; inserted dependency-explanation TODOs in " + ", ".join(inserted)
            if inserted
            else ""
        )
    )


def topological_order(nodes: dict[str, Node]) -> tuple[list[str], list[str]]:
    incoming = {
        label: set(node.dependencies)
        for label, node in nodes.items()
    }
    outgoing = {label: set() for label in nodes}
    for label, dependencies in incoming.items():
        for dependency in dependencies:
            outgoing[dependency].add(label)

    ready = [
        (node.source_order, label)
        for label, node in nodes.items()
        if not incoming[label]
    ]
    heapq.heapify(ready)
    order: list[str] = []
    while ready:
        _, label = heapq.heappop(ready)
        order.append(label)
        for dependent in outgoing[label]:
            incoming[dependent].discard(label)
            if not incoming[dependent]:
                node = nodes[dependent]
                heapq.heappush(ready, (node.source_order, dependent))

    cyclic = sorted(set(nodes) - set(order), key=lambda label: nodes[label].source_order)
    order.extend(cyclic)
    return order, cyclic


def render_content(nodes: dict[str, Node]) -> str:
    order, cyclic = topological_order(nodes)
    if cyclic:
        raise SystemExit(f"blueprint: dependency graph is cyclic near {', '.join(cyclic)}")
    lines = [
        "% Generated by scripts/blueprint.sh; do not edit.",
        "% Run `scripts/blueprint.sh build` to rebuild this file.",
    ]
    lines.extend(
        f"\\mermaidsource{{{node.label}}}{{{node.source.as_posix()}}}{{{node.source_line}}}"
        f"{{{(node.title or '').encode().hex()}}}"
        f"{{{PHASE_BY_KEY[node.phase].title.encode().hex()}}}"
        for node in sorted(nodes.values(), key=lambda node: node.source_order)
    )
    lines.append("")

    by_section: dict[str, list[str]] = {}
    for label in order:
        by_section.setdefault(nodes[label].phase, []).append(label)
    for phase in PHASE_METADATA:
        labels = by_section.get(phase.key)
        if not labels:
            continue
        lines.extend([f"\\section{{{phase.title}}}", ""])
        for label in labels:
            node = nodes[label]
            declaration = tex_identifier(node.declarations[0])
            environment = label.split(":", 1)[0]
            environment = {
                "def": "definition",
                "thm": "theorem",
                "lem": "lemma",
                "prop": "proposition",
                "cor": "corollary",
                "fact": "fact",
            }[environment]
            dependencies = ",".join(sorted(node.dependencies))
            lines.extend(
                [
                    f"\\begin{{{environment}}}[{node.title}]",
                    f"\\label{{{label}}}",
                    f"\\lean{{{node.declarations[0]}}}",
                    "\\leanok",
                    node.statement,
                    f"\\end{{{environment}}}",
                    "\\begin{proof}",
                    *( [f"\\uses{{{dependencies}}}"] if dependencies else [] ),
                    "\\leanok",
                    node.proof,
                    "\\end{proof}",
                    f"\\blueprintsourcelink{{{label}}}{{{declaration}}}"
                    f"{{{node.source_end_line}}}",
                    "",
                ]
            )
    return "\n".join(lines)


def render_phase_report(nodes: dict[str, Node]) -> str:
    """Summarize each phase and the live frontier after it from the current reduced DAG."""

    shallow = shallow_dependencies(nodes)
    phase_index = {phase: index for index, phase in enumerate(PHASES)}
    lines = [f"Blueprint phases: {len(nodes)} selected results"]
    for index, phase in enumerate(PHASE_METADATA):
        local = [node for node in nodes.values() if node.phase == phase.key]
        modules = {node.module for node in local}
        module_label = "module" if len(modules) == 1 else "modules"
        lines.append(
            f"{index + 1}. {phase.title}: {len(local)} results in "
            f"{len(modules)} {module_label}"
        )
        if index == len(PHASE_METADATA) - 1:
            continue
        crossing = [
            (dependency, label)
            for label, dependencies in shallow.items()
            for dependency in dependencies
            if phase_index[nodes[dependency].phase] <= index
            and phase_index[nodes[label].phase] > index
        ]
        frontier = sorted(
            {dependency for dependency, _ in crossing},
            key=lambda label: nodes[label].source_order,
        )
        lines.append(
            f"   boundary: {len(crossing)} reduced edges from {len(frontier)} results"
        )
        lines.extend(
            f"   - {label}: {nodes[label].title}" for label in frontier
        )
    return "\n".join(lines)


def update(path: Path, expected: str, check: bool) -> bool:
    actual = path.read_text() if path.exists() else None
    if actual == expected:
        return False
    if check:
        raise SystemExit(f"blueprint: generated file is stale: {path.relative_to(ROOT)}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(expected)
    return True


def main() -> None:
    parser = argparse.ArgumentParser()
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--check", action="store_true", help="fail instead of updating files")
    action.add_argument(
        "--phase-report", action="store_true", help="describe the current phase boundaries"
    )
    args = parser.parse_args()

    nodes = read_nodes()
    validate_phase_contract(nodes)
    validate_reference_contract(nodes)
    if args.phase_report:
        print(render_phase_report(nodes))
        return
    content = render_content(nodes)
    changed = []
    if update(CONTENT, content, args.check):
        changed.append(CONTENT.relative_to(ROOT).as_posix())
    edge_count = sum(len(node.dependencies) for node in nodes.values())
    action = "checked" if args.check else "generated"
    print(f"blueprint: {action} {len(nodes)} nodes and {edge_count} dependency edges")
    if changed:
        print(f"blueprint: updated {', '.join(changed)}")


if __name__ == "__main__":
    main()
