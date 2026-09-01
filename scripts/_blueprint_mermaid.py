"""Render the README and Markdown dependency maps from blueprint node data."""

from __future__ import annotations

import re
from pathlib import Path
from urllib.parse import quote


README_START = "<!-- blueprint-mermaid:start -->"
README_END = "<!-- blueprint-mermaid:end -->"
GUIDE_URL = "https://gaearon.github.io/conway-refinement/"
GUIDE_RESULT_URL = GUIDE_URL + "#/result/"
GUIDE_CHAPTER_URL = GUIDE_URL + "#/chapter/"

NODE_CLASSES = {
    "Definition": "definition",
    "Theorem": "theorem",
    "Lemma": "lemma",
    "Proposition": "proposition",
    "Corollary": "corollary",
    "Fact": "fact",
}

TEX_COMMANDS = {
    r"\Kser": "K((ℝ^{≤0}))",
    r"\Kfin": "K_fin",
    r"\Ph": "P̂",
    r"\RVh": "RV̂",
    r"\Prin": "P",
    r"\vJ": "v_J",
    r"\Nn": "Fun_{0^-}",
    r"\lifts": "b_𝓑",
    r"\KX": "K[X]",
    r"\pol": "pol",
    r"\calB": "𝓑",
    r"\Oz": "Oz",
    r"\No": "No",
    r"\On": "On",
    r"\deg": "deg",
    r"\dim": "dim",
    r"\ot": "ot",
    r"\supp": "supp",
    r"\oplus": "⊕",
    r"\odot": "⊙",
    r"\ominus": "⊖",
    r"\nsum": "⊕",
    r"\nsub": "⊖",
    r"\leq": "≤",
    r"\le": "≤",
    r"\geq": "≥",
    r"\ge": "≥",
    r"\neq": "≠",
    r"\ne": "≠",
    r"\equiv": "≡",
    r"\bot": "⊥",
    r"\ell": "ℓ",
    r"\notin": "∉",
    r"\cap": "∩",
    r"\otimes": "⊗",
    r"\bigcup": "⋃",
    r"\forall": "∀",
    r"\exists": "∃",
    r"\subseteq": "⊆",
    r"\supseteq": "⊇",
    r"\in": "∈",
    r"\nexists": "∄",
    r"\iff": "⇔",
    r"\simeq": "≃",
    r"\Rightarrow": "⇒",
    r"\Longrightarrow": "⇒",
    r"\to": "→",
    r"\mapsto": "↦",
    r"\bmod": " mod ",
    r"\pmod": " mod ",
    r"\uparrow": "↑",
    r"\partial": "∂",
    r"\sum": "∑",
    r"\omega": "ω",
    r"\Delta": "Δ",
    r"\Lambda": "Λ",
    r"\alpha": "α",
    r"\beta": "β",
    r"\gamma": "γ",
    r"\delta": "δ",
    r"\eta": "η",
    r"\lambda": "λ",
    r"\mu": "μ",
    r"\rho": "ρ",
    r"\sigma": "σ",
    r"\tau": "τ",
    r"\theta": "θ",
    r"\xi": "ξ",
    r"\zeta": "ζ",
    r"\infty": "∞",
    r"\iota": "ι",
    r"\nu": "ν",
    r"\varphi": "φ",
    r"\mathcal A": "𝒜",
    r"\mathcal B": "𝓑",
    r"\varspol": "vars",
    r"\vars": "vars",
    r"\utrunc": "trunc",
    r"\sup": "sup",
    r"\lbrack": "[",
    r"\rbrack": "]",
    r"\langle": "⟨",
    r"\rangle": "⟩",
    r"\vert": "|",
    r"\cdots": "⋯",
    r"\colon": ":",
    r"\,": " ",
    r"\ ": " ",
    r"\!": "",
}

STYLES = [
    "  classDef theorem fill:#fff3bf,stroke:#e67700,stroke-width:2px,color:#111827",
    "  classDef definition fill:#f3f4f6,stroke:#4b5563,color:#111827",
    "  classDef lemma fill:#dbeafe,stroke:#2563eb,color:#111827",
    "  classDef proposition fill:#ede9fe,stroke:#7c3aed,color:#111827",
    "  classDef corollary fill:#dcfce7,stroke:#16a34a,color:#111827",
    "  classDef fact fill:#fce7f3,stroke:#db2777,color:#111827",
    "  classDef boundary fill:#f8fafc,stroke:#64748b,stroke-dasharray:4 3,color:#334155",
]


def mermaid_text(text: str) -> str:
    return (
        text.replace("&", "&amp;")
        .replace('"', "&quot;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("\n", " ")
    )


def mermaid_math_text(text: str) -> str:
    """Transcribe the title TeX subset into GitHub-safe linear mathematics."""
    if text.count("$") % 2:
        raise ValueError(f"unbalanced math delimiters in Mermaid title: {text!r}")

    def transcribe(fragment: str, math: bool) -> str:
        if not math:
            fragment = fragment.replace("---", "—").replace("--", "–")
        fragment = re.sub(
            r"\\mathbb\s*(?:\{([NQRZ])\}|([NQRZ]))",
            lambda match: {"N": "ℕ", "Q": "ℚ", "R": "ℝ", "Z": "ℤ"}[
                match.group(1) or match.group(2)
            ],
            fragment,
        )
        for command in sorted(TEX_COMMANDS, key=len, reverse=True):
            fragment = fragment.replace(command, TEX_COMMANDS[command])
        previous = None
        while previous != fragment:
            previous = fragment
            fragment = re.sub(
                r"\\(?:mathrm|mathbf|mathsf|operatorname|text)\{([^{}]*)\}",
                r"\1",
                fragment,
            )
            fragment = re.sub(r"\\(?:mathrm|mathbf|mathsf)\s*([A-Za-z])", r"\1", fragment)
            fragment = re.sub(r"\\widehat\{([^{}]*)\}", r"\1̂", fragment)
            fragment = re.sub(r"\\mathbin\{([^{}]*)\}", r"\1", fragment)
        fragment = fragment.replace(r"\{", "{").replace(r"\}", "}")
        unknown = re.search(r"\\(?:[A-Za-z]+|.)", fragment)
        if unknown is not None:
            raise ValueError(f"unsupported TeX command {unknown.group(0)!r} in {text!r}")
        if math:
            fragment = re.sub(r"\s*([=<>≤≥≠≃∈∉⊆⊕⊖→↦+])\s*", r" \1 ", fragment)
            fragment = re.sub(r"\s*(?<!\^)-\s*", " - ", fragment)
            fragment = re.sub(r",\s*", ", ", fragment)
            fragment = re.sub(r"\s*:\s*", " : ", fragment)
            fragment = re.sub(r"\{\s+", "{", fragment)
            fragment = re.sub(r"\s+\}", "}", fragment)
            fragment = re.sub(r" {2,}", " ", fragment).strip()
        return fragment

    pieces = text.split("$")
    return mermaid_text(
        "".join(transcribe(piece, index % 2 == 1) for index, piece in enumerate(pieces))
    )


def display(node: dict) -> str:
    return mermaid_math_text(f"({node['number']}) {node['title']}")


def source_url(node: dict, source: dict | None) -> str:
    if source is None:
        return f"{quote(node['source'], safe='/')}#L{node['line']}"
    return (
        f"{source['repository']}/blob/{source['revision']}/"
        f"{quote(node['source'], safe='/')}#L{node['line']}"
    )


def guide_result_url(node: dict) -> str:
    slug = node["id"].split(":", 1)[-1]
    return GUIDE_RESULT_URL + quote(slug, safe="")


def edge_rows(nodes: list[dict]) -> list[tuple[dict, dict, bool]]:
    by_id = {node["id"]: node for node in nodes}
    return [
        (by_id[dependency], node, dependency in node["proofDependencies"])
        for node in nodes
        for dependency in node["dependencies"]
    ]


def render_full(phases: list[dict], nodes: list[dict], source: dict | None) -> str:
    ids = {node["id"]: f"n{node['number']:03d}" for node in nodes}
    lines = [
        "%% Generated by scripts/blueprint.sh; do not edit.",
        "%% Arrows point from a prerequisite to the result that depends on it.",
        "%% Solid arrows are proof dependencies; dashed arrows are statement dependencies.",
        "flowchart TB",
    ]
    for index, phase in enumerate(phases):
        lines.extend([
            f'  subgraph phase{index}["{mermaid_text(phase["title"])}"]',
            "    direction TB",
        ])
        for node in nodes:
            if node["phase"] == phase["id"]:
                lines.append(
                    f'    {ids[node["id"]]}["{display(node)}"]:::{NODE_CLASSES[node["kind"]]}'
                )
        lines.append("  end")
    lines.append("")
    for edge_source, target, proof in edge_rows(nodes):
        arrow = "-->" if proof else "-.->"
        lines.append(f"  {ids[edge_source['id']]} {arrow} {ids[target['id']]}")
    for node in nodes:
        lines.append(
            f'  click {ids[node["id"]]} "{mermaid_text(source_url(node, source))}" '
            f'"Open {mermaid_text(node["source"])} at line {node["line"]}"'
        )
    return "\n".join(lines + ["", *STYLES]) + "\n"


def render_overview(phases: list[dict], nodes: list[dict]) -> str:
    counts = {
        phase["id"]: sum(node["phase"] == phase["id"] for node in nodes)
        for phase in phases
    }
    phase_ids = {phase["id"]: f"p{index}" for index, phase in enumerate(phases)}
    phase_edges: dict[tuple[str, str], tuple[int, bool]] = {}
    for source, target, proof in edge_rows(nodes):
        if source["phase"] == target["phase"]:
            continue
        key = (source["phase"], target["phase"])
        count, has_proof = phase_edges.get(key, (0, False))
        phase_edges[key] = count + 1, has_proof or proof
    lines = [
        "%% Generated by scripts/blueprint.sh; do not edit.",
        "%% Edge labels count visible result dependencies.",
        "flowchart TB",
    ]
    for phase in phases:
        lines.append(
            f'  {phase_ids[phase["id"]]}["{mermaid_text(phase["title"])}<br/>'
            f'{counts[phase["id"]]} results"]:::phase'
        )
    for (source, target), (count, proof) in phase_edges.items():
        arrow = "-->" if proof else "-.->"
        lines.append(f'  {phase_ids[source]} {arrow}|"{count}"| {phase_ids[target]}')
    for phase in phases:
        lines.append(
            f'  click {phase_ids[phase["id"]]} "{GUIDE_CHAPTER_URL}{phase["id"]}" '
            f'"Open {mermaid_text(phase["title"])}"'
        )
    lines.extend(
        ["", "  classDef phase fill:#f8fafc,stroke:#475569,stroke-width:2px,color:#111827"]
    )
    return "\n".join(lines) + "\n"


def render_phase(
    phase: dict, phases: list[dict], nodes: list[dict], source: dict | None,
    *, guide_links: bool = False,
) -> str:
    phase_id = phase["id"]
    phase_titles = {item["id"]: item["title"] for item in phases}
    phase_order = [item["id"] for item in phases]
    local = [node for node in nodes if node["phase"] == phase_id]
    local_ids = {node["id"]: f"n{node['number']:03d}" for node in local}
    local_set = set(local_ids)
    incoming: dict[tuple[str, str], bool] = {}
    outgoing: dict[tuple[str, str], bool] = {}
    internal = []
    for edge_source, target, proof in edge_rows(nodes):
        if edge_source["id"] in local_set and target["id"] in local_set:
            internal.append((edge_source, target, proof))
        elif target["id"] in local_set:
            key = (edge_source["phase"], target["id"])
            incoming[key] = incoming.get(key, False) or proof
        elif edge_source["id"] in local_set:
            key = (edge_source["id"], target["phase"])
            outgoing[key] = outgoing.get(key, False) or proof
    input_phases = [item for item in phase_order if any(key[0] == item for key in incoming)]
    output_phases = [item for item in phase_order if any(key[1] == item for key in outgoing)]
    input_ids = {item: f"in{index}" for index, item in enumerate(input_phases)}
    output_ids = {item: f"out{index}" for index, item in enumerate(output_phases)}
    lines = [
        "%% Generated by scripts/blueprint.sh; do not edit.",
        "%% Other sections are compressed to boundary nodes.",
        "%% Solid arrows are proof dependencies; dashed arrows are statement dependencies.",
        "flowchart TB",
    ]
    if input_phases:
        lines.extend(['  subgraph inputs["Inputs from other sections"]', "    direction TB"])
        for item in input_phases:
            count = sum(key[0] == item for key in incoming)
            lines.append(
                f'    {input_ids[item]}["{mermaid_text(phase_titles[item])}<br/>'
                f'used by {count} results"]:::boundary'
            )
        lines.append("  end")
    lines.extend([f'  subgraph current["{mermaid_text(phase["title"])}"]', "    direction TB"])
    for node in local:
        lines.append(
            f'    {local_ids[node["id"]]}["{display(node)}"]:::{NODE_CLASSES[node["kind"]]}'
        )
    lines.append("  end")
    if output_phases:
        lines.extend(['  subgraph outputs["Used by other sections"]', "    direction TB"])
        for item in output_phases:
            count = sum(key[1] == item for key in outgoing)
            lines.append(
                f'    {output_ids[item]}["{mermaid_text(phase_titles[item])}<br/>'
                f'{count} results used downstream"]:::boundary'
            )
        lines.append("  end")
    lines.append("")
    for edge_source, target, proof in internal:
        arrow = "-->" if proof else "-.->"
        lines.append(f"  {local_ids[edge_source['id']]} {arrow} {local_ids[target['id']]}")
    for (source_phase, target), proof in incoming.items():
        arrow = "-->" if proof else "-.->"
        lines.append(f"  {input_ids[source_phase]} {arrow} {local_ids[target]}")
    for (edge_source, target_phase), proof in outgoing.items():
        arrow = "-->" if proof else "-.->"
        lines.append(f"  {local_ids[edge_source]} {arrow} {output_ids[target_phase]}")
    for node in local:
        url = guide_result_url(node) if guide_links else source_url(node, source)
        description = (
            f"Open the statement for {node['kind'].lower()} {node['number']}"
            if guide_links
            else f"Open {node['source']} at line {node['line']}"
        )
        lines.append(
            f'  click {local_ids[node["id"]]} "{mermaid_text(url)}" '
            f'"{mermaid_text(description)}"'
        )
    return "\n".join(lines + ["", *STYLES]) + "\n"


def update_readme(path: Path, overview: str, details: list[tuple[dict, str]]) -> None:
    text = path.read_text()
    if text.count(README_START) != 1 or text.count(README_END) != 1:
        raise ValueError(f"{path} must contain exactly one generated Mermaid marker pair")
    start = text.index(README_START)
    end = text.index(README_END, start) + len(README_END)
    detail_blocks = "\n\n".join(
        f'<a id="phase-{phase["id"]}"></a>\n<details>\n'
        f'<summary>{phase["title"]}</summary>\n\n'
        f"```mermaid\n{diagram}```\n</details>"
        for phase, diagram in details
    )
    block = (
        f"{README_START}\n"
        "### Proof overview\n\n"
        f"```mermaid\n{overview}```\n\n"
        f"{detail_blocks}\n{README_END}"
    )
    path.write_text(text[:start] + block + text[end:])


def generate(root: Path, output: Path, payload: dict) -> None:
    phases = payload["phases"]
    nodes = payload["nodes"]
    source = payload["source"]
    complete = render_full(phases, nodes, source)
    overview = render_overview(phases, nodes)
    details = [
        (phase, render_phase(phase, phases, nodes, source)) for phase in phases
    ]
    readme_details = [
        (phase, render_phase(phase, phases, nodes, None, guide_links=True))
        for phase in phases
    ]
    for stale in output.glob("dependency-graph-*.mmd"):
        stale.unlink()
    for stale in output.glob("dependency-graph-*.md"):
        stale.unlink()
    (output / "dependency-graph.mmd").write_text(complete)
    (output / "dependency-graph-overview.mmd").write_text(overview)
    (output / "dependency-graph.md").write_text(
        "<!-- Generated by scripts/blueprint.sh; do not edit. -->\n"
        "# Lean proof guide\n\n"
        "Solid arrows are proof dependencies; dashed arrows are statement dependencies.\n\n"
        f"```mermaid\n{overview}```\n\n"
        "## Detailed maps\n\n"
        + "\n".join(
            f"- [{phase['title']}](dependency-graph-{phase['id']}.md)" for phase in phases
        )
        + f"\n\n## Complete graph\n\n```mermaid\n{complete}```\n"
    )
    for phase, diagram in details:
        stem = f"dependency-graph-{phase['id']}"
        (output / f"{stem}.mmd").write_text(diagram)
        (output / f"{stem}.md").write_text(
            "<!-- Generated by scripts/blueprint.sh; do not edit. -->\n"
            f"# {phase['title']}\n\n[Back to the dependency map](dependency-graph.md)\n\n"
            "Cross-section dependencies are compressed to boundary nodes.\n\n"
            f"```mermaid\n{diagram}```\n"
        )
    update_readme(root / "README.md", overview, readme_details)
