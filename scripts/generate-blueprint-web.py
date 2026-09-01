#!/usr/bin/env python3
"""Build the interactive mathematical reader from checked blueprint artifacts."""

from __future__ import annotations

import importlib.util
import html
import json
import re
import sys
from pathlib import Path
from urllib.parse import quote

from _blueprint_mermaid import generate as generate_mermaid
from _blueprint_revision import read_metadata


ROOT = Path(__file__).resolve().parents[1]
BLUEPRINT = ROOT / "scripts/_blueprint.py"
REFERENCES = ROOT / "blueprint/references.json"
REFERENCES_TEX = ROOT / "blueprint/src/references.tex"
OUTPUT = ROOT / "blueprint/web/data.json"

ENVIRONMENTS = {
    "def": "definition",
    "thm": "theorem",
    "lem": "lemma",
    "prop": "proposition",
    "cor": "corollary",
    "fact": "fact",
}


def load_blueprint_module():
    spec = importlib.util.spec_from_file_location("conway_refinement_blueprint_data", BLUEPRINT)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {BLUEPRINT}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def tex_escape(value: str) -> str:
    return value.replace("&", r"\&").replace("%", r"\%").replace("#", r"\#")


def generate_references_tex(references: list[dict[str, str]]) -> None:
    widest_key = max((reference["key"] for reference in references), key=len)
    lines = [rf"\begin{{thebibliography}}{{{widest_key}}}", ""]
    for reference in references:
        key = reference["key"]
        title = tex_escape(reference["title"])
        if url := reference.get("url"):
            title = rf"\href{{{url}}}{{\emph{{{title}}}}}"
        else:
            title = rf"\emph{{{title}}}"
        if reference["kind"] == "book":
            citation = f'{tex_escape(reference["venue"])}, {tex_escape(reference["details"])}.'
        else:
            venue = rf'\emph{{{tex_escape(reference["venue"])}}}'
            volume = rf' \textbf{{{reference["volume"]}}}' if reference.get("volume") else ""
            year = f' ({reference["year"]})' if reference.get("year") else ""
            details = f', {tex_escape(reference["details"])}' if reference.get("details") else ""
            citation = f"{venue}{volume}{year}{details}."
        lines.extend([
            rf"\bibitem[{key}]{{{key}}}",
            f'{tex_escape(reference["authors"])},',
            f"{title},",
            citation,
            "",
        ])
    lines.append(r"\end{thebibliography}")
    REFERENCES_TEX.write_text("\n".join(lines) + "\n")


def latex_to_html(
    source: str,
    source_metadata: dict[str, object] | None = None,
    references: dict[str, dict[str, object]] | None = None,
) -> str:
    """Render the small prose subset used by blueprint annotations."""
    tokens: list[str] = []

    def token(value: str) -> str:
        tokens.append(value)
        return f"@@BLUEPRINT{len(tokens) - 1}@@"

    source = re.sub(r"(?m)^%.*$", "", source)
    source = re.sub(r"(?m)^\\(?:leanok|lean\{.*\}|uses\{.*\}|label\{.*\})\s*$", "", source)
    source = source.replace(r"\clearpage", "").replace(r"\newpage", "")

    for command, level in (("section", 2), ("subsection", 3), ("paragraph", 4)):
        source = re.sub(
            rf"\\{command}\*?\{{([^{{}}]*)\}}",
            lambda match, level=level: token(
                f"<h{level}>{html.escape(match.group(1))}</h{level}>"
            ),
            source,
        )

    def list_environment(match: re.Match[str]) -> str:
        tag = "ol" if match.group(1) == "enumerate" else "ul"
        items = [item.strip() for item in re.split(r"\\item\s*", match.group(2)) if item.strip()]
        return token(
            f"<{tag}>"
            + "".join(
                f"<li>{latex_to_html(item, source_metadata, references)}</li>" for item in items
            )
            + f"</{tag}>"
        )

    source = re.sub(
        r"\\begin\{(itemize|enumerate)\}(.*?)\\end\{\1\}",
        list_environment,
        source,
        flags=re.DOTALL,
    )

    def display_environment(match: re.Match[str]) -> str:
        body = match.group(2).strip()
        if match.group(1).startswith("align"):
            body = rf"\begin{{aligned}}{body}\end{{aligned}}"
        return token(f'<div class="displaymath">\\[{html.escape(body)}\\]</div>')

    source = re.sub(
        r"\\begin\{(displaymath|equation\*?|align\*?)\}(.*?)\\end\{\1\}",
        display_environment,
        source,
        flags=re.DOTALL,
    )
    source = re.sub(
        r"\\\[(.*?)\\\]",
        lambda match: token(
            f'<div class="displaymath">\\[{html.escape(match.group(1).strip())}\\]</div>'
        ),
        source,
        flags=re.DOTALL,
    )
    source = re.sub(
        r"(?<!\\)\$(.*?)(?<!\\)\$",
        lambda match: token(f"\\({html.escape(match.group(1))}\\)"),
        source,
        flags=re.DOTALL,
    )
    def reference(match: re.Match[str]) -> str:
        label = match.group(1)
        target = references.get(label) if references is not None else None
        if target is None:
            return token(
                f'<a data-reference="{html.escape(label, quote=True)}" '
                f'href="#{html.escape(label, quote=True)}">reference</a>'
            )
        title = str(target["title"]).replace(r"\lbrack", "[").replace(r"\rbrack", "]")
        title = html.escape(title)
        title = re.sub(r"(?<!\\)\$(.*?)(?<!\\)\$", r"\\(\1\\)", title)
        return token(
            f'<a data-reference="{html.escape(label, quote=True)}" '
            f'href="#/result/{quote(label.split(":", 1)[-1], safe="")}">'
            f'{html.escape(str(target["kind"]))} {target["number"]} '
            f'<span class="reference-title">({title})</span></a>'
        )

    source = re.sub(r"\\(?:ref|Cref|cref|eqref)\{([^{}]+)\}", reference, source)
    if source_metadata is not None:
        repository = str(source_metadata["repository"])
        revision = str(source_metadata["revision"])
        source = re.sub(
            r"\\blueprintfilelink\{([^{}]+)\}\s*\{([^{}]+)\}",
            lambda match: token(
                '<a class="text-link" target="_blank" rel="noreferrer" href="'
                + html.escape(
                    f"{repository}/blob/{revision}/{match.group(1)}", quote=True
                )
                + '"><em>'
                + html.escape(match.group(2))
                + "</em></a>"
            ),
            source,
        )
    source = re.sub(
        r"\\cite(?:\[([^\]]+)\])?\{([^{}]+)\}",
        lambda match: token(
            '<span class="citation">['
            + html.escape(match.group(2))
            + (', ' + html.escape(match.group(1).replace('~', ' ')) if match.group(1) else '')
            + ']</span>'
        ),
        source,
    )
    source = re.sub(
        r"\\emph\{([^{}]*)\}",
        lambda match: token(f"<em>{html.escape(match.group(1))}</em>"),
        source,
    )
    source = source.replace(r"\leavevmode", "")
    source = html.escape(source)
    source = source.replace("---", "—").replace("--", "–").replace("~", "&nbsp;")
    paragraphs = [re.sub(r"\s*\n\s*", " ", part).strip() for part in re.split(r"\n\s*\n", source)]
    rendered = "".join(f"<p>{part}</p>" for part in paragraphs if part)
    for index, value in enumerate(tokens):
        rendered = rendered.replace(f"@@BLUEPRINT{index}@@", value)
    rendered = re.sub(
        r"<p>\s*(<(h[2-4]|ul|ol)>.*?</\2>)\s*</p>",
        r"\1",
        rendered,
        flags=re.DOTALL,
    )
    return rendered


def node_prose(node, references) -> tuple[str, str]:
    return latex_to_html(node.statement, references=references), latex_to_html(
        node.proof, references=references
    )


def main() -> None:
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    blueprint = load_blueprint_module()
    source = read_metadata()
    nodes = blueprint.read_nodes()
    blueprint.validate_phase_contract(nodes)
    order, cyclic = blueprint.topological_order(nodes)
    if cyclic:
        raise RuntimeError(f"cyclic blueprint graph: {', '.join(cyclic)}")
    shallow = blueprint.shallow_dependencies(nodes)
    ordered = [
        label
        for phase in blueprint.PHASES
        for label in order
        if nodes[label].phase == phase
    ]
    numbers = {label: index for index, label in enumerate(ordered, start=1)}
    kinds = {
        "def": "Definition",
        "thm": "Theorem",
        "lem": "Lemma",
        "prop": "Proposition",
        "cor": "Corollary",
        "fact": "Fact",
    }
    references = {
        label: {
            "kind": kinds[label.split(":", 1)[0]],
            "number": numbers[label],
            "title": nodes[label].title or label,
        }
        for label in ordered
    }
    bibliography = json.loads(REFERENCES.read_text())
    generate_references_tex(bibliography)
    payload = {
        "phases": [phase.web_data() for phase in blueprint.PHASE_METADATA],
        "source": source,
        "references": bibliography,
        "nodes": [],
    }
    for label in ordered:
        statement, proof = node_prose(nodes[label], references)
        payload["nodes"].append(
            {
                "id": label,
                "name": nodes[label].declarations[0],
                "number": numbers[label],
                "kind": kinds[label.split(":", 1)[0]],
                "phase": blueprint.PHASE_BY_KEY[nodes[label].phase].slug,
                "title": nodes[label].title or label,
                "highlight": nodes[label].highlight,
                "source": nodes[label].source.as_posix(),
                "line": nodes[label].source_line,
                "dependencies": sorted(
                    shallow[label], key=lambda dependency: numbers[dependency]
                ),
                "proofDependencies": sorted(
                    shallow[label].intersection(nodes[label].proof_references),
                    key=lambda dependency: numbers[dependency],
                ),
                "statement": statement,
                "proof": proof,
            }
        )
    OUTPUT.write_text(json.dumps(payload, indent=2) + "\n")
    generate_mermaid(ROOT, OUTPUT.parent, payload)
    for stale in (*OUTPUT.parent.glob("sect*.html"), OUTPUT.parent / "dep_graph_document.html",
                  OUTPUT.parent / "symbol-defs.svg",
                  OUTPUT.parent / "dependency-graph-generated-files.txt"):
        if stale.exists():
            stale.unlink()
    print(f"blueprint: wrote interactive reader with {len(ordered)} results")


if __name__ == "__main__":
    main()
