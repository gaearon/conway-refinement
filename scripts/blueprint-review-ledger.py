#!/usr/bin/env python3
"""Write an exact-source ledger for an exhaustive blueprint review."""

from __future__ import annotations

import json
from pathlib import Path

import _blueprint


ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / ".lake/build/blueprint/nodes.json"
OUT = ROOT / "tmp/blueprint-audit"


def main() -> None:
    if not DATA.exists():
        raise SystemExit("blueprint review: run `scripts/blueprint.sh check` first")
    records = json.loads(DATA.read_text())
    ranges = {record["label"]: record["range"] for record in records}
    selected = sorted(_blueprint.read_nodes().values(), key=lambda node: node.source_order)
    OUT.mkdir(parents=True, exist_ok=True)
    nodes: list[dict[str, object]] = []
    for number, node in enumerate(selected, 1):
        source = ROOT / node.source
        start = node.source_line
        end = ranges[node.label]["end"]["line"]
        source_lines = source.read_text().splitlines()
        nodes.append(
            {
                "number": number,
                "label": node.label,
                "declaration": list(node.declarations),
                "title": node.title,
                "dependencies": sorted(node.dependencies),
                "proof_references": sorted(node.proof_references),
                "source": str(node.source),
                "start": start,
                "end": end,
                "statement": node.statement,
                "proof": node.proof,
                "lean_source": "\n".join(source_lines[start - 1 : end]),
            }
        )

    (OUT / "nodes.json").write_text(json.dumps(nodes, indent=2) + "\n")
    with (OUT / "ledger.md").open("w") as stream:
        stream.write("# Exhaustive blueprint review\n\n")
        stream.write(f"Selected nodes: {len(nodes)}\n\n")
        for node in nodes:
            declaration = node["declaration"][0]
            stream.write(
                f"- [ ] {node['number']:03d} `{node['label']}` — "
                f"`{declaration}` — {node['source']}:{node['start']}\n"
            )
    print(f"blueprint review: wrote {len(nodes)} nodes to {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
