#!/usr/bin/env python3
"""Build selected Lean modules and export their checked blueprint metadata."""

from __future__ import annotations

import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "ConwayRefinement"
BUILD = ROOT / ".lake/build/blueprint"
OUTPUT = BUILD / "nodes.json"
EXPORT = BUILD / "Export.lean"


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def selected_modules() -> list[str]:
    return sorted(
        module_name(path)
        for path in SOURCE.rglob("*.lean")
        if 'blueprint "' in path.read_text()
    )


def main() -> None:
    modules = selected_modules()
    if not modules:
        raise SystemExit("blueprint-data: discovered no selected modules")
    subprocess.run(["lake", "build", *modules], cwd=ROOT, check=True)
    BUILD.mkdir(parents=True, exist_ok=True)
    imports = [*(f"import {module}" for module in modules), ""]
    EXPORT.write_text(
        "\n".join([*imports, f'#write_blueprint_data "{OUTPUT}"', ""])
    )
    subprocess.run(
        [
            "lake",
            "env",
            "lean",
            "-DautoImplicit=false",
            "-DrelaxedAutoImplicit=false",
            str(EXPORT),
        ],
        cwd=ROOT,
        check=True,
    )
    print(f"blueprint-data: wrote selected declarations to {OUTPUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
