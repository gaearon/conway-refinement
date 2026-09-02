"""Load and validate the ordered mathematical phases of the proof guide."""

from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "blueprint/phases.json"
LEAN_KEYS = ROOT / "ConwayRefinement/Blueprint.lean"
SLUG_RE = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")


@dataclass(frozen=True)
class Highlights:
    title: str
    description: str

    def web_data(self) -> dict[str, str]:
        return asdict(self)


@dataclass(frozen=True)
class Phase:
    key: str
    slug: str
    title: str
    description: str

    def web_data(self) -> dict[str, str]:
        result = asdict(self)
        result["id"] = result.pop("slug")
        result.pop("key")
        return result


def _fail(message: str) -> None:
    raise SystemExit(f"blueprint phases: {message}")


def load_manifest() -> tuple[Highlights, tuple[Phase, ...]]:
    try:
        payload = json.loads(MANIFEST.read_text())
    except (OSError, json.JSONDecodeError) as error:
        _fail(f"cannot read {MANIFEST.relative_to(ROOT)}: {error}")
    if not isinstance(payload, dict) or set(payload) != {"highlights", "phases"}:
        _fail("manifest root must contain exactly `highlights` and `phases`")
    highlights_record = payload["highlights"]
    highlights_fields = {"title", "description"}
    if not isinstance(highlights_record, dict) or set(highlights_record) != highlights_fields:
        _fail("`highlights` must contain exactly `description` and `title`")
    if any(
        not isinstance(highlights_record[field], str)
        or highlights_record[field].strip() != highlights_record[field]
        or not highlights_record[field]
        for field in highlights_fields
    ):
        _fail("`highlights` fields must be non-empty trimmed strings")
    highlights = Highlights(**highlights_record)
    records = payload["phases"]
    if not isinstance(records, list) or not records:
        _fail("`phases` must be a non-empty array")
    phases: list[Phase] = []
    fields = {"key", "slug", "title", "description"}
    for index, record in enumerate(records, start=1):
        if not isinstance(record, dict) or set(record) != fields:
            _fail(f"phase {index} must contain exactly {', '.join(sorted(fields))}")
        if any(not isinstance(record[field], str) or record[field].strip() != record[field]
               or not record[field] for field in fields):
            _fail(f"phase {index} fields must be non-empty trimmed strings")
        if SLUG_RE.fullmatch(record["slug"]) is None:
            _fail(f"phase {index} has invalid slug {record['slug']!r}")
        phases.append(Phase(**record))
    for field in ("key", "slug", "title"):
        values = [getattr(phase, field) for phase in phases]
        duplicates = sorted({value for value in values if values.count(value) > 1})
        if duplicates:
            _fail(f"duplicate {field}(s): {', '.join(duplicates)}")
    return highlights, tuple(phases)


def validate_lean_keys(phases: tuple[Phase, ...]) -> None:
    text = LEAN_KEYS.read_text()
    match = re.search(r"meta def phases : Array String := #\[(.*?)\n\]", text, re.DOTALL)
    if match is None:
        _fail(f"cannot find the compile-time phase-key mirror in {LEAN_KEYS.relative_to(ROOT)}")
    lean_keys = tuple(re.findall(r'^\s*"([^"]+)",\s*$', match.group(1), re.MULTILINE))
    manifest_keys = tuple(phase.key for phase in phases)
    if lean_keys != manifest_keys:
        _fail(
            f"{LEAN_KEYS.relative_to(ROOT)} does not mirror {MANIFEST.relative_to(ROOT)}"
        )


HIGHLIGHTS_METADATA, PHASE_METADATA = load_manifest()
PHASES = tuple(phase.key for phase in PHASE_METADATA)
PHASE_BY_KEY = {phase.key: phase for phase in PHASE_METADATA}
