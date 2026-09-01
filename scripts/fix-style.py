#!/usr/bin/env python3
"""Apply conservative fixes for the Lean source style audit."""

from __future__ import annotations

import sys
import textwrap
from pathlib import Path


MAX_LINE_LENGTH = 100
SOURCE_ROOTS = (Path("ConwayRefinement"), Path("scripts"))


def lean_files(arguments: list[str]) -> list[Path]:
    if arguments:
        roots = [Path(argument) for argument in arguments]
    else:
        roots = list(SOURCE_ROOTS)
    files: list[Path] = []
    for root in roots:
        if root.is_dir():
            files.extend(sorted(root.rglob("*.lean")))
        elif root.is_file() and root.suffix == ".lean":
            files.append(root)
        elif root.exists():
            raise ValueError(root)
        else:
            raise FileNotFoundError(root)
    if not arguments:
        for root in SOURCE_ROOTS:
            root_file = root.with_suffix(".lean")
            if root_file.exists():
                files.append(root_file)
    return list(dict.fromkeys(files))


def comment_depth_after(line: str, depth: int) -> int:
    """Track nested block comments, ignoring markers inside strings and line comments."""
    in_string = False
    escaped = False
    index = 0
    while index < len(line):
        char = line[index]
        following = line[index : index + 2]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif depth == 0 and following == "--":
            break
        elif following == "/-":
            depth += 1
            index += 2
        elif depth > 0 and following == "-/":
            depth -= 1
            index += 2
        elif depth == 0 and char == '"':
            in_string = True
            index += 1
        else:
            index += 1
    return depth


def prose_parts(line: str, block_depth: int) -> tuple[str, str] | None:
    """Return the first-line prefix and prose body for a comment-only line."""
    stripped = line.lstrip()
    indent = line[: len(line) - len(stripped)]
    if block_depth > 0:
        if "-/" in stripped and stripped.split("-/", 1)[1].strip():
            return None
        return indent, stripped
    if stripped.startswith("--"):
        marker = "-- " if stripped.startswith("-- ") else "--"
        return indent + marker, stripped[len(marker) :]
    for marker in ("/-! ", "/-- ", "/- ", "/-!", "/--", "/-"):
        if stripped.startswith(marker):
            if "-/" in stripped and stripped.split("-/", 1)[1].strip():
                return None
            return indent + marker, stripped[len(marker) :]
    return None


def wrap_comment(line: str, block_depth: int, fenced: bool) -> list[str]:
    if len(line) <= MAX_LINE_LENGTH or fenced:
        return [line]
    parts = prose_parts(line, block_depth)
    if parts is None:
        return [line]
    prefix, body = parts
    stripped_body = body.strip()
    if not stripped_body or stripped_body.startswith("|") or "  " in stripped_body:
        return [line]
    continuation = (
        prefix
        if prefix.lstrip().startswith("--")
        else line[: len(line) - len(line.lstrip())]
    )
    wrapped = textwrap.wrap(
        stripped_body,
        width=MAX_LINE_LENGTH,
        initial_indent=prefix,
        subsequent_indent=continuation,
        break_long_words=False,
        break_on_hyphens=False,
    )
    return wrapped or [line]


def comma_positions(line: str, limit: int) -> list[int]:
    """Find commas before `limit` that are outside strings and comments."""
    positions: list[int] = []
    in_string = False
    escaped = False
    block_depth = 0
    delimiter_depth = 0
    index = 0
    while index < min(len(line), limit):
        char = line[index]
        following = line[index : index + 2]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif block_depth == 0 and following == "--":
            break
        elif following == "/-":
            block_depth += 1
            index += 2
        elif block_depth > 0 and following == "-/":
            block_depth -= 1
            index += 2
        elif block_depth == 0 and char == '"':
            in_string = True
            index += 1
        elif block_depth == 0 and char in "([{⟨":
            delimiter_depth += 1
            index += 1
        elif block_depth == 0 and char in ")]}⟩":
            delimiter_depth = max(0, delimiter_depth - 1)
            index += 1
        elif block_depth == 0 and delimiter_depth > 0 and char == ",":
            is_character_comma = (
                index > 0 and index + 1 < len(line) and line[index - 1] == line[index + 1] == "'"
            )
            if not is_character_comma:
                positions.append(index)
            index += 1
        else:
            index += 1
    return positions


def split_at_commas(line: str, block_depth: int) -> list[str]:
    if block_depth > 0 or len(line) <= MAX_LINE_LENGTH:
        return [line]
    indent = line[: len(line) - len(line.lstrip())]
    lines: list[str] = []
    remaining = line
    while len(remaining) > MAX_LINE_LENGTH:
        positions = comma_positions(remaining, MAX_LINE_LENGTH)
        if not positions:
            break
        cut = positions[-1]
        lines.append(remaining[: cut + 1].rstrip())
        remaining = indent + "  " + remaining[cut + 1 :].lstrip()
    lines.append(remaining)
    return lines


def fix_lines(lines: list[str]) -> list[str]:
    normalized = [line.rstrip(" \t") for line in lines]
    wrapped: list[str] = []
    block_depth = 0
    fenced = False
    for line in normalized:
        comment_only = prose_parts(line, block_depth) is not None
        if comment_only and line.lstrip().startswith("```"):
            fenced = not fenced
        additions = wrap_comment(line, block_depth, fenced)
        wrapped.extend(additions)
        block_depth = comment_depth_after(line, block_depth)

    fixed: list[str] = []
    block_depth = 0
    for line in wrapped:
        fixed.extend(split_at_commas(line, block_depth))
        block_depth = comment_depth_after(line, block_depth)
    return fixed


def fix_file(path: Path) -> bool:
    original = path.read_text(encoding="utf-8")
    if not original:
        return False
    fixed = "\n".join(fix_lines(original.splitlines())) + "\n"
    if fixed == original:
        return False
    path.write_text(fixed, encoding="utf-8")
    return True


def main() -> int:
    try:
        files = lean_files(sys.argv[1:])
    except FileNotFoundError as error:
        print(f"style: no such file or directory: {error}", file=sys.stderr)
        return 2
    except ValueError as error:
        print(f"style: expected a Lean source file or directory: {error}", file=sys.stderr)
        return 2
    changed = sum(fix_file(path) for path in files)
    print(f"style: autofixed {changed} of {len(files)} Lean source file(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
