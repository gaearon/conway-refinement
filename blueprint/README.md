# Lean proof guide

The guide is generated from `@[blueprint]` annotations in the Lean source. It is the reader's map
of the mathematical argument, not a second statement tree. It contains the minimum information
from which a research mathematician can reconstruct the entire proof with reasonable
research-level effort.

`src/statements.tex` presents the three standalone formulations of the headline claim.

## Selection

- Each node is exactly one Lean declaration.
- Select the complete mathematical spine, every substantive result proved here, every external
  result it relies on, and every intermediate step that a research mathematician could not readily
  infer. Omit routine identities, coercions, and API plumbing.
- After a proof refactor, add every declaration that newly meets this criterion. Remove a previous
  node only when it disappeared, became readily inferable, or was subsumed by a stronger selected
  declaration. The proof spine must remain mathematically reconstructible across the change.
- A node title is a concise mathematical name for the result. Use an established name when the
  literature has one; otherwise use a transparent noun phrase built from standard objects and
  properties. The exact proposition belongs in the statement, not in a title that repeats it.
  Titles never introduce terminology, narrate a proof, or depend on surrounding node labels.
- A node statement and proof must match the Lean signature and proof route. A node states several
  conclusions only when the Lean declaration returns them together.

## Dependencies

Proof prose cites every visible immediate predecessor with `\ref{...}`. The generator contracts
unselected declarations, transitively reduces the resulting graph, and rejects missing or extra
references. Dependencies treated as routine background therefore do not appear as nodes.

## Vocabulary

[The field terminology map](terminology/FIELD.md), especially Part 0, fixes the vocabulary and
notation. The records in `terminology/sources/` preserve the source evidence for those choices.
New objects are named by ordinary mathematical constructions whenever possible.

## Checks

```text
scripts/blueprint.sh build
```

This checks the selected annotations and regenerates the source, Mermaid maps, README fragment,
interactive reader, and PDF together. The reader, maps, and PDF all use the same checked node data.
`scripts/blueprint.sh check` performs the same annotation and dependency checks without rendering.
For a change confined to `phases.json` or the renderers, `scripts/blueprint.sh render` regenerates
the guide from the existing checked node data without rebuilding Lean.
`python3 scripts/_blueprint.py --phase-report` reports the size and reduced dependency frontier of
every phase from that data, without any phase-specific expectations.

The ordinary build is a working-tree preview. To reproduce the publishable guide locally from a
clean committed source tree, run:

```text
scripts/publish-blueprint.sh
```

The command runs the local Lean gates and builds every guide format against the full source SHA.
Use `--quick` to retain the cached build while omitting only the slow negative audit probes.
`scripts/check-blueprint-publication.sh` rejects a mutable `blob/main` link, a mismatched source
SHA, or any generated change to tracked source files.

GitHub Actions runs the same checks for the checked-out commit, deploys `blueprint/web/` to GitHub
Pages, and uploads the PDF. Tagged builds also attach the PDF to the corresponding GitHub Release.
Generated web and PDF artifacts are not committed.

The Mermaid output has three synchronized scales: a phase overview, one detailed map for each
phase with cross-phase dependencies compressed to boundary ports, and the complete theorem graph.
Every theorem node is numbered as in the PDF and appears as a local node in exactly one phase map.
Nodes and edges follow the Lean annotations automatically. The Highlights introduction and the
ordered phase titles, slugs, and descriptions live in `phases.json`; the PDF uses that introduction
as its Overview, and each annotation carries the corresponding stable internal key.
Generation rejects unknown or unused keys, drift from Lean's compile-time key mirror, backwards
dependencies, and modules split between phases. The annotation label's `def:`, `thm:`, `lem:`,
`prop:`, `cor:`, or `fact:` prefix controls the displayed result kind. Phase and result kind are
reviewed whenever a node is added or retagged.
