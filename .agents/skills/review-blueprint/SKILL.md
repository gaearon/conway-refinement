---
name: review-blueprint
description: >-
  Verify that the mathematical blueprint is a rigorous and faithful account of the Lean proof. Use
  the smallest review boundary capable of catching drift after a change; review every node only for
  a final PR or release audit.
---

# Review the proof blueprint

Ensure that a research mathematician who has never used Lean receives a correct, standard, and
sufficient account of the formal proof. Lean is the authority for what is proved. The blueprint is
the mathematical translation of the selected proof spine.

Treat every existing blueprint node as an unverified claim until its Lean declaration and proof
have been checked in this review. Compilation, a previous review, polished prose, and a plausible
title do not establish semantic fidelity. Try to falsify each statement, proof sentence, dependency,
and source attribution against the authoritative evidence before accepting it.

This skepticism is not a mandate to edit. If a node is already exact, atomic, standard, legible, and
properly selected, leave its wording unchanged. A review may correctly produce no diff. Do not
replace accepted terminology with synonyms, restyle a faithful proof, or churn prose merely to show
activity; edit only to close a confirmed defect or a concrete failure of the stated selection and
legibility criteria.

Review only what a change can have disturbed. A change to mathematical factoring, selection, a
selected signature, a proof route, or a visible dependency reopens the affected nodes and the
smallest complete inference chain around them. A bookkeeping edit deliberately excluded from the
map, which changes none of those things, needs no blueprint review. For a final PR or release audit,
review every selected node without sampling.

When an external review is requested, read its full report and reconcile every substantive finding
with the exact Lean statement and proof before resuming unrelated work; its overall verdict is not a
substitute for resolving its individual findings.

Before editing any title, statement, or proof, read `blueprint/README.md` and the whole of
`blueprint/terminology/FIELD.md`. Treat the field map as a vocabulary constraint, not merely a
reference:

- use its chosen system of notation and terminology wholesale;
- assume Lean names may be internal shorthand: their presence in code is not evidence that the
  vocabulary is mathematical, and they must not leak into blueprint titles, statements, or proofs;
- if a proposed term is absent from the map, stop and check the primary sources recorded there;
  either use their term or state the defining mathematical condition without naming it;
- audit every noun phrase introduced by the review, not only names already suspected of being
  nonstandard.

After any conversation context compaction, reread the whole of
`blueprint/terminology/FIELD.md` before making another Lean or blueprint edit, even when the
compacted summary says that it was read earlier.

Treat a divergence between Lean and the field map as a code finding, not merely a prose finding.
Rename declarations, structures, fields, predicates, and docstrings to accepted mathematical
terminology wherever practical, and update their uses. Avoid creating private project nomenclature
when standard mathematics or a direct defining phrase will do. Retain a short internal name only
when a literal mathematical name would be genuinely unwieldy; keep that exception out of the
blueprint and document its mathematical meaning at its public boundary. Do not close the review by
translating a nonstandard public Lean API only in prose.

Distinguish vocabulary from spelling conventions. Lean module paths, declaration names, and exact
API references follow Mathlib and the pinned dependencies; blueprint text, docstrings, and other
reader-facing mathematics follow the field map. For example, Lean uses `Factorization`, while the
mathematical text uses “factorisation”. Preserve cited titles verbatim, and never “correct” a code
identifier inside prose into a name that does not exist.

When a review identifies a project coinage or a repeatedly misleading phrase, prevent its return.
After replacing every mathematician-facing occurrence in scope, add the phrase to
`scripts/Documentation.lean` with the accepted replacement or the exact condition that should be
stated instead. The existing documentation negative control tests the checker; add another probe
only when the checker itself changes, not when its vocabulary list grows. Do not use this lexical
guard as a substitute for reviewing meaning: it records conclusions already established from the
field map and primary sources, and must not ban a standard term merely because one occurrence was
imprecise.

Run the fast structural check first:

```text
scripts/blueprint.sh check
```

If it reports missing immediate references, the check inserts an unsupported blueprint argument
`FIXME_blueprint_review_why_does_proof_depend_on := "..."` at the source annotation. The argument is
a durable review queue, not an explanation: Lean will not compile the file while it remains, so a
wording change cannot accidentally turn it into a completed audit. Resolve each argument with
mathematical judgment:

- replace it by a sentence that explains the precise role of every cited predecessor in the
  argument, when that implication is genuinely legible from those predecessors;
- if the implication is not reasonably reconstructible by a research mathematician, select the
  missing intermediate theorem and explain the shorter steps instead;
- if the dependency exposes a proof written through an unnatural API or coordinate system,
  improve the Lean factorization rather than forcing an opaque sentence into the blueprint.

Remove the unsupported argument only after making one of those repairs. Never close a ledger row by
merely deleting it, inserting a bare reference list, or paraphrasing declaration names. The
resulting proof paragraph must make mathematical sense on its own and must still describe the route
Lean actually takes.

For a full PR or release review, first generate an exact-source ledger of every selected node from
the checked blueprint metadata. Record at least the node label, sole Lean declaration, source file and
range, title, visible dependencies, and proof references. Fix the node count before reviewing, mark
each node only after reading its full Lean declaration and proof, and retain the completed ledger
until the review closes. This is an exhaustive audit, not a sampling exercise; a final report must
account for every node in the initial ledger and every node added during repair.

Generate that ledger after building the blueprint:

```text
python3 scripts/blueprint-review-ledger.py
```

It writes exact generated prose and the corresponding Lean source slices to
`tmp/blueprint-audit/`; do not commit the review ledger.

Close the ledger one declaration at a time. For each node, read its full Lean declaration and its
immediate mathematical inputs, decide its disposition, make any repair, record that disposition in
the ledger, and then open the next node. Use cheap local checks while iterating: inspect the exact
diff, search for stale names and references, and run a direct Lean check only when the edit changes a
signature or proof in a way that needs immediate elaboration feedback. Do not rebuild the full
blueprint or project after each node; run those checks at coherent dependency checkpoints and at the
end. Do not accumulate a batch of unactioned findings: a review state that survives context
compaction must consist of closed nodes and one current node, not remembered prose about a large
unrepaired range.

For every declaration in scope, read the full Lean signature and proof, together with the
definitions that determine their mathematical meaning. Verify:

- **Annotation syntax:** a blueprint `title := "..."` is a Lean string, so every TeX backslash
  must be doubled in the Lean source (`\\omega`, `\\operatorname`, and so on). The `statement` and
  `proof` fields are doc comments and use ordinary single TeX backslashes. Run a direct Lean check
  after editing titles so malformed string escapes are caught before the next node.

- **Title:** the title is a concise mathematical name for the result, not a second copy of its
  proposition. Use an established name from the references when one exists; otherwise use a
  transparent noun phrase built from standard objects and properties. It must not invent
  terminology, narrate the proof, or depend on pronouns or surrounding node labels. Review the
  rendered form `Theorem N (Title). Statement` (or the corresponding result kind) as one sentence:
  the title and opening of the statement must not repeat each other or collide grammatically.
- **Atomicity:** one node is one Lean declaration, and its prose presents several conclusions only
  when the Lean return type presents them together.
- **Vocabulary:** title, statement, and proof use established terminology and the notation fixed by
  the field guide, with no project-invented substitutes for standard objects.
- **Statement fidelity:** every quantifier, hypothesis, endpoint, zero case, orientation, and
  conclusion agrees with the Lean type.
- **Proof fidelity:** the prose describes the route Lean actually proves, including every
  nontrivial intermediate conclusion and side condition; it does not substitute a nicer argument.
- **Dependencies:** the cited immediate blueprint predecessors are exactly the nontrivial results
  used by the proof and visible in the map. Do not create dummy Lean dependencies or prose citations
  to shape the graph.
- **Sources:** every attribution and source claim is supported by the opened primary source at the
  stated location.

Review selection as mathematics, not graph cosmetics. Add each declaration that has newly become a
necessary nontrivial step. Accept a removed node only when it disappeared, became readily inferable,
or was subsumed by a stronger selected theorem. Confirm that a research mathematician can still
reconstruct every path from the stated inputs to the main results.

Treat phase assignment and result kind as reviewed mathematical metadata. Nodes and edges are read
from Lean automatically; the required `phase` field of `@[blueprint]` assigns the phase, and the
annotation label prefix (`def:`, `thm:`, `lem:`, `prop:`, `cor:`, or `fact:`) assigns the displayed
result kind. Lean's declaration command does not make either editorial decision. Whenever a
selected declaration is added or retagged, inspect its phase map. Check that the
phase states the declaration's role in the argument, that dependencies respect the reading order,
and that the result kind matches ordinary mathematical usage. Do not classify nodes to
balance the diagram. A final PR or release review checks this metadata for every node.

Treat each phase description as mathematical glue between chapters. For every changed description,
read the complete rendered chapter in `blueprint/src/content.tex` and inspect the full reduced
dependency graph in `blueprint/web/dependency-graph.mmd`. Check every factual clause against the
selected statements or an actual graph edge, including claims about what the preceding chapter leaves
open, why the present change of viewpoint addresses it, what this chapter establishes, and what that
opens up next. A description may use a later result as motivation, but must not present it as already
proved. Reject an isolated inventory in place of an explanation, and reject invented continuity when
the chapter is only a collection of prerequisites.
Check the prose for simple English without weakening its mathematical content. Prefer short sentences
and concrete verbs. Require every necessary field term and hypothesis, but reject academic shorthand
when the same point can be stated directly.

Read all introductions in order to check the narrative handoffs, terminology, and repetition. A
description-only edit does not reopen otherwise unchanged node statements and proofs, but it still
requires `scripts/blueprint.sh check`, `scripts/blueprint.sh render`, and inspection of the regenerated
maps to confirm that the checked nodes, edges, and phase assignments are unchanged. A final PR or
release review checks every chapter introduction alongside every node.

Review the Highlights introduction as a summary of all chapter descriptions and of the complete
reduced graph. It must cover the whole proof route rather than only the highlighted nodes, and it
must leave enough space to explain every major change of viewpoint. Check that it synthesises the
chapter introductions instead of repeating their intermediate details, and that it remains readable
before the selected results begin. Its layout must not depend on a fixed number of phases or arcs.
Distinct steps must not be compressed into a false implication. Confirm that the web guide and PDF
render the same introduction text as Highlights and Overview rather than separate copies.

Review the publication provenance disclosures. Verify their claims about axiom use, standalone
import boundaries, statement--proof pairing, generated content, source links, and release versioning
against the current repository checks.  It must make unmistakable which text is AI-generated,
which objects are machine-checked, that Lean does not validate their intended mathematical
interpretation, and what a reader must inspect to decide whether the formal headline is the
intended mathematics. The disclosure must describe the project accurately without depending on
where a page break happens to fall.

After repairs, run:

```text
scripts/blueprint.sh build
```

Render and read the Mermaid graph when selection, dependencies, titles, or factoring changed. Report
only mathematical or fidelity findings within the justified review boundary; do not turn the review
into a new refinement project.
