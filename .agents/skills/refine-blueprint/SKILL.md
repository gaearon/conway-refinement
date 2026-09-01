---
name: refine-blueprint
description: >-
  Improve a Lean proof and its mathematical blueprint together. Use the map to discover better
  objects, coordinates, and theorem factorizations; refactor Lean when that makes the mathematics
  more direct; organize chapters around the proof's actual mathematical phases; and iterate until
  the user asks to stop.
---

# Refine the proof through its blueprint

Make the formal argument as mathematically natural, economical, and illuminating as possible. The
blueprint and Lean serve each other:

- the blueprint must tell the truth about the proof Lean contains;
- Lean should use the objects and coordinates that make that truth easiest to see.

The target blueprint contains the minimum necessary information from which a research mathematician
could reconstruct the entire proof with reasonable effort: the mathematical spine, the results
proved here, the results relied upon, and the intermediate steps that are not readily inferable.
Bookkeeping familiar to a researcher stays out.

## Fix the mathematical language before editing

Treat accepted mathematical language as the first constraint on every change. A cleaner graph,
shorter proof, or more appealing chapter structure never justifies coined terminology, project
vocabulary, or a phrase copied from a Lean identifier.

Before changing Lean or blueprint prose, read `blueprint/README.md` and the whole of
`blueprint/terminology/FIELD.md`. Its choices are binding for the mathematicians' map. A Lean
structure name, namespace, file name, or convenient project phrase is not evidence that a term is
mathematical vocabulary. If a proposed term does not occur in the map, check the recorded primary
sources before using it; otherwise write the defining condition directly. Never invent a polished
name for an internal abstraction and then present it as field terminology.

Expect Lean code to contain historical or implementation shorthand. Do not let it leak into the
blueprint. When a Lean name diverges from accepted mathematical terminology, treat that as a reason
to rename the declaration, structure, field, predicate, or docstring and its uses, not as a reason
to preserve two vocabularies. Avoid internal project nomenclature wherever standard terminology or
a direct defining phrase suffices. Keep a concise internal name only when the fully literal name
would be genuinely unwieldy; confine that exception to implementation code and state the
mathematical meaning at every public or blueprint boundary.

Spelling follows the boundary between code and mathematical prose. Lean module paths, declaration
names, and exact API references follow Mathlib and the pinned dependencies. Blueprint text,
docstrings, and other reader-facing mathematics follow the field map. For example, write
`Factorization` in a Lean identifier and “factorisation” in the generated mathematical text; do not
rewrite exact cited titles.

## Work as a mathematical loop

Choose one object or tightly connected part of the argument. Read its Lean declarations, proofs,
dependencies, and blueprint nodes together. Ask what the shape of the map reveals:

- Is the proof using coordinates instead of an intrinsic object?
- Do parallel chains express one general theorem?
- Does a large detour hide an equivalence, universal property, grading, valuation, topology, or
  algebraic-independence argument?
- Is a difficult node hard to state because the Lean theorem is factored unnaturally?
- Would a mathematician introduce a lemma, change variables, or transport across an isomorphism and
  thereby make several constructions disappear?

Form one precise theory about the simplification. Before editing, record the present mathematical
objects, the proposed replacement, what concepts or case splits should disappear, and what observable
failure would refute the idea. Search pinned Mathlib and CombinatorialGames, then test the shortest
uncertain part in `tmp/`.

Change Lean whenever the theory identifies a truer mathematical route. Do not merely move logic,
wrap existing bookkeeping, rename invented concepts, or delete explanation. Lines matter only as
secondary evidence. Prefer a refactor that removes concepts, special cases, transports, declarations,
or nontrivial dependency steps.

After the Lean route settles, rewrite the blueprint in the field map's accepted terminology. Audit
every newly introduced noun phrase against that map. Every node must be one Lean declaration with
a concise mathematical name, an exact statement, and proof prose faithful to the actual Lean
proof. Follow the references' title convention: retain an established name when one exists;
otherwise use a transparent noun phrase built from standard objects and properties. A title names
the result; it does not repeat the proposition, narrate the proof, introduce terminology, or depend
on surrounding node labels. The generated guide prints it inline as `Theorem N (Title).` (or the
corresponding result kind), immediately before the statement. Read that combined text aloud: the
title and the opening sentence must form a natural mathematical heading without repetition or a
grammatical collision.

Recompute the selection rather than preserving yesterday's node list. Add anything that now belongs
to the minimal sufficient argument. Remove an old node only because its declaration disappeared,
became readily inferable, or was subsumed by a stronger selected result. The complete spine must
remain reconstructible; nodes never vanish merely to improve the diagram.

Measure the change by conceptual objects, theorem paths, case splits, and nontrivial dependencies,
with theorem and line counts as supporting data. Keep the refactor only when the mathematical reason
for the improvement is clear.

## Design chapters as mathematical seasons

Treat chapters as a linear filtration of the proof, not as labels pasted onto the existing node
order. A declaration or module in chapter `N` may depend on chapter `N` or an earlier chapter, but
never on a later one. Validate proposed boundaries against both the selected-declaration dependency
DAG and the Lean module-import DAG.

Do not mistake an arbitrary topological sort for a mathematical narrative. Ignore the current
chapter boundaries, compute the DAG's strongly connected components and transitive reduction, and
then look for genuine phase transitions:

- a change of objects, coordinates, invariant, or ambient category;
- a notable theorem that packages or supersedes the preceding machinery;
- a narrow interface through which an earlier part of the proof enters everything later;
- the point where independent preparatory branches meet and the main argument changes goal.

Use those milestones to constrain the topological order. Group a node with the first downstream
milestone whose proof needs it, keep one mathematical route contiguous when the partial order permits
it, and place shared prerequisites before the routes that use them. Prefer boundaries whose prefixes
are ancestor-closed and whose live frontier into the remaining graph consists of a few mathematically
recognizable results. Treat frontier size as diagnostic evidence, not an objective to optimize at the
expense of meaning.

For each proposed chapter, state its mathematical job, its entry coordinates, its culminating result
or honest stopping point, and the handoff to the next chapter. Check every cross-boundary edge and
explain any edge that bypasses the advertised handoff. Reorder nodes and discard the existing grouping
when a better valid filtration exists. Do not balance chapter sizes, optimize for diagram rendering,
or invent a season finale where the proof has no real transition; report a large continuous phase as
such when that is what the mathematics says.

Name every chapter and describe every transition using terminology accepted by the field map or a
literal statement in standard mathematical language. Never derive reader-facing language from a Lean
declaration, namespace, module path, repository directory, or internal abstraction. If the literature
does not name a phase, describe what its theorems establish instead of coining a name for it.

Run the relevant Lean and blueprint checks, then apply `review-blueprint` to the affected chain.
Reassess the new map, choose the next promising object, and continue this loop until the user asks
to stop. When one theory stops removing machinery, abandon it and form a different theory of the
proof space.
