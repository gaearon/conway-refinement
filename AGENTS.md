# Conway Refinement working rules

`README.md` states the results and reading order. These rules govern changes to the Lean
development and its generated proof blueprint.

## Mathematical standard

- Lean is the authority for what is proved. State exact quantifiers, ambient hypotheses, zero and
  degenerate cases, inequalities, and equality orientations.
- Use established mathematical terminology in declaration names, statements, docstrings, and the
  blueprint. `blueprint/terminology/FIELD.md`, especially Part 0, records the vocabulary chosen for
  this project.
- Follow Mathlib and dependency spelling in Lean module paths, declaration names, and exact API
  references. Reader-facing prose and the blueprint follow the field map. Thus Lean uses
  `Factorization`, while mathematical prose uses “factorisation”; preserve cited titles verbatim.
- A theorem attributed to a source retains every mathematically relevant source hypothesis. Put a
  stronger generalization in a separate declaration and identify it as such.
- Validate a new definition with characteristic lemmas and a nondegenerate example that separates
  it from the nearest plausible wrong definition. Compilation alone does not establish fidelity.
- Search pinned Mathlib and CombinatorialGames before introducing a definition or substantial
  proof. Reuse their natural namespace, notation, theorem shape, and API when the mathematics
  agrees. Do not edit pinned dependencies in place.
- No declaration under `ConwayRefinement/` may use `sorry`, directly or transitively. The only
  admitted axioms there are `propext`, `Classical.choice`, and `Quot.sound`, as enforced by
  `lake exe axioms`. The root-level Palomar `Challenge.lean` may contain only its advertised hole;
  it imports no project module, is paired with the proved `Solution.lean`, and is checked for exact
  statement drift in CI.

## Repository architecture

Modules are organized by their mathematical objects. General mathematics lives under `Algebra/`,
`Data/`, `FieldTheory/`, `LinearAlgebra/`, `Order/`, `RingTheory/`, `SetTheory/`, and `Topology/`.
The main subject modules live under `HahnSeries/` and `Surreal/`; their subdirectories name the
mathematical construction or conclusion, such as ordinal value, polynomial algebra, factorization,
integer parts, and omnific integers. Source attribution belongs in module documentation and the
source index, not in the directory name.

Imports run from general mathematics to Hahn series to surreal numbers. `Examples/`, `Standalone/`,
and local `Tests/` directories are leaves. `Tests/` contains compiled clients of nearby public APIs,
while `Examples/` contains reader-worthy mathematics.

`lake exe layering` enforces these boundaries. `ConwayRefinement/` is a module root, not a namespace
requirement; generic declarations belong in mathematical namespaces such as `HahnSeries`.

Every Lean file uses the module system. Begin with `module`, use `public import` exactly when an
imported name occurs in an exported type, and put exported declarations in a `public section` or
`public noncomputable section`. Import the module that directly provides each name or instance.
`lake build` is authoritative because the `ConwayRefinement.*` glob compiles every source file.

Keep the pinned Lean, Mathlib, CombinatorialGames, and SubVerso revisions fixed during a
mathematical change. A dependency update is its own reviewed change.

## Standalone entry points

Top-level files in `ConwayRefinement/Standalone/Mathlib/` and
`ConwayRefinement/Standalone/CombinatorialGames/` are mathematical claims intended to be read by a
mathematician as single files.

- A top-level claim file states a substantive result in immediately recognizable mathematical
  language. A reader must not need to follow a project definition to decide what it says; inline
  the relevant predicate or display an exact elementary characterization in the file.
- Keep narration short. Docstrings describe the object or conclusion, never implementation history,
  proof status, or editorial plans.
- A sibling `FooProof.lean` supplies the proof of every closed proposition in `Foo.lean`. The proof
  file should make the connection to the statement easy to inspect and move unrelated machinery to
  `Support/`.
- `Support/` is for definitions and lemmas needed only to elaborate proofs. `Examples/` contains
  results worth reading in their own right.
- Mathlib statement files import only Mathlib. CombinatorialGames statement files may additionally
  import CombinatorialGames. Neither imports another project module. Proof siblings are the explicit
  exception and may import the development.

The compiled isolation and pairing rules are enforced by `lake exe standalone-mathlib`,
`lake exe standalone-combinatorial-games`, and `lake exe proof-links`.

## Lean API and source style

- Keep public definition bodies opaque. Provide the characteristic, membership, coercion,
  evaluation, extensionality, and operation lemmas needed by downstream clients.
- Do not rely on accidental definitional equality across modules. Add a public eliminator or pass
  explicit data. Use `@[expose]` only when computation is intentionally public and a separate client
  demonstrates the need.
- Test public interfaces in separately compiled local `Tests/` clients. Include zero, degenerate, and
  nondegenerate cases where they distinguish the intended semantics.
- Prefer dependency-native notation and dot notation. Introduce syntax only when it clarifies a
  repeated mathematical distinction.
- Public definitions and principal theorems receive concise mathematical docstrings. Module
  documentation explains purpose, conventions, and source. Git history and PRs carry development
  history.
- Follow Mathlib formatting and keep lines at most 100 characters. Do not weaken warnings or
  linters. A `@[nolint]` requires a mathematical justification and an allowlist entry.

## Blueprint: refine and review

The proof blueprint is generated from inline `@[blueprint]` annotations. It records the minimal
mathematical spine from which a research mathematician can reconstruct the proof, using the
notation and terminology fixed by `blueprint/terminology/FIELD.md`; it is not a second
hand-maintained statement tree. Read `blueprint/README.md` for the selection contract.

Blueprint titles are emitted as LaTeX optional theorem arguments. Never put a raw `]` in a title:
write `\\lbrack` and `\\rbrack` in the Lean string for mathematical brackets and right endpoints.
The doubled backslashes are required by Lean string syntax.

Use `refine-blueprint` as an iterative research loop. Make the map faithful and useful, then use its
shape to detect Lean proofs written in the wrong objects, coordinates, or theorem factorization.
Form one mathematical simplification hypothesis, prototype it, and refactor Lean when it removes
real concepts, cases, transports, or dependency steps. Recompute the node selection after every
such change: add newly necessary mathematics and remove a node only for a stated mathematical
reason. Continue until the user asks to stop.

Use `review-blueprint` as a proportional correctness gate. Review the smallest complete inference
chain affected by a change to mathematical factoring, selection, a selected signature, proof route,
or visible dependency. Trivial edits that change none of these need no blueprint review. A final PR
or release review covers every selected declaration without sampling.

For every selected node:

- one node is exactly one Lean declaration;
- the title is a concise mathematical name for the result, while the statement gives the exact
  proposition. Follow the references' convention: use an established name when one exists
  (for example, “convolution formula” or “Leibniz rule”); otherwise use a transparent noun phrase
  built from standard objects and properties, such as “Injectivity of …”, “Multiplicativity of …”,
  or “… decomposition”. Never invent terminology merely to title a node, restate the whole theorem
  in the title, use proof narration as a title, or rely on pronouns and surrounding nodes;
- multiple conclusions appear only when the Lean type returns them together;
- statement and proof prose exactly match the full Lean signature and actual proof;
- proof prose cites exactly the visible immediate blueprint predecessors;
- the vocabulary is standard and source attributions are checked at their primary pinpoints.

Never add dummy theorem uses or prose references to shape the dependency graph. When an implication
is not reconstructible from the visible predecessors, select the missing nontrivial declaration or
improve the Lean factorization.

## Workflow

1. Fix the intended mathematical statement and search the pinned dependencies.
2. Prototype uncertain mathematics in `tmp/`; keep `tmp/` empty at committed checkpoints. Test
   opaque public interfaces with separate producer and consumer modules.
3. Move only a typechecked design into its semantic module and add the smallest meaningful client.
4. If the mathematical shape changed, update the blueprint and run `review-blueprint` on the
   affected chain.
5. Run focused checks while iterating. Before a green checkpoint run:

   ```text
   lake build
   lake exe module-system
   lake exe axioms
   lake exe standalone-mathlib
   lake exe standalone-combinatorial-games
   lake exe proof-links
   lake exe style
   lake exe documentation
   lake exe layering
   scripts/blueprint.sh build
   ```

6. When changing an audit executable, extend `scripts/audit-probes.sh` so the checker must reject a
   representative bad input.
7. Inspect the exact diff, do the proportional blueprint review, and commit one coherent change.
   Do not stage unrelated user work.
8. Before merging a PR, review every blueprint node and run `scripts/release-audit.sh` from the
   clean committed candidate. Any repair reopens its affected mathematical chain. GitHub Actions
   publishes the web guide and PDF only after the same source commit passes the Lean gates; every
   generated source link and guide title records that exact commit.

A direct one-file check must pass the package options explicitly:

```text
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false FILE.lean
```
