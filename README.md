# A Proof of Conway’s Refinement Conjecture

50 years ago, in his book *On Numbers and Games*, John Conway proposed a conjecture:

<img width="500" height="267" alt="Conway's refinement conjecture: Omnific integers have a refinement property, i.e. if ab = cd for omnific integers, then there are further integers e, f, g, h with a = ef, b = gh, c = eg, d = fh." src="https://github.com/user-attachments/assets/2d905459-91d8-4ebd-98e6-89f3dfc998f7" />

He claims that if $a,b,c,d\in\mathbf{Oz}$ and $ab=cd$, then there are $e,f,g,h\in\mathbf{Oz}$ such that $a=ef$, $b=gh$, $c=eg$, and $d=fh$.

(If you're not familiar with omnific integers aka $\mathbf{Oz}$, I briefly describe them at the bottom.)

I believe that this repository contains a [proof](ConwayRefinement/Standalone/CombinatorialGames/ConwayRefinementProof.lean) of this conjecture, which you can explore through its [proof map](https://gaearon.github.io/conway-refinement/#/map/conway-refinement).

## About this proof

This proof was obtained in a somewhat unusual way.

I am not a mathematician, but I have an amateur level of interest in mathematics. Initially, after seeing all the recent headlines, I wanted to try an "AI proof" as an experiment. I asked Claude to pick an open problem about [surreal numbers](https://www.infinitelymore.xyz/p/surreal-numbers), a strange and beautiful invention (discovery?) of John Conway. Claude suggested this little conjecture because Sonia L'Innocente and Vincenzo Mantova had [recently made some progress toward it](https://www.sciencedirect.com/science/article/pii/S0001870824000288), so new pathways might have become available.

I couldn't "one-shot" the conjecture with AI, but this only got me more interested. I started wondering whether it was possible to make some progress if I steered the AI in some particular way. I would also have to figure out some way to know if I've actually made any progress, or if it's feeding me hallucinations. I thought it was funny and considerably absurd that I'm trying to do this without actually understanding the space, and I've limited my mathematical inquest to understanding what the *statement* says, but not anything about its proof methods.

Over the course of the last month, I've spent all my free time on it, repeatedly maxed out my 20x Pro usage for [ChatGPT](https://chatgpt.com/) and [Claude](https://claude.ai/) to generate potential "ideas" and then steered the AI into writing [Lean](https://lean-lang.org/) to sort out which of these ideas "agree" with acceptable mathematics.

This is probably why this proof ended up so long and confusing.

## Why I think it's correct

As anyone who's tried to prove things with Lean knows, there are two main dangers:

1. You may transitively [rely on bad axioms](https://overreacted.io/the-math-is-haunted/) or `sorry`s.
2. You may have proven a different statement than you intended.

To protect myself against these two dangers, I have taken two precautions.

### The CombinatorialGames formulation

The harder question is whether the Lean statement actually says what Conway's conjecture says. To make this easier to check, I put the statement in a standalone file with as little of "my" code as possible. [`ConwayRefinement.lean`](ConwayRefinement/Standalone/CombinatorialGames/ConwayRefinement.lean) uses only `Surreal` from [CombinatorialGames](https://github.com/vihdzp/combinatorial-games):

```lean
import CombinatorialGames.Surreal.Multiplication

universe u

/-- `x` is an omnific integer when it is the cut with
sole left option `x - 1` and sole right option `x + 1`. -/
abbrev IsConwayOmnificInteger (x : Surreal.{u}) : Prop :=
  x = !{{x - 1} | {x + 1}}' (by
    simp only [Set.mem_singleton_iff]
    rintro _ rfl _ rfl
    simp [sub_eq_add_neg])

/-- Conjecture: Every equality `a * b = c * d` of omnific integers
has an omnific refinement `a = e * f`, `b = g * h`, `c = e * g`, `d = f * h`. -/
abbrev ConwayConjecture : Prop :=
  ∀ a b c d : Surreal.{u},
    IsConwayOmnificInteger a → IsConwayOmnificInteger b →
    IsConwayOmnificInteger c → IsConwayOmnificInteger d → a * b = c * d →
    ∃ e f g h : Surreal.{u},
      IsConwayOmnificInteger e ∧ IsConwayOmnificInteger f ∧
      IsConwayOmnificInteger g ∧ IsConwayOmnificInteger h ∧
      a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h
```

Then I offer a proof of exactly that statement in [`ConwayRefinementProof.lean`](ConwayRefinement/Standalone/CombinatorialGames/ConwayRefinementProof.lean):

```lean
theorem proof : ConwayConjecture.{u} := by
  -- ...

#print axioms proof
```

which prints:

```text
'ConwayConjecture.proof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

*(CI also runs a linter [inspired by TauCeti](https://github.com/TauCetiProject/TauCeti/blob/main/scripts/Axioms.lean) that bans all other axioms from the entire project.)*

### The Mathlib-only formulation

Of course, you might not want to take the `Surreal` definition from CombinatorialGames on faith, so I also have a [Mathlib](https://github.com/leanprover-community/mathlib4)-only formulation in [`InlineConwayRefinement.lean`](ConwayRefinement/Standalone/Mathlib/InlineConwayRefinement.lean). It inlines every necessary definition from [CombinatorialGames](https://github.com/vihdzp/combinatorial-games/) into a ~250-line file.

The corresponding proof is in [`InlineConwayRefinementProof.lean`](ConwayRefinement/Standalone/Mathlib/InlineConwayRefinementProof.lean). It reports the same three axioms: `propext`, `Classical.choice`, and `Quot.sound`.

It is still quite possible that one or both of these statements do not correspond to Conway's conjecture in some small or big way, in which case this would not be a valid mathematical proof no matter what Lean says about it.

## Navigating the proof

While the above approach gave me some confidence in the validity of the proof, I am sure it is needlessly complicated and poorly explained. I've experimented with different ways to nudge the models into writing clearer mathematics, but it was difficult to get them to reliably write using standard terms, or to separate the core of the argument from bookkeeping or long detours that got fossilized in Lean.

Initially, I tried to generate a "paper". Eventually, I switched to [a proof guide website](https://gaearon.github.io/conway-refinement/), which is closer to what this project actually is. The website has AI-written descriptions of some Lean theorems that contribute to the top-level result. AI also chose which theorems to include. The tooling verifies that each numbered result actually corresponds to a checked piece of Lean code:

<img width="2660" height="1848" alt="Proof guide: statements" src="https://github.com/user-attachments/assets/c07b59ae-5a70-4216-9d93-60434e37f908" />

Inside these snippets, you can Cmd/Ctrl+Click any Lean identifier to open its source code on GitHub. For each selected theorem, you can step through the captured proof state at every character to retrace that part of the proof:

https://github.com/user-attachments/assets/04a4d2e8-913b-496c-95f2-b0decdec8811

The mathematical prose summarizing each Lean proof is written by AI and may contain mistakes. (There's an edit button if you'd like to contribute a fix.) I welcome pull requests that refine which theorems are selected for the website, or improve their factoring.

You can also select any result and see its "proof map", which traces its dependencies and consequences:

<img width="2660" height="1848" alt="Proof guide: map" src="https://github.com/user-attachments/assets/b4405de8-14b1-4b91-9e76-4307976e5139" />

I thought this might help a mathematical reader make some sense of the AI's argument. If you can propose a more direct path, please open an issue or a pull request. I would be happy to delete any uninteresting intermediate results, to factor the results differently, or to try another path as long as your proposal compiles or AI can get it to compile. If there is a better route, I can merge it and regenerate the proof map.

The [interactive guide](https://gaearon.github.io/conway-refinement/) is also available in [PDF form](https://gaearon.github.io/conway-refinement/blueprint.pdf), which you can save offline. Source code links inside them are versioned and link to the commit that they were built from.

If the result is correct, it might eventually be useful to cite it. I don't think the proof in this repository is in an acceptable state for that yet, but hopefully putting it out will either build confidence in the Lean result or debunk it. I also hope it serves as an example of another AI-driven experiment in proof exploration. I don't consider this completed mathematical work.

## Formalized results

The proof guide has a lot of intermediate steps. This is a shorter list of results and examples that I think are worth looking at. It includes every result from the guide's [Highlights page](https://gaearon.github.io/conway-refinement/#/highlights).

Each standalone statement is paired with a proof file. Each map shows how the result depends on the rest of the proof. Only Lean declarations explicitly annotated for the proof guide appear in these maps.

### The headline claim

| Formulation | Links |
|---|---|
| CombinatorialGames formulation of Conway's refinement conjecture | [statement](ConwayRefinement/Standalone/CombinatorialGames/ConwayRefinement.lean), [proof](ConwayRefinement/Standalone/CombinatorialGames/ConwayRefinementProof.lean), [map](https://gaearon.github.io/conway-refinement/#/map/conway-refinement) |
| Mathlib-only formulation of Conway's refinement conjecture | [statement](ConwayRefinement/Standalone/Mathlib/InlineConwayRefinement.lean), [proof](ConwayRefinement/Standalone/Mathlib/InlineConwayRefinementProof.lean), [map](https://gaearon.github.io/conway-refinement/#/map/conway-refinement) |

### Standalone statements over Mathlib

Each statement file in this table imports only Mathlib. Its paired proof connects it to the rest of the proof.

| Result | Links |
|---|---|
| For every Cauchy-complete ordered abelian group $G$, the ring of germs $K((G^{\le 0}))/J$ is a polynomial ring over $K$; hence $J$ is prime and germs have four-factor refinement | [statement](ConwayRefinement/Standalone/Mathlib/CompleteHahnGerm.lean), [proof](ConwayRefinement/Standalone/Mathlib/CompleteHahnGermProof.lean), [map](https://gaearon.github.io/conway-refinement/#/map/complete-hahn-germ-polynomial-algebra) |
| Polynomial presentation of $K((\mathbb R^{\le 0}))$ over its finite-support subring | [statement](ConwayRefinement/Standalone/Mathlib/HahnSeriesPolynomialRing.lean), [proof](ConwayRefinement/Standalone/Mathlib/HahnSeriesPolynomialRingProof.lean), [map](https://gaearon.github.io/conway-refinement/#/map/hahn-series-polynomial-algebra) |
| $K((\mathbb R^{\le 0}))$ is a GCD domain: every series is primal, irreducibles are prime, and irreducible factorisations are unique | [statement](ConwayRefinement/Standalone/Mathlib/HahnSeriesGCD.lean), [proof](ConwayRefinement/Standalone/Mathlib/HahnSeriesGCDProof.lean), [map](https://gaearon.github.io/conway-refinement/#/map/hahn-series-gcd-domain) |
| Berarducci's ring of germs $K((\mathbb R^{\le 0}))/J$ is a polynomial ring and a unique factorisation domain (Berarducci's conjecture as stated in [LM17, Conjecture 1.5]) | [statement](ConwayRefinement/Standalone/Mathlib/GermPolynomialRing.lean), [proof](ConwayRefinement/Standalone/Mathlib/GermPolynomialRingProof.lean), [map](https://gaearon.github.io/conway-refinement/#/map/complete-hahn-germ-polynomial-algebra) |
| In $\mathbb Q((\mathbb R^{\le 0}))$ the monomial $t^{-1}$ has an $n$-th root for every $n\ge 1$, so factorisations into nonunits can be arbitrarily long | [statement](ConwayRefinement/Standalone/Mathlib/Examples/NegativeMonomialRoots.lean), [proof](ConwayRefinement/Standalone/Mathlib/Examples/NegativeMonomialRootsProof.lean) |

### Other results and examples

These also have short statement and proof files, but their statements use code from this repository.

| Result | Links |
|---|---|
| Normal-form identification, every omnific integer primal, irreducibles prime, and uniqueness of irreducible factorisations in $\mathbf{Oz}$ | [statement](ConwayRefinement/Standalone/CombinatorialGames/Examples/OmnificFactorization.lean), [proof](ConwayRefinement/Standalone/CombinatorialGames/Examples/OmnificFactorizationProof.lean), [map](https://gaearon.github.io/conway-refinement/#/map/omnific-factorisation) |
| $\omega$ has an $n$-th root in $\mathbf{Oz}$ for every $n\ge 1$, so an omnific integer can have factorisations into arbitrarily many nonunits | [statement](ConwayRefinement/Standalone/CombinatorialGames/Examples/OmegaRoots.lean), [proof](ConwayRefinement/Standalone/CombinatorialGames/Examples/OmegaRootsProof.lean) |

### Results without separate statement files

These results don't have separate standalone statement files, but AI chose them as useful on their own or especially important to the proof.

| Result | Links |
|---|---|
| Transcendence lemma for germs of translated truncations | [source](ConwayRefinement/RingTheory/TruncationGerms/Transcendence.lean), [map](https://gaearon.github.io/conway-refinement/#/map/transcendence) |
| The ideal $J$ is prime for every Cauchy-complete exponent group, as a corollary of the polynomial presentation (for $G=\mathbb R$ this is Berarducci's theorem [Ber00, Cor. 9.8]) | [source](ConwayRefinement/HahnSeries/Germ/PolynomialRing.lean), [map](https://gaearon.github.io/conway-refinement/#/map/bounded-away-ideal-prime) |
| Every element of $Z+R((G^{<0}))_\kappa$ is primal, for $Z$ pre-Schreier, under conditions (A1)–(A3) of [LM24, Thm. 9.0.1] together with cofinality and Cauchy completeness at limits of Archimedean classes | [source](ConwayRefinement/HahnSeries/IntegerPart/Primality.lean), [map](https://gaearon.github.io/conway-refinement/#/map/hahn-integer-part-primality) |
| Refinement of $Z+K((G^{<0}))$ forces $K=\mathrm{Frac}(Z)$ | [source](ConwayRefinement/HahnSeries/IntegerPart/FractionField.lean), [map](https://gaearon.github.io/conway-refinement/#/map/refinement-forces-coefficient-fraction-field) |

Please open an issue if any of these are wrong or could be clearer.

## Proof maps

The proof map on the website is based on a dependency graph from specially marked theorems. I originally used [LeanArchitect](https://github.com/hanwenzhu/LeanArchitect) and [subverso](https://github.com/leanprover/subverso), but ended up slopforking both, so the tooling for the site is currently custom.

I also have a script that turns the proof map into the Mermaid diagrams below:

<!-- blueprint-mermaid:start -->
### Proof overview

```mermaid
%% Generated by scripts/blueprint.sh; do not edit.
%% Edge labels count visible result dependencies.
flowchart TB
  p0["Two primality criteria<br/>2 results"]:::phase
  p1["Germs of translated truncations<br/>8 results"]:::phase
  p2["Polynomial presentations<br/>18 results"]:::phase
  p3["Reduction along Archimedean classes<br/>9 results"]:::phase
  p4["Surreal numbers and omnific integers<br/>10 results"]:::phase
  p1 -->|"5"| p2
  p2 -->|"3"| p3
  p0 -->|"2"| p3
  p3 -->|"1"| p4
  click p0 "https://gaearon.github.io/conway-refinement/#/chapter/primality-criteria" "Open Two primality criteria"
  click p1 "https://gaearon.github.io/conway-refinement/#/chapter/germs" "Open Germs of translated truncations"
  click p2 "https://gaearon.github.io/conway-refinement/#/chapter/polynomial-presentations" "Open Polynomial presentations"
  click p3 "https://gaearon.github.io/conway-refinement/#/chapter/archimedean-reduction" "Open Reduction along Archimedean classes"
  click p4 "https://gaearon.github.io/conway-refinement/#/chapter/conway-refinement" "Open Surreal numbers and omnific integers"

  classDef phase fill:#f8fafc,stroke:#475569,stroke-width:2px,color:#111827
```

<a id="phase-primality-criteria"></a>
<details>
<summary>Two primality criteria</summary>

```mermaid
%% Generated by scripts/blueprint.sh; do not edit.
%% Other sections are compressed to boundary nodes.
%% Solid arrows are proof dependencies; dashed arrows are statement dependencies.
flowchart TB
  subgraph current["Two primality criteria"]
    direction TB
    n001["(1) Primality in a D + M construction"]:::lemma
    n002["(2) Primality via a quotient and retractions"]:::lemma
  end
  subgraph outputs["Used by other sections"]
    direction TB
    out0["Reduction along Archimedean classes<br/>2 results used downstream"]:::boundary
  end

  n001 --> out0
  n002 --> out0
  click n001 "https://gaearon.github.io/conway-refinement/#/result/primality-in-d-plus-m" "Open the statement for lemma 1"
  click n002 "https://gaearon.github.io/conway-refinement/#/result/primality-from-germs-and-restrictions" "Open the statement for lemma 2"

  classDef theorem fill:#fff3bf,stroke:#e67700,stroke-width:2px,color:#111827
  classDef definition fill:#f3f4f6,stroke:#4b5563,color:#111827
  classDef lemma fill:#dbeafe,stroke:#2563eb,color:#111827
  classDef proposition fill:#ede9fe,stroke:#7c3aed,color:#111827
  classDef corollary fill:#dcfce7,stroke:#16a34a,color:#111827
  classDef fact fill:#fce7f3,stroke:#db2777,color:#111827
  classDef boundary fill:#f8fafc,stroke:#64748b,stroke-dasharray:4 3,color:#334155
```
</details>

<a id="phase-germs"></a>
<details>
<summary>Germs of translated truncations</summary>

```mermaid
%% Generated by scripts/blueprint.sh; do not edit.
%% Other sections are compressed to boundary nodes.
%% Solid arrows are proof dependencies; dashed arrows are statement dependencies.
flowchart TB
  subgraph current["Germs of translated truncations"]
    direction TB
    n003["(3) Cantor–Bendixson value"]:::definition
    n004["(4) The ideal J"]:::definition
    n005["(5) Germ of a series at an exponent"]:::definition
    n006["(6) Germs of a translated truncation"]:::lemma
    n007["(7) Decrease of the Cantor–Bendixson value under translated truncation"]:::lemma
    n008["(8) Convolution formula"]:::lemma
    n009["(9) Exponents with nonzero germ"]:::lemma
    n010["(10) Characterisation of constant germs"]:::lemma
  end
  subgraph outputs["Used by other sections"]
    direction TB
    out0["Polynomial presentations<br/>4 results used downstream"]:::boundary
  end

  n004 --> n005
  n005 --> n006
  n003 --> n007
  n003 --> n008
  n005 --> n008
  n003 --> n009
  n005 --> n009
  n003 --> n010
  n006 --> n010
  n009 --> out0
  n010 --> out0
  n007 --> out0
  n008 --> out0
  click n003 "https://gaearon.github.io/conway-refinement/#/result/cantor-bendixson-value" "Open the statement for definition 3"
  click n004 "https://gaearon.github.io/conway-refinement/#/result/bounded-away-ideal" "Open the statement for definition 4"
  click n005 "https://gaearon.github.io/conway-refinement/#/result/germ-at" "Open the statement for definition 5"
  click n006 "https://gaearon.github.io/conway-refinement/#/result/germs-of-translated-truncation" "Open the statement for lemma 6"
  click n007 "https://gaearon.github.io/conway-refinement/#/result/cantor-bendixson-value-drop" "Open the statement for lemma 7"
  click n008 "https://gaearon.github.io/conway-refinement/#/result/convolution-formula" "Open the statement for lemma 8"
  click n009 "https://gaearon.github.io/conway-refinement/#/result/nonzero-germs" "Open the statement for lemma 9"
  click n010 "https://gaearon.github.io/conway-refinement/#/result/constant-germs" "Open the statement for lemma 10"

  classDef theorem fill:#fff3bf,stroke:#e67700,stroke-width:2px,color:#111827
  classDef definition fill:#f3f4f6,stroke:#4b5563,color:#111827
  classDef lemma fill:#dbeafe,stroke:#2563eb,color:#111827
  classDef proposition fill:#ede9fe,stroke:#7c3aed,color:#111827
  classDef corollary fill:#dcfce7,stroke:#16a34a,color:#111827
  classDef fact fill:#fce7f3,stroke:#db2777,color:#111827
  classDef boundary fill:#f8fafc,stroke:#64748b,stroke-dasharray:4 3,color:#334155
```
</details>

<a id="phase-polynomial-presentations"></a>
<details>
<summary>Polynomial presentations</summary>

```mermaid
%% Generated by scripts/blueprint.sh; do not edit.
%% Other sections are compressed to boundary nodes.
%% Solid arrows are proof dependencies; dashed arrows are statement dependencies.
flowchart TB
  subgraph inputs["Inputs from other sections"]
    direction TB
    in0["Germs of translated truncations<br/>used by 2 results"]:::boundary
  end
  subgraph current["Polynomial presentations"]
    direction TB
    n011["(11) Greatest common divisors of finite-support series"]:::fact
    n012["(12) Series with constant germs"]:::lemma
    n013["(13) Axioms for germs of translated truncations"]:::definition
    n014["(14) The germs of K((G^{≤ 0})) form a system of germs"]:::proposition
    n015["(15) Axioms for germs on a ring of series"]:::definition
    n016["(16) Closure under truncation of a simple extension"]:::lemma
    n017["(17) Transcendence of a series with transcendental germ"]:::lemma
    n018["(18) Generation by a subalgebra closed under truncation"]:::lemma
    n019["(19) Proportionality lemma"]:::lemma
    n020["(20) Absence of linear relations"]:::lemma
    n021["(21) Transcendence lemma"]:::lemma
    n022["(22) Algebraically independent generators of the ring of germs"]:::theorem
    n023["(23) Polynomial presentation of the ring of germs of series with small support"]:::theorem
    n024["(24) Polynomial presentation of the ring of germs"]:::theorem
    n025["(25) Primality of J"]:::theorem
    n026["(26) Algebraically independent generators of the ring of series"]:::theorem
    n027["(27) Polynomial presentation of K((ℝ^{≤ 0}))"]:::theorem
    n028["(28) Greatest common divisors in K((ℝ^{≤ 0}))"]:::theorem
  end
  subgraph outputs["Used by other sections"]
    direction TB
    out0["Reduction along Archimedean classes<br/>3 results used downstream"]:::boundary
  end

  n013 --> n014
  n013 --> n016
  n015 --> n016
  n013 --> n017
  n015 --> n017
  n013 --> n018
  n015 --> n018
  n013 --> n019
  n013 --> n020
  n019 --> n021
  n020 --> n021
  n021 --> n022
  n014 --> n023
  n022 --> n023
  n014 --> n024
  n022 --> n024
  n024 --> n025
  n016 --> n026
  n017 --> n026
  n018 --> n026
  n022 --> n026
  n012 --> n027
  n014 --> n027
  n026 --> n027
  n011 --> n028
  n027 --> n028
  in0 --> n012
  in0 --> n014
  n024 --> out0
  n028 --> out0
  n023 --> out0
  click n011 "https://gaearon.github.io/conway-refinement/#/result/finite-support-hahn-gcd" "Open the statement for fact 11"
  click n012 "https://gaearon.github.io/conway-refinement/#/result/constant-germs-finite-support" "Open the statement for lemma 12"
  click n013 "https://gaearon.github.io/conway-refinement/#/result/germ-axioms" "Open the statement for definition 13"
  click n014 "https://gaearon.github.io/conway-refinement/#/result/hahn-germs-axioms" "Open the statement for proposition 14"
  click n015 "https://gaearon.github.io/conway-refinement/#/result/series-germ-axioms" "Open the statement for definition 15"
  click n016 "https://gaearon.github.io/conway-refinement/#/result/truncation-closed-adjunction" "Open the statement for lemma 16"
  click n017 "https://gaearon.github.io/conway-refinement/#/result/transcendence-of-series" "Open the statement for lemma 17"
  click n018 "https://gaearon.github.io/conway-refinement/#/result/generation" "Open the statement for lemma 18"
  click n019 "https://gaearon.github.io/conway-refinement/#/result/proportionality" "Open the statement for lemma 19"
  click n020 "https://gaearon.github.io/conway-refinement/#/result/no-linear-relations" "Open the statement for lemma 20"
  click n021 "https://gaearon.github.io/conway-refinement/#/result/transcendence" "Open the statement for lemma 21"
  click n022 "https://gaearon.github.io/conway-refinement/#/result/germ-ring-generators" "Open the statement for theorem 22"
  click n023 "https://gaearon.github.io/conway-refinement/#/result/bounded-hahn-germ-polynomial-algebra" "Open the statement for theorem 23"
  click n024 "https://gaearon.github.io/conway-refinement/#/result/complete-hahn-germ-polynomial-algebra" "Open the statement for theorem 24"
  click n025 "https://gaearon.github.io/conway-refinement/#/result/bounded-away-ideal-prime" "Open the statement for theorem 25"
  click n026 "https://gaearon.github.io/conway-refinement/#/result/series-ring-generators" "Open the statement for theorem 26"
  click n027 "https://gaearon.github.io/conway-refinement/#/result/hahn-series-polynomial-algebra" "Open the statement for theorem 27"
  click n028 "https://gaearon.github.io/conway-refinement/#/result/hahn-series-gcd-domain" "Open the statement for theorem 28"

  classDef theorem fill:#fff3bf,stroke:#e67700,stroke-width:2px,color:#111827
  classDef definition fill:#f3f4f6,stroke:#4b5563,color:#111827
  classDef lemma fill:#dbeafe,stroke:#2563eb,color:#111827
  classDef proposition fill:#ede9fe,stroke:#7c3aed,color:#111827
  classDef corollary fill:#dcfce7,stroke:#16a34a,color:#111827
  classDef fact fill:#fce7f3,stroke:#db2777,color:#111827
  classDef boundary fill:#f8fafc,stroke:#64748b,stroke-dasharray:4 3,color:#334155
```
</details>

<a id="phase-archimedean-reduction"></a>
<details>
<summary>Reduction along Archimedean classes</summary>

```mermaid
%% Generated by scripts/blueprint.sh; do not edit.
%% Other sections are compressed to boundary nodes.
%% Solid arrows are proof dependencies; dashed arrows are statement dependencies.
flowchart TB
  subgraph inputs["Inputs from other sections"]
    direction TB
    in0["Two primality criteria<br/>used by 2 results"]:::boundary
    in1["Polynomial presentations<br/>used by 3 results"]:::boundary
  end
  subgraph current["Reduction along Archimedean classes"]
    direction TB
    n029["(29) Restriction to a convex subgroup"]:::lemma
    n030["(30) Divisibility from a convex restriction"]:::lemma
    n031["(31) Factorisation by a convex restriction"]:::lemma
    n032["(32) Refinement forces K = Frac(Z)"]:::theorem
    n033["(33) Primality through regrouping along a convex subgroup"]:::lemma
    n034["(34) Primality for finitely many Archimedean classes"]:::theorem
    n035["(35) Factorisation at an Archimedean class of a quotient"]:::lemma
    n036["(36) Primality at a limit of Archimedean classes"]:::theorem
    n037["(37) Primality in Z + R((G^{&lt; 0}))_κ"]:::theorem
  end
  subgraph outputs["Used by other sections"]
    direction TB
    out0["Surreal numbers and omnific integers<br/>1 results used downstream"]:::boundary
  end

  n029 --> n034
  n030 --> n034
  n033 --> n034
  n031 --> n035
  n029 --> n036
  n030 --> n036
  n033 --> n036
  n035 --> n036
  n034 --> n037
  n036 --> n037
  in1 --> n032
  in0 --> n033
  in1 --> n034
  in0 --> n036
  in1 --> n036
  n037 --> out0
  click n029 "https://gaearon.github.io/conway-refinement/#/result/convex-restriction-ring-hom" "Open the statement for lemma 29"
  click n030 "https://gaearon.github.io/conway-refinement/#/result/divisibility-from-convex-restriction" "Open the statement for lemma 30"
  click n031 "https://gaearon.github.io/conway-refinement/#/result/factorisation-by-convex-restriction" "Open the statement for lemma 31"
  click n032 "https://gaearon.github.io/conway-refinement/#/result/refinement-forces-coefficient-fraction-field" "Open the statement for theorem 32"
  click n033 "https://gaearon.github.io/conway-refinement/#/result/primality-through-regrouping" "Open the statement for lemma 33"
  click n034 "https://gaearon.github.io/conway-refinement/#/result/finite-support-classes-primality" "Open the statement for theorem 34"
  click n035 "https://gaearon.github.io/conway-refinement/#/result/support-class-factorisation" "Open the statement for lemma 35"
  click n036 "https://gaearon.github.io/conway-refinement/#/result/limit-tail-step" "Open the statement for theorem 36"
  click n037 "https://gaearon.github.io/conway-refinement/#/result/hahn-integer-part-primality" "Open the statement for theorem 37"

  classDef theorem fill:#fff3bf,stroke:#e67700,stroke-width:2px,color:#111827
  classDef definition fill:#f3f4f6,stroke:#4b5563,color:#111827
  classDef lemma fill:#dbeafe,stroke:#2563eb,color:#111827
  classDef proposition fill:#ede9fe,stroke:#7c3aed,color:#111827
  classDef corollary fill:#dcfce7,stroke:#16a34a,color:#111827
  classDef fact fill:#fce7f3,stroke:#db2777,color:#111827
  classDef boundary fill:#f8fafc,stroke:#64748b,stroke-dasharray:4 3,color:#334155
```
</details>

<a id="phase-conway-refinement"></a>
<details>
<summary>Surreal numbers and omnific integers</summary>

```mermaid
%% Generated by scripts/blueprint.sh; do not edit.
%% Other sections are compressed to boundary nodes.
%% Solid arrows are proof dependencies; dashed arrows are statement dependencies.
flowchart TB
  subgraph inputs["Inputs from other sections"]
    direction TB
    in0["Reduction along Archimedean classes<br/>used by 1 results"]:::boundary
  end
  subgraph current["Surreal numbers and omnific integers"]
    direction TB
    n038["(38) Condition (A1)_σ for the surreal numbers"]:::fact
    n039["(39) Cofinality of surreal Archimedean balls"]:::fact
    n040["(40) Cofinality of intersections of surreal Archimedean balls"]:::lemma
    n041["(41) Filling small cuts in the surreal numbers"]:::theorem
    n042["(42) Conway normal form of omnific integers"]:::theorem
    n043["(43) A cut criterion for Cauchy completeness"]:::lemma
    n044["(44) Cauchy completeness of surreal quotients"]:::lemma
    n045["(45) Primality in ℤ + ℝ((No^{&lt; 0}))_κ"]:::theorem
    n046["(46) Conway's refinement theorem for omnific integers"]:::theorem
    n047["(47) Irreducible omnific integers are prime"]:::theorem
  end

  n041 --> n044
  n043 --> n044
  n038 --> n045
  n039 --> n045
  n040 --> n045
  n044 --> n045
  n042 --> n046
  n045 --> n046
  n042 --> n047
  n045 --> n047
  in0 --> n045
  click n038 "https://gaearon.github.io/conway-refinement/#/result/surreal-archimedean-strata" "Open the statement for fact 38"
  click n039 "https://gaearon.github.io/conway-refinement/#/result/surreal-archimedean-ball-cofinality" "Open the statement for fact 39"
  click n040 "https://gaearon.github.io/conway-refinement/#/result/surreal-common-tail-cofinality" "Open the statement for lemma 40"
  click n041 "https://gaearon.github.io/conway-refinement/#/result/surreal-simplicity-small-cuts" "Open the statement for theorem 41"
  click n042 "https://gaearon.github.io/conway-refinement/#/result/signed-normal-form-omnific-integer-equivalence" "Open the statement for theorem 42"
  click n043 "https://gaearon.github.io/conway-refinement/#/result/complete-of-coinitial-scales-and-cut-filling" "Open the statement for lemma 43"
  click n044 "https://gaearon.github.io/conway-refinement/#/result/surreal-common-tail-quotient-complete" "Open the statement for lemma 44"
  click n045 "https://gaearon.github.io/conway-refinement/#/result/surreal-hahn-integer-part-primality" "Open the statement for theorem 45"
  click n046 "https://gaearon.github.io/conway-refinement/#/result/conway-refinement" "Open the statement for theorem 46"
  click n047 "https://gaearon.github.io/conway-refinement/#/result/omnific-factorisation" "Open the statement for theorem 47"

  classDef theorem fill:#fff3bf,stroke:#e67700,stroke-width:2px,color:#111827
  classDef definition fill:#f3f4f6,stroke:#4b5563,color:#111827
  classDef lemma fill:#dbeafe,stroke:#2563eb,color:#111827
  classDef proposition fill:#ede9fe,stroke:#7c3aed,color:#111827
  classDef corollary fill:#dcfce7,stroke:#16a34a,color:#111827
  classDef fact fill:#fce7f3,stroke:#db2777,color:#111827
  classDef boundary fill:#f8fafc,stroke:#64748b,stroke-dasharray:4 3,color:#334155
```
</details>
<!-- blueprint-mermaid:end -->

These diagrams can also help AI refactor or simplify the overall proof path.

## But what was the conjecture about?

This conjecture is about *omnific integers*.

Omnific integers were invented (or discovered?) by John Conway. Intuitively, I'd describe them as an extension of integers as we know them ($-3$, $10$, $1840$, $-437349$) to infinity and beyond. Recall that there is no biggest integer: after $1$ comes $2$, after $2$ comes $3$, and so on. So if you say some $X$ is the biggest integer, I would point to $X + 1$, which is bigger, and you would be wrong. However, omnific integers *do* contain a number bigger than every regular integer. It's called $\omega$, "omega", and in a sense it represents an infinity: $\omega$ is "what stands after" every regular integer.

You might think that it ends there, but it doesn't.

You can add $1$ to get $\omega + 1$, then add $1$ again to get $\omega + 2$, and so on. Curiously, you can also go *backwards* — to $\omega - 1$, $\omega - 2$, $\omega - 800$, and so on. No matter how many finite steps you go down, you will never reach the "regular" integers. If you started off from $\omega$, you're just *too high already* to ever reach the regular integers. And it doesn't end here either. You can divide $\omega$, for example $\omega / 2$, and it would *still* be bigger than all regular integers. (Curiously, $\omega$ is even — it is divisible by 2 — but it is also divisible by 3, 4, or really by any integer except zero.)

You could also keep going up — perhaps, after another infinity of steps, reaching $\omega + \omega = \omega \cdot 2$, or further up to $\omega \cdot 3$, or, after making infinite jumps, to $\omega \cdot \omega = \omega^2$. You could keep going (or rather, "jumping" — walking can't even get you to $\omega$), stacking powers of omega into ever taller towers:

$$
\omega,\qquad \omega^\omega,\qquad \omega^{\omega^\omega},\qquad \ldots
$$

Now "jump" through doing *that* forever, and you'll reach a tower so tall that raising $\omega$ to it doesn't change it:

$$\omega^{\left(\omega^{\omega^{\omega^{\cdots}}}\right)} = \omega^{\omega^{\omega^{\cdots}}}.$$

And yet you could still keep on going.

All of this is very strange, but what is stranger is that it all "falls out" of a very simple theory.

Forget all the numbers you know. Define a single number called "zero" and then go step by step. At every step, invent a new number at each distinct gap between the numbers you already have ("to the left of all" and "to the right of all" also count as gaps). Continue doing this forever, and then forevermore forever, and so on.

Turns out, if you do this forever, you'll get a fractal tree of [all numbers great and small](https://upload.wikimedia.org/wikipedia/commons/4/49/Surreal_number_tree.svg):

<img width="500" height="618" alt="Surreal tree illustration by Joel David Hamkins" src="https://github.com/user-attachments/assets/5bcec33f-e41b-41af-b736-515df166388b" />

*(Illustration by Joel David Hamkins, go [read his posts](https://www.infinitelymore.xyz/p/surreal-numbers) and [buy his book!](https://jdh.hamkins.org/the-book-of-infinity/))*

This simple recursive binary tree turns out to produce exactly the numbers we commonly use in life — naturals, integers, rationals, reals — as well as weirder numbers such as infinite "ordinals" like $\omega$, "infinitesimals" like $\frac{1}{\omega}$, and all sorts of combinations between them, such as $\omega^2+\pi\omega-7+\frac{3}{\omega}+\frac{1}{\omega^2}$.

These beautiful and strange numbers are called *surreal numbers*.

Omnific integers are the "whole" part of the surreal number tree. Turns out, every surreal number can be seen as a result of division $A/B$ of two omnific integers $A$ and $B$. This is true even for familiar irrationals like $\sqrt{2}$. No ratio of regular integers can equal $\sqrt{2}$, but you get it if you divide $\sqrt{2}\omega$ by $\omega$, and both of these are omnific integers. (Yep, $\sqrt{2}\omega$ is a "whole" number! The bigness of $\omega$ "swallows up" the infinite precision of a real number like $\sqrt{2}$, leaving no fractional part.) That's why Conway called them omnific, i.e. "all-creating". Their ratios "create" every number.

Finally, the conjecture.

Conway claims that if $ab = cd$, we can "break down" $a$ and $b$ into pieces, and then $c$ and $d$ will turn out to be the same pieces recombined. With regular integers, we take this for granted. Say 210 = 10 × 21. We can break 10 down as 2 × 5 and 21 as 3 × 7, then reshuffle them into 2 × 3 = 6 and 5 × 7 = 35. The product is still 6 × 35 = 210.

However, when you deal with infinities, things don't always turn out as we expect. So the conjecture means Conway thought omnific integers had, in a sense, enough "structure" to keep this property. It happens that every surreal number can also be written as a certain kind of infinite series, with omnific integers being a special case. This lets us study how omnific integers break apart by studying how these series break apart. Over the years, Berarducci, Pitteloud, Pommersheim and Shahriari, and L'Innocente and Mantova developed increasingly strong results about exactly that. This proof builds on all of that work and claims to finish the refinement conjecture.

Or at least so I would hope!

## Discussion

If you want to say or ask something, feel free to use Issues or Discussions.

You can also find me on Bluesky as [`@danabra.mov`](https://bsky.app/profile/danabra.mov).

Thank you for reading!

## Build

```text
lake build
lake exe palomar-compatibility
lake exe module-system
lake exe axioms
lake exe standalone-mathlib
lake exe standalone-combinatorial-games
lake exe proof-links
lake exe style
lake exe documentation
lake exe layering
scripts/lint-env.sh
scripts/blueprint.sh build
```

For release, run `scripts/publish-blueprint.sh` from a clean commit.

This runs the release gates and generates the PDF and the website. Release history is in [`CHANGELOG.md`](CHANGELOG.md).

## License

Apache License Version 2.0

## References

- J. H. Conway, *On Numbers and Games*, London Mathematical Society Monographs, no. 6, Academic Press, 1976.
- M. Zafrullah, “[On a property of pre-Schreier domains](https://doi.org/10.1080/00927878708823512),” *Comm. Algebra* **15** (1987), no. 9, 1895–1920.
- A. Berarducci, “[Factorization in generalized power series](https://doi.org/10.1090/S0002-9947-99-02172-8),” *Trans. Amer. Math. Soc.* **352** (2000), no. 2, 553–577.
- D. Pitteloud, “[Existence of prime elements in rings of generalized power series](https://doi.org/10.2307/2695102),” *J. Symbolic Logic* **66** (2001), no. 3, 1206–1216.
- D. Pitteloud, “[Algebraic properties of rings of generalized power series](https://doi.org/10.1016/S0168-0072(01)00099-9),” *Ann. Pure Appl. Logic* **116** (2002), nos. 1–3, 39–66.
- J. Pommersheim and S. Shahriari, “[Unique factorization in generalized power series rings](https://doi.org/10.1090/S0002-9939-05-08162-1),” *Proc. Amer. Math. Soc.* **134** (2006), no. 5, 1277–1287.
- S. L'Innocente and V. Mantova, “[Factorisation of germ-like series](https://doi.org/10.4115/jla.2017.9.3),” *J. Log. Anal.* **9** (2017), no. 3, 1–16.
- S. L'Innocente and V. Mantova, “[A factorisation theory for generalised power series and omnific integers](https://doi.org/10.1016/j.aim.2024.109513),” *Adv. Math.* **442** (2024), 109513.
- A. Fornasiero, N. Lavi, S. L'Innocente and V. Mantova, “[Irreducibility in generalized power series](https://arxiv.org/abs/2405.13815),” arXiv:2405.13815v1 (2024).
