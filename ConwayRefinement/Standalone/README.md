# Standalone statements

These files isolate the main claims from the machinery used to prove them. Each statement file is
paired with a proof file. Mathlib statements import only Mathlib; the statements under
`CombinatorialGames/` import CombinatorialGames and Mathlib.

## Conway's refinement conjecture

All three entry points state the same four-factor conclusion

$$
ab=cd \Longrightarrow
a=ef,\quad b=gh,\quad c=eg,\quad d=fh.
$$

| Formulation | Statement | Proof |
|---|---|---|
| Surreal numbers defined inline from Mathlib | [`Mathlib/InlineConwayRefinement.lean`](Mathlib/InlineConwayRefinement.lean) | [`Mathlib/InlineConwayRefinementProof.lean`](Mathlib/InlineConwayRefinementProof.lean) |
| Surreal numbers from CombinatorialGames | [`CombinatorialGames/ConwayRefinement.lean`](CombinatorialGames/ConwayRefinement.lean) | [`CombinatorialGames/ConwayRefinementProof.lean`](CombinatorialGames/ConwayRefinementProof.lean) |

## Other main results

| Result | Statement | Proof |
|---|---|---|
| Polynomial presentation of $K((\mathbb R^{\le 0}))$ | [`Mathlib/HahnSeriesPolynomialRing.lean`](Mathlib/HahnSeriesPolynomialRing.lean) | [`Mathlib/HahnSeriesPolynomialRingProof.lean`](Mathlib/HahnSeriesPolynomialRingProof.lean) |
| GCDs and primality in $K((\mathbb R^{\le 0}))$ | [`Mathlib/HahnSeriesGCD.lean`](Mathlib/HahnSeriesGCD.lean) | [`Mathlib/HahnSeriesGCDProof.lean`](Mathlib/HahnSeriesGCDProof.lean) |
| Germs over a Cauchy-complete exponent group: polynomial presentation, primality of $J$, refinement | [`Mathlib/CompleteHahnGerm.lean`](Mathlib/CompleteHahnGerm.lean) | [`Mathlib/CompleteHahnGermProof.lean`](Mathlib/CompleteHahnGermProof.lean) |
| Berarducci's germ ring is a polynomial ring and a UFD | [`Mathlib/GermPolynomialRing.lean`](Mathlib/GermPolynomialRing.lean) | [`Mathlib/GermPolynomialRingProof.lean`](Mathlib/GermPolynomialRingProof.lean) |
| Primality and unique irreducible factorisation of omnific integers | [`CombinatorialGames/Examples/OmnificFactorization.lean`](CombinatorialGames/Examples/OmnificFactorization.lean) | [`CombinatorialGames/Examples/OmnificFactorizationProof.lean`](CombinatorialGames/Examples/OmnificFactorizationProof.lean) |
| Roots of every order of $\omega$ in the omnific integers | [`CombinatorialGames/Examples/OmegaRoots.lean`](CombinatorialGames/Examples/OmegaRoots.lean) | [`CombinatorialGames/Examples/OmegaRootsProof.lean`](CombinatorialGames/Examples/OmegaRootsProof.lean) |
| Roots of every order of $t^{-1}$ in $\mathbb Q((\mathbb R^{\le 0}))$ | [`Mathlib/Examples/NegativeMonomialRoots.lean`](Mathlib/Examples/NegativeMonomialRoots.lean) | [`Mathlib/Examples/NegativeMonomialRootsProof.lean`](Mathlib/Examples/NegativeMonomialRootsProof.lean) |

Reader-worthy examples live in the adjacent `Examples/` directories. Proof-only definitions and
lemmas live under `Support/`.

The repository checks the import boundaries with `lake exe standalone-mathlib` and
`lake exe standalone-combinatorial-games`, checks statement–proof pairing with
`lake exe proof-links`, and checks allowed axioms with `lake exe axioms`.
