# Standalone statements

These files isolate the main claims from the machinery used to prove them. Each statement file is
paired with a proof file. Mathlib statements import only Mathlib; the concise surreal statement
imports CombinatorialGames.

## Conway's refinement conjecture

All three entry points state the same four-factor conclusion

$$
ab=cd \Longrightarrow
a=ef,\quad b=gh,\quad c=eg,\quad d=fh.
$$

| Formulation | Statement | Proof |
|---|---|---|
| Surreal numbers defined inline from Mathlib | [`Mathlib/InlineConwayRefinement.lean`](Mathlib/InlineConwayRefinement.lean) | [`Mathlib/InlineConwayRefinementProof.lean`](Mathlib/InlineConwayRefinementProof.lean) |
| Generalised power series over saturated exponent groups, using Mathlib | [`Mathlib/HahnIntegerPartRefinement.lean`](Mathlib/HahnIntegerPartRefinement.lean) | [`Mathlib/HahnIntegerPartRefinementProof.lean`](Mathlib/HahnIntegerPartRefinementProof.lean) |
| Surreal numbers from CombinatorialGames | [`CombinatorialGames/ConwayRefinement.lean`](CombinatorialGames/ConwayRefinement.lean) | [`CombinatorialGames/ConwayRefinementProof.lean`](CombinatorialGames/ConwayRefinementProof.lean) |

## Other main results

| Result | Statement | Proof |
|---|---|---|
| Polynomial presentation of $K((\mathbb R^{\le 0}))$ | [`Mathlib/HahnSeriesPolynomialRing.lean`](Mathlib/HahnSeriesPolynomialRing.lean) | [`Mathlib/HahnSeriesPolynomialRingProof.lean`](Mathlib/HahnSeriesPolynomialRingProof.lean) |
| GCDs and primality in $K((\mathbb R^{\le 0}))$ | [`Mathlib/HahnSeriesGCD.lean`](Mathlib/HahnSeriesGCD.lean) | [`Mathlib/HahnSeriesGCDProof.lean`](Mathlib/HahnSeriesGCDProof.lean) |
| Polynomiality and refinement of complete Hahn germs | [`Mathlib/CompleteHahnGerm.lean`](Mathlib/CompleteHahnGerm.lean) | [`Mathlib/CompleteHahnGermProof.lean`](Mathlib/CompleteHahnGermProof.lean) |
| Berarducci's germ ring is a polynomial ring and a UFD | [`Mathlib/GermPolynomialRing.lean`](Mathlib/GermPolynomialRing.lean) | [`Mathlib/GermPolynomialRingProof.lean`](Mathlib/GermPolynomialRingProof.lean) |
| Algebraic independence of minimal homogeneous families in $\widehat{\mathrm P}$ | [`CombinatorialGames/PrincipalRVAlgebraicIndependence.lean`](CombinatorialGames/PrincipalRVAlgebraicIndependence.lean) | [`CombinatorialGames/PrincipalRVAlgebraicIndependenceProof.lean`](CombinatorialGames/PrincipalRVAlgebraicIndependenceProof.lean) |
| Primality and unique irreducible factorisation of omnific integers | [`CombinatorialGames/Examples/OmnificFactorization.lean`](CombinatorialGames/Examples/OmnificFactorization.lean) | [`CombinatorialGames/Examples/OmnificFactorizationProof.lean`](CombinatorialGames/Examples/OmnificFactorizationProof.lean) |

Reader-worthy examples live in the adjacent `Examples/` directories. Proof-only definitions and
lemmas live under `Support/`.

The repository checks the import boundaries with `lake exe standalone-mathlib` and
`lake exe standalone-combinatorial-games`, checks statement–proof pairing with
`lake exe proof-links`, and checks allowed axioms with `lake exe axioms`.
