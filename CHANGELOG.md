# Changelog

## 2.0

- The proof now goes through germs of translated truncations: a transcendence lemma presents
  Berarducci's ring of germs $K((G^{\le 0}))/J$ as a polynomial ring over $K$ for every
  Cauchy-complete exponent group, and the same recursion presents $K((\mathbb R^{\le 0}))$ as a
  polynomial ring over its finite-support subring, which makes it a GCD domain. The reduction from
  $Z+R((G^{<0}))_\kappa$ runs along Archimedean classes through a single $D+M$ step. This replaces
  the route through associated graded rings.
- Removed, and still available at tag [`v1.0`](https://github.com/gaearon/conway-refinement/tree/v1.0):
  algebraic independence of the minimal homogeneous generators of the principal RV algebra (a
  strictly stronger graded statement than the polynomial presentation of the ring of germs); the
  degree-two, one-row, and random-series prime examples; the corollaries for saturated exponent
  groups.
- The standalone statements of Conway's refinement conjecture (`Challenge.lean`,
  `ConwayRefinement/Standalone/CombinatorialGames/ConwayRefinement.lean`,
  `ConwayRefinement/Standalone/Mathlib/InlineConwayRefinement.lean`) are unchanged.
- Size: about 144,000 → about 31,000 lines of Lean; 13,337 → 3,854 declarations (as counted by
  `lake exe axioms`).

## 1.0

- First public proof of Conway's refinement conjecture for omnific integers.
