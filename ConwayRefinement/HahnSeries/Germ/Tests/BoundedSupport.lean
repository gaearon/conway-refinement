/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Germ.BoundedSupport
public import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Tests for germs of series with fewer than `κ` support exponents

The bounded translated truncation at `0` is the identity, the bounded germ ring embeds in the
ring of all germs, and over the Cauchy-complete group `ℝ` every bounded germ is primal.
-/

public noncomputable section

namespace Tests

open HahnSeries HahnSeries.CardSuppLTNonpositive

variable {G : Type} {K : Type} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field K]
variable {κ : Cardinal.{0}} [Fact (Cardinal.aleph0 < κ)]

/-- The bounded translated truncation at `0` is the identity. -/
theorem translatedTruncation_zero (b : CardSuppLTNonpositive (G := G) (L := K) (κ := κ)) :
    translatedTruncation 0 b = b :=
  toNonpositiveAlgHom_injective (by
    rw [toNonpositiveAlgHom_translatedTruncation, Nonpositive.translatedTruncation_zero])

/-- Two bounded series with the same germ in the ring of all germs have the same bounded germ. -/
theorem mk_eq_mk_of_germEmbedding [Nontrivial G]
    {b c : CardSuppLTNonpositive (G := G) (L := K) (κ := κ)}
    (h : Ideal.Quotient.mk (Nonpositive.boundedAwayIdeal G K) (toNonpositiveAlgHom G K κ b) =
      Ideal.Quotient.mk (Nonpositive.boundedAwayIdeal G K) (toNonpositiveAlgHom G K κ c)) :
    Ideal.Quotient.mk (boundedAwayIdeal G K κ) b = Ideal.Quotient.mk _ c :=
  germEmbedding_injective (by rw [germEmbedding_mk, germEmbedding_mk, h])

/-- Every germ of an `ℵ₁`-bounded nonpositive real-exponent series over `ℚ` is primal. -/
theorem isPrimal_germ_real [Fact (Cardinal.aleph0 < Cardinal.aleph 1)]
    (q : CardSuppLTNonpositive (G := ℝ) (L := ℚ) (κ := Cardinal.aleph 1) ⧸
      boundedAwayIdeal ℝ ℚ (Cardinal.aleph 1)) : IsPrimal q :=
  isPrimal_germ q

end Tests
