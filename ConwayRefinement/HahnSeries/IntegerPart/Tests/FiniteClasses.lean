/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.IntegerPart.FiniteClasses
public import ConwayRefinement.HahnSeries.IntegerPart.Regrouping

/-!
# Tests for primality through regrouping

Bounded series over an exponent group isomorphic to `ℝ` are all primal, embedding along the
identity preserves primality, and the open Archimedean ball is a convex subgroup.
-/

public noncomputable section

open scoped HahnSeries

namespace Tests

open HahnSeries HahnSeries.CardSuppLTTruncationIntegerPart

/-- Every `ℵ₁`-bounded nonpositive real-exponent series over `ℚ` is primal. -/
theorem isPrimal_cardSuppLTNonpositive_real [Fact (Cardinal.aleph0 < Cardinal.aleph 1)]
    (x : CardSuppLTNonpositive (G := ℝ) (L := ℚ) (κ := Cardinal.aleph 1)) : IsPrimal x :=
  CardSuppLTNonpositive.isPrimal_of_orderIso_real (OrderAddMonoidIso.refl ℝ) x

/-- The open ball at the nonzero Archimedean class of `ℚ` is convex. -/
example (c : FiniteArchimedeanClass ℚ) :
    (FiniteArchimedeanClass.ball ℚ c).toAddSubgroup.IsConvex :=
  inferInstance

/-- Embedding along the identity carries primal elements to primal elements. -/
theorem isPrimal_mapDomain_id {G : Type} {R : Type} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [Field R] {κ : Cardinal.{0}} [Fact (Cardinal.aleph0 < κ)]
    (Z : Subring R) (a : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (ha : IsPrimal a) :
    IsPrimal (mapDomain (AddMonoidHom.id G) Function.injective_id (fun _ _ ↦ Iff.rfl) Z a) :=
  isPrimal_mapDomain_of_isPrimal Z _ _ _ (by simpa using Set.ordConnected_univ) ha

end Tests
