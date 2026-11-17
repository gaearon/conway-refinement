/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.ConvexSubgroup.Restriction

/-!
# Tests for restriction to a convex subgroup

Restriction to a convex subgroup is a ring endomorphism of the bounded integer part that keeps
the constant coefficient. Restriction to the whole group is the identity, so divisibility from a
convex restriction specializes to an ordinary divisibility.
-/

public noncomputable section

open scoped HahnSeries

namespace Tests

open HahnSeries HahnSeries.CardSuppLTTruncationIntegerPart

variable {G K : Type*} {κ : Cardinal}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field K] [Fact (Cardinal.aleph0 < κ)]

open Classical in
/-- Restriction keeps the constant coefficient, since `0` lies in every subgroup. -/
theorem coeff_zero_restrictToAddSubgroup (Z : Subring K) (C : AddSubgroup G)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z) :
    (restrictToAddSubgroup Z C x : K⟦G⟧).coeff 0 = (x : K⟦G⟧).coeff 0 := by
  rw [coe_restrictToAddSubgroup, HahnSeries.coeff_filter, if_pos C.zero_mem]

/-- Restriction to a convex subgroup is multiplicative. -/
theorem restrictToAddSubgroup_mul (Z : Subring K) {C : AddSubgroup G}
    (hC : (C : Set G).OrdConnected)
    (x y : cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z) :
    restrictToAddSubgroup Z C (x * y) =
      restrictToAddSubgroup Z C x * restrictToAddSubgroup Z C y := by
  simpa only [restrictToAddSubgroupRingHom_apply] using
    map_mul (restrictToAddSubgroupRingHom Z hC) x y

/-- Restriction to the whole group is the identity. -/
theorem restrictToAddSubgroup_top (Z : Subring K)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z) :
    restrictToAddSubgroup Z ⊤ x = x := by
  classical
  apply Subtype.ext; apply Subtype.ext
  ext g
  rw [coe_restrictToAddSubgroup, HahnSeries.coeff_filter, if_pos (AddSubgroup.mem_top g)]

/-- With the whole group, divisibility from a convex restriction is ordinary divisibility. -/
theorem dvd_of_dvd_restrictToAddSubgroup_top (Z : Subring K)
    {q x : cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z}
    (hq0 : q ≠ 0) (h : q ∣ x) : q ∣ x :=
  dvd_of_dvd_restrictToAddSubgroup Z (by simpa using Set.ordConnected_univ)
    (restrictToAddSubgroup_top Z q) hq0
    (by rwa [restrictToAddSubgroup_top])

end Tests
