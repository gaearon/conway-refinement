/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Nonpositive
public import ConwayRefinement.Surreal.HahnSeries.Full
public import ConwayRefinement.Surreal.OmnificInteger.NormalForm

/-!
# Omnific integers in the nonpositive Hahn integer part

This module packages Conway's normal-form characterization into LM24's Hahn-series orientation.
The order dual implements `t = ω⁻¹`, so a nonnegative Conway exponent becomes a nonpositive
Hahn exponent. The coefficient at exponent zero lands in the image of `ℤ → ℝ`.

The resulting map is an injective ring map.
-/

universe u

public noncomputable section

namespace Surreal

/-- The copy of the integers inside the real coefficient field. -/
def realIntegerSubring : Subring ℝ :=
  (Int.castRingHom ℝ).range

/-- The integer coefficient subring of the reals is isomorphic to `ℤ`. -/
noncomputable def realIntegerSubringEquiv : ℤ ≃+* realIntegerSubring :=
  RingEquiv.ofBijective (Int.castRingHom ℝ).rangeRestrict
    ⟨Int.cast_injective, RingHom.rangeRestrict_surjective _⟩

/-- The integer coefficient subring of the reals is pre-Schreier. -/
noncomputable instance instDecompositionMonoidRealIntegerSubring :
    DecompositionMonoid realIntegerSubring :=
  MulEquiv.decompositionMonoid realIntegerSubringEquiv.symm.toMulEquiv

/-- Membership in the real integer coefficient subring. -/
@[simp]
theorem mem_realIntegerSubring {r : ℝ} :
    r ∈ realIntegerSubring ↔ r ∈ Set.range ((↑) : ℤ → ℝ) :=
  Iff.rfl

namespace OmnificInteger

/-- The nonpositive full Hahn series underlying an omnific integer. -/
def toNonpositiveHahn (x : OmnificInteger.{u}) :
    HahnSeries.Nonpositive Surrealᵒᵈ ℝ :=
  ⟨toFullHahnSeries x.1, fun i hi ↦ by
    have hsupport := (isOmnificInteger_iff_normalForm.mp
      (mem_omnificIntegers.mp x.2)).1
    exact hsupport (mem_support_toFullHahnSeries.mp hi)⟩

/-- Coercing the nonpositive Hahn image recovers the full Conway Hahn series. -/
@[simp]
theorem coe_toNonpositiveHahn (x : OmnificInteger.{u}) :
    (x.toNonpositiveHahn : HahnSeries Surrealᵒᵈ ℝ) = toFullHahnSeries x.1 :=
  (rfl)

/-- The Hahn truncation-integer-part element represented by an omnific integer. -/
def toTruncationIntegerPart (x : OmnificInteger.{u}) :
    HahnSeries.truncationIntegerPart Surrealᵒᵈ realIntegerSubring :=
  ⟨x.toNonpositiveHahn, by
    rw [HahnSeries.mem_truncationIntegerPart]
    change (toFullHahnSeries x.1).coeff 0 ∈ realIntegerSubring
    rw [coeff_toFullHahnSeries, mem_realIntegerSubring]
    change x.1.coeff 0 ∈ Set.range ((↑) : ℤ → ℝ)
    exact (isOmnificInteger_iff_normalForm.mp (mem_omnificIntegers.mp x.2)).2⟩

/-- Coercing the truncation-integer-part image recovers the nonpositive Hahn image. -/
@[simp]
theorem coe_toTruncationIntegerPart (x : OmnificInteger.{u}) :
    (x.toTruncationIntegerPart : HahnSeries.Nonpositive Surrealᵒᵈ ℝ) =
      x.toNonpositiveHahn :=
  by
    apply Subtype.ext
    rfl

end OmnificInteger

end Surreal
