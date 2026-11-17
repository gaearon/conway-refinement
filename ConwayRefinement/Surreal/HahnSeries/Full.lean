/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import all CombinatorialGames.Surreal.HahnSeries.Basic
public import ConwayRefinement.Surreal.HahnSeries.Transfer
import ConwayRefinement.Surreal.HahnSeries.NormalFormAdd
import ConwayRefinement.Surreal.HahnSeries.NormalFormMul

/-!
# Conway normal forms as Hahn series

Every surreal number is the sum of its Conway normal form. Recording the normal form as a Hahn
series in `t = ω⁻¹` with dual exponents gives the full Hahn-series embedding of the surreal numbers;
negating exponents puts it in a Hahn field whose exponent group is `Surreal` itself.
-/

section


/-!
# Conway normal forms in the full Hahn field

The Conway coefficients of a surreal number determine a Hahn series in
`ℝ⟦Surrealᵒᵈ⟧`. The order dual implements LM24's change from Conway's monomial `ω` to
`t = ω⁻¹`: nonnegative Conway exponents become nonpositive Hahn exponents.

This map preserves the full ring structure.
-/

universe u

public noncomputable section

namespace Surreal

/-- The full Hahn series with the Conway coefficients of a surreal number. -/
def toFullHahnSeries (x : Surreal.{u}) : HahnSeries Surrealᵒᵈ ℝ where
  coeff i := x.coeff i.ofDual
  isPWO_support' := by
    rw [Set.isPWO_iff_isWF]
    apply Set.WellFoundedOn.mapsTo (fun i : Surrealᵒᵈ ↦ i.ofDual) _
      x.wellFoundedOn_support
    intro i hi
    rw [mem_support_iff]
    exact hi

/-- Evaluation of the full Conway Hahn series. -/
@[simp]
theorem coeff_toFullHahnSeries (x : Surreal.{u}) (i : Surrealᵒᵈ) :
    x.toFullHahnSeries.coeff i = x.coeff i.ofDual :=
  (rfl)

/-- The support of the full Conway Hahn series is the order dual of the Conway support. -/
theorem mem_support_toFullHahnSeries {x : Surreal.{u}} {i : Surrealᵒᵈ} :
    i ∈ x.toFullHahnSeries.support ↔ i.ofDual ∈ x.support := by
  rw [HahnSeries.mem_support x.toFullHahnSeries i, coeff_toFullHahnSeries,
    mem_support_iff]

/-- The full Conway Hahn-series map sends zero to zero. -/
@[simp]
theorem toFullHahnSeries_zero : (0 : Surreal.{u}).toFullHahnSeries = 0 := by
  ext i
  rw [coeff_toFullHahnSeries, HahnSeries.coeff_zero]
  exact congrFun coeff_zero i.ofDual

/-- The full Conway Hahn-series map preserves addition. -/
@[simp]
theorem toFullHahnSeries_add (x y : Surreal.{u}) :
    (x + y).toFullHahnSeries = x.toFullHahnSeries + y.toFullHahnSeries := by
  ext i
  rw [coeff_toFullHahnSeries, HahnSeries.coeff_add, coeff_toFullHahnSeries,
    coeff_toFullHahnSeries]
  exact congrFun (coeff_add x y) i.ofDual

/-- The additive full Conway Hahn-series map is injective. -/
theorem toFullHahnSeries_injective :
    Function.Injective (toFullHahnSeries : Surreal.{u} → HahnSeries Surrealᵒᵈ ℝ) := by
  intro x y hxy
  rw [← toHahnSeries_inj]
  apply SurrealHahnSeries.ext
  funext i
  have hcoeff := congrArg (fun q : HahnSeries Surrealᵒᵈ ℝ ↦
    q.coeff (OrderDual.toDual i)) hxy
  simpa only [coeff_toFullHahnSeries, OrderDual.ofDual_toDual,
    coeff_toHahnSeries] using hcoeff

private theorem toFullHahnSeries_eq_ofLex_toHahnSeries (x : Surreal.{u}) :
    x.toFullHahnSeries = ofLex x.toHahnSeries.1 := by
  ext i
  rw [coeff_toFullHahnSeries, ← coeff_toHahnSeries]
  rfl

private theorem ofLex_coe_mul (x y : SurrealHahnSeries.{u}) :
    ofLex (x * y).1 = ofLex x.1 * ofLex y.1 := by
  with_unfolding_all rfl

/-- The full Conway Hahn-series map preserves arbitrary surreal products. -/
@[simp]
theorem toFullHahnSeries_mul (x y : Surreal.{u}) :
    (x * y).toFullHahnSeries = x.toFullHahnSeries * y.toFullHahnSeries := by
  calc
    (x * y).toFullHahnSeries = ofLex (x * y).toHahnSeries.1 :=
      toFullHahnSeries_eq_ofLex_toHahnSeries (x * y)
    _ = ofLex (x.toHahnSeries * y.toHahnSeries).1 := by
      rw [toHahnSeries_mul]
    _ = ofLex x.toHahnSeries.1 * ofLex y.toHahnSeries.1 :=
      ofLex_coe_mul x.toHahnSeries y.toHahnSeries
    _ = x.toFullHahnSeries * y.toFullHahnSeries := by
      rw [← toFullHahnSeries_eq_ofLex_toHahnSeries,
        ← toFullHahnSeries_eq_ofLex_toHahnSeries]

/-- The full Conway Hahn series of a real is concentrated at exponent zero. -/
@[simp]
theorem toFullHahnSeries_realCast (r : ℝ) :
    toFullHahnSeries (r : Surreal.{u}) = HahnSeries.single 0 r := by
  ext i
  rw [coeff_toFullHahnSeries, HahnSeries.coeff_single]
  have hcoeff : (r : Surreal.{u}).coeff = Pi.single 0 r := by
    rw [← coeff_toHahnSeries, toHahnSeries_realCast,
      SurrealHahnSeries.coeff_single]
  rw [hcoeff]
  by_cases hi : i = 0
  · subst i
    simp
  · have hi' : i.ofDual ≠ 0 := by
      exact fun h ↦ hi (by simpa using congrArg OrderDual.toDual h)
    simp [hi, hi']

/-- The full Conway Hahn series of `ω ^ x` is its corresponding monomial. -/
@[simp]
theorem toFullHahnSeries_wpow (x : Surreal.{u}) :
    toFullHahnSeries (ω^ x) = HahnSeries.single (OrderDual.toDual x) 1 := by
  ext i
  rw [coeff_toFullHahnSeries, coeff_wpow, HahnSeries.coeff_single]
  by_cases hi : i = OrderDual.toDual x
  · subst i
    simp
  · have hi' : i.ofDual ≠ x := by
      exact fun h ↦ hi (by simpa using congrArg OrderDual.toDual h)
    simp [hi, hi']

end Surreal

end
end

/-!
## Conway normal forms with signed surreal exponents

The order dual in `Surreal.toFullHahnSeries` records the reversal from Conway's `ω` to
LM24's `t = ω⁻¹`. Sending a dual exponent `i` to the ordinary surreal exponent `-i` makes
that reversal explicit and places the normal form in a Hahn field whose exponent group is
`Surreal` itself. This is the orientation in which the surreal Archimedean-stratum assumptions
apply directly.
-/

section

universe u

public noncomputable section

namespace Surreal

/-- Negation identifies dual Conway exponents with signed ordinary surreal exponents. -/
def dualExponentOrderAddMonoidIso : Surrealᵒᵈ ≃+o Surreal :=
  { toFun := fun x ↦ -x.ofDual
    invFun := fun x ↦ OrderDual.toDual (-x)
    left_inv := by intro x; simp
    right_inv := by intro x; simp
    map_add' := by intro x y; simp [add_comm]
    map_le_map_iff' := by
      intro x y
      change -x.ofDual ≤ -y.ofDual ↔ y.ofDual ≤ x.ofDual
      exact neg_le_neg_iff }

end Surreal

end
end
