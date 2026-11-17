/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import ConwayRefinement.Surreal.HahnSeries.NormalForm

/-!
# Transfer surreal Hahn-series definitions to surreal numbers

This module transfers coefficients, support, length, and truncation along the Conway normal-form
order equivalence. It follows CombinatorialGames PR #263, adapted to the pinned module-safe API.
Arithmetic compatibility is proved in later modules.
-/

universe u

public noncomputable section

namespace Surreal

open Set

/-! ### Coefficients -/

/-- The coefficient of `ω ^ i` in the Conway normal form of a surreal number. -/
def coeff (x : Surreal) : Surreal → ℝ :=
  x.toHahnSeries.coeff

@[simp]
theorem coeff_zero : coeff 0 = 0 := by
  simp [coeff]

@[simp]
theorem coeff_wpow (x : Surreal) : coeff (ω^ x) = Pi.single x 1 := by
  rw [coeff, toHahnSeries_wpow, SurrealHahnSeries.coeff_single]

/-- A real surreal has only its constant Conway coefficient. -/
@[simp]
theorem coeff_realCast (r : ℝ) :
    coeff (r : Surreal.{u}) = Pi.single 0 r := by
  rw [coeff, toHahnSeries_realCast, SurrealHahnSeries.coeff_single]

@[simp]
theorem coeff_toHahnSeries (x : Surreal) : x.toHahnSeries.coeff = x.coeff :=
  (rfl)

@[simp]
theorem _root_.SurrealHahnSeries.coeff_toSurreal (x : SurrealHahnSeries) :
    x.toSurreal.coeff = x.coeff := by
  simp [coeff]

/-! ### Support -/

/-- The support of the Conway normal form of a surreal number. -/
def support (x : Surreal) : Set Surreal :=
  x.toHahnSeries.support

@[simp]
theorem support_coeff (x : Surreal) : x.coeff.support = x.support :=
  (rfl)

@[simp]
theorem support_wpow (x : Surreal) : support (ω^ x) = {x} := by
  aesop (add simp [support])

/-- The Conway support of a real surreal is finite. -/
theorem support_realCast_finite (r : ℝ) :
    (support (r : Surreal.{u})).Finite := by
  rw [← support_coeff, coeff_realCast]
  exact Set.Finite.subset (Set.finite_singleton 0) Pi.support_single_subset

@[simp]
theorem support_toHahnSeries (x : Surreal) : x.toHahnSeries.support = x.support :=
  (rfl)

@[simp]
theorem _root_.SurrealHahnSeries.support_toSurreal (x : SurrealHahnSeries) :
    x.toSurreal.support = x.support := by
  simp [support]

theorem wellFoundedOn_support (x : Surreal) : x.support.WellFoundedOn (fun a b ↦ a > b) :=
  x.toHahnSeries.wellFoundedOn_support

instance (x : Surreal.{u}) : Small.{u} x.support :=
  inferInstanceAs (Small (SurrealHahnSeries.support _))

/-! ### Length -/

/-- The ordinal length of the Conway normal form of a surreal number. -/
def length (x : Surreal) : Ordinal :=
  x.toHahnSeries.length

@[simp, grind =]
theorem mem_support_iff {x i : Surreal} : i ∈ x.support ↔ x.coeff i ≠ 0 :=
  (Iff.rfl)

theorem notMem_support_iff {x i : Surreal} : i ∉ x.support ↔ x.coeff i = 0 :=
  mem_support_iff.not_left

@[simp]
theorem length_toHahnSeries (x : Surreal) : x.toHahnSeries.length = x.length :=
  (rfl)

theorem PartialSum.length_top (x : Surreal) : (⊤ : PartialSum x).length = x.length := by
  rw [PartialSum.length_eq_carrier_length, PartialSum.carrier_top, length_toHahnSeries]

@[simp]
theorem _root_.SurrealHahnSeries.length_toSurreal (x : SurrealHahnSeries) :
    x.toSurreal.length = x.length := by
  simp [length]

/-! ### Truncation -/

/-- Remove the terms of the Conway normal form whose exponents are at most `i`. -/
def trunc (x i : Surreal) : Surreal :=
  x.toHahnSeries.trunc i

@[simp]
theorem toHahnSeries_trunc (x i : Surreal) :
    (x.trunc i).toHahnSeries = x.toHahnSeries.trunc i := by
  simp [trunc]

@[simp]
theorem _root_.SurrealHahnSeries.toSurreal_trunc (x : SurrealHahnSeries) (i : Surreal) :
    x.trunc i = x.toSurreal.trunc i := by
  simp [trunc]

@[aesop simp]
theorem coeff_trunc (x i : Surreal) :
    (x.trunc i).coeff = fun j ↦ if i < j then x.coeff j else 0 := by
  unfold coeff
  aesop

@[simp, grind =]
theorem support_trunc (x i : Surreal) : (x.trunc i).support = x.support ∩ Ioi i := by
  aesop

theorem trunc_eq_self_iff {x i : Surreal} : x.trunc i = x ↔ ∀ j ∈ x.support, i < j := by
  nth_rw 2 [← toSurreal_toHahnSeries x]
  rw [trunc, SurrealHahnSeries.toSurreal_inj]
  exact SurrealHahnSeries.trunc_eq_self_iff

alias ⟨_, trunc_eq_self⟩ := trunc_eq_self_iff

theorem trunc_eq_trunc {x i j : Surreal} (h : i ≤ j)
    (H : ∀ k, i < k → k ≤ j → x.coeff k = 0) : x.trunc i = x.trunc j := by
  simpa [← toHahnSeries_trunc] using x.toHahnSeries.trunc_eq_trunc h H

end Surreal
