/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Germ.Basic
public import Mathlib.Data.Real.Basic
import ConwayRefinement.HahnSeries.Germ.PolynomialRing
import Mathlib.Topology.Algebra.Ring.Real

/-!
# API checks for the ideal of series bounded away from zero

The monomial `t^γ`, `γ < 0`, lies in `J`, while the constant `1` does not, so `J` is a proper
nonzero ideal and `1 + t^γ` has the germ of `1`. The ring of germs over real exponents is an
integral domain by instance search.
-/

public noncomputable section

namespace Tests

open HahnSeries HahnSeries.Nonpositive

universe v

variable {K : Type v} [Field K]

/-- The monomial `t^γ`, `γ < 0`, is bounded away from zero. -/
theorem single_mem_boundedAwayIdeal {γ : ℝ} (hγ : γ < 0) :
    single γ (1 : K) hγ.le ∈ boundedAwayIdeal ℝ K := by
  refine (mem_boundedAwayIdeal _).mpr ⟨γ, hγ, ?_⟩
  rw [coe_single]
  exact HahnSeries.support_single_subset.trans
    (Set.singleton_subset_iff.mpr (Set.mem_Iic.mpr le_rfl))

/-- The constant `1` is not bounded away from zero. -/
theorem one_notMem_boundedAwayIdeal' : (1 : Nonpositive ℝ K) ∉ boundedAwayIdeal ℝ K :=
  one_notMem_boundedAwayIdeal

/-- Adding `t^γ`, `γ < 0`, does not change the germ. -/
theorem mk_one_add_single {γ : ℝ} (hγ : γ < 0) :
    Ideal.Quotient.mk (boundedAwayIdeal ℝ K) (1 + single γ (1 : K) hγ.le) =
      Ideal.Quotient.mk (boundedAwayIdeal ℝ K) 1 := by
  have h : Ideal.Quotient.mk (boundedAwayIdeal ℝ K) (single γ (1 : K) hγ.le) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (single_mem_boundedAwayIdeal hγ)
  rw [map_add, h, add_zero]

/-- Nonzero germs over real exponents have nonzero product. -/
theorem mul_ne_zero_germ [CharZero K] {a b : Nonpositive ℝ K ⧸ boundedAwayIdeal ℝ K}
    (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  mul_ne_zero ha hb

end Tests
