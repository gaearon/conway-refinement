/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Nonpositive.PolynomialRing
import ConwayRefinement.HahnSeries.Germ.GermSupport
import Mathlib.Topology.Algebra.Ring.Real

/-!
# API checks for germs at exponents

The monomial `t^γ`, `γ < 0`, separates the germ at an exponent from the germ at zero: its germ at
`γ` is `1`, while its germ at `0` vanishes because its support is bounded away from zero. The
monomial has finite support, so it lies in the subalgebra of series with constant germs.
-/

public noncomputable section

namespace Tests

open HahnSeries HahnSeries.Nonpositive

universe v

variable {K : Type v} [Field K] [CharZero K]

omit [CharZero K] in
/-- The germ of `t^γ` at `γ` is `1`. -/
theorem germAt_single_self {γ : ℝ} (hγ : γ ≤ 0) :
    germAt γ (single γ (1 : K) hγ) = 1 := by
  rw [← mul_one (single γ (1 : K) hγ), germAt_single_mul, sub_self, germAt_zero, map_one]

/-- The germ of `t^γ` at `0` vanishes when `γ < 0`. -/
theorem germAt_zero_single {γ : ℝ} (hγ : γ < 0) :
    germAt 0 (single γ (1 : K) hγ.le) = 0 := by
  by_contra h
  have hmem := (germAt_ne_zero_iff _ 0).mp h
  rw [coe_single, HahnSeries.support_single_of_ne one_ne_zero, closure_singleton] at hmem
  exact hγ.ne (Set.mem_singleton_iff.mp hmem).symm

/-- The monomial `t^γ` has constant germs everywhere. -/
theorem single_mem_seriesWithConstantGerms {γ : ℝ} (hγ : γ ≤ 0) :
    single γ (1 : K) hγ ∈ (seriesTruncationGerms K).seriesWithConstantGerms := by
  rw [mem_seriesWithConstantGerms_iff, Nonpositive.mem_finiteSupportSubring_iff, coe_single]
  exact (Set.finite_singleton γ).subset HahnSeries.support_single_subset

end Tests
