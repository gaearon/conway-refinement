/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Truncation

import Mathlib.Data.Rat.Floor

/-!
# API checks for Hahn-series truncations

This client uses only the public Hahn-series interface. Its series has nonzero coefficients exactly
at `-1`, `0`, and `1`, and is truncated at `0`. The support calculations distinguish the strict
truncation `< 0` from the weak truncation `≤ 0`.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries

private def threeTermCoeffs : ℤ →₀ ℚ :=
  Finsupp.single (-1) 1 + Finsupp.single 0 2 + Finsupp.single 1 3

/-- A Hahn series with nonzero coefficients precisely at `-1`, `0`, and `1`. -/
def threeTermTruncationSeries : ℚ⟦ℤ⟧ :=
  HahnSeries.ofFinsupp threeTermCoeffs

@[simp]
theorem threeTermTruncationSeries_support :
    threeTermTruncationSeries.support = {-1, 0, 1} := by
  classical
  ext z
  by_cases hneg : z = -1
  · simp [threeTermTruncationSeries, threeTermCoeffs, hneg]
  by_cases hzero : z = 0
  · simp [threeTermTruncationSeries, threeTermCoeffs, hzero]
  by_cases hone : z = 1
  · simp [threeTermTruncationSeries, threeTermCoeffs, hone]
  · simp [threeTermTruncationSeries, threeTermCoeffs, hneg, hzero, hone]

/-- Strict lower truncation at zero keeps exactly the exponent `-1`. -/
theorem threeTermTruncationSeries_support_truncLT :
    (HahnSeries.truncLT 0 threeTermTruncationSeries).support = {-1} := by
  rw [HahnSeries.support_truncLT, threeTermTruncationSeries_support]
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- Weak lower truncation at zero keeps exactly the exponents `-1` and `0`. -/
theorem threeTermTruncationSeries_support_truncLE :
    (HahnSeries.truncLE 0 threeTermTruncationSeries).support = {-1, 0} := by
  rw [HahnSeries.support_truncLE, threeTermTruncationSeries_support]
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- The weak lower truncation at zero is proper because it discards the term at exponent `1`. -/
theorem threeTermTruncationSeries_truncLE_ne :
    HahnSeries.truncLE 0 threeTermTruncationSeries ≠ threeTermTruncationSeries := by
  intro h
  have hcoeff := congrArg (fun x : ℚ⟦ℤ⟧ => x.coeff 1) h
  simp [threeTermTruncationSeries, threeTermCoeffs] at hcoeff

end Tests
