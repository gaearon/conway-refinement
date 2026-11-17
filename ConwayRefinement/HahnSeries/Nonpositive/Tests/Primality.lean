/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Nonpositive.GCD

/-!
# API checks for primality in the series ring

The degenerate series `0` is primal through dot notation, instance search finds the pre-Schreier
structure on `K((ℝ^{≤0}))` without naming it, and an irreducible series is prime.
-/

public noncomputable section

namespace Tests

open HahnSeries

universe v

variable {K : Type v} [Field K] [CharZero K]

example : IsPrimal (0 : Nonpositive ℝ K) := (0 : Nonpositive ℝ K).isPrimal

example (a : Nonpositive ℝ K) : IsPrimal a := DecompositionMonoid.primal a

example {a : Nonpositive ℝ K} (ha : Irreducible a) : Prime a := Nonpositive.prime_of_irreducible ha

end Tests
