/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.Surreal.OmnificInteger.Basic

import ConwayRefinement.Algebra.Divisibility.Refinement

/-!
# Conway's four-factor refinement conjecture

This file states the second conjecture on omnific integers from *On Numbers and Games*, page 46,
and LM24, Conjecture 1.1.1(2). There are no nonzero hypotheses: every equality `a * b = c * d`
must have factors `e`, `f`, `g`, and `h` satisfying the four displayed equations.

The four inputs and four witnesses range over `Surreal.OmnificInteger.{u}`.
-/

universe u

public section

/-- The fixed-universe four-factor refinement conjecture for omnific integers. -/
def ConwayRefinementConjecture : Prop :=
  HasFourFactorRefinement Surreal.OmnificInteger.{u}

/-- The four equations in the fixed-universe refinement conjecture. -/
theorem conwayRefinementConjecture_def :
    ConwayRefinementConjecture.{u} ↔
      ∀ a b c d : Surreal.OmnificInteger.{u}, a * b = c * d →
        ∃ e f g h : Surreal.OmnificInteger.{u},
          a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h :=
  hasFourFactorRefinement_def
