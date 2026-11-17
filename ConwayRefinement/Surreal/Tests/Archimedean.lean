/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.Surreal.Archimedean
import CombinatorialGames.Surreal.Pow
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# API checks for surreal Archimedean balls

This separately compiled client consumes the cardinal and cofinality interface without unfolding
the cut constructions, and checks that the open ball below the class of `1` is nontrivial, so that
the cofinality alternative, not the zero-group alternative, is the one in force.
-/

public noncomputable section

namespace Tests

universe u v

theorem surreal_smallSupportCardinal_uncountable :
    Cardinal.aleph0 < Surreal.smallSupportCardinal.{u} :=
  Surreal.aleph0_lt_smallSupportCardinal

theorem surreal_smallSupportCardinal_regular :
    Surreal.smallSupportCardinal.{u}.IsRegular :=
  Surreal.smallSupportCardinal_isRegular

/-- The Archimedean class of the surreal number `1`. -/
def surrealUnitClass : FiniteArchimedeanClass Surreal :=
  FiniteArchimedeanClass.mk 1 one_ne_zero

theorem surrealUnitClass_eq :
    surrealUnitClass = FiniteArchimedeanClass.mk 1 one_ne_zero := (rfl)

/-- The monomial `ω⁻¹` lies in the open ball below the class of `1`. -/
def surrealPositiveInfinitesimal :
    ↥(FiniteArchimedeanClass.ball ℝ surrealUnitClass) :=
  ⟨ω^ (-1 : Surreal), by
    rw [FiniteArchimedeanClass.mem_ball_iff]
    intro hzero
    rw [surrealUnitClass_eq, FiniteArchimedeanClass.mk_lt_mk one_ne_zero hzero]
    simpa using Surreal.archimedeanClassMk_wpow_strictAnti
      (show (-1 : Surreal) < 0 by norm_num)⟩

theorem surrealPositiveInfinitesimal_pos :
    0 < surrealPositiveInfinitesimal :=
  Surreal.wpow_pos _

/-- The open surreal ball below the class of `1` is nondegenerate. This separates the cofinality
alternative of the ball condition from its zero-group alternative. -/
theorem surrealUnitClass_ball_nontrivial :
    ¬Subsingleton ↥(FiniteArchimedeanClass.ball ℝ surrealUnitClass) := by
  intro h
  exact surrealPositiveInfinitesimal_pos.ne'
    (Subsingleton.elim surrealPositiveInfinitesimal 0)

end Tests
