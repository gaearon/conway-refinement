/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.Standalone.Mathlib.InlineConwayRefinement
import ConwayRefinement.Standalone.Mathlib.Support.InlineConwayRefinementProof

set_option linter.hashCommand false

public noncomputable section

universe u

namespace ConwayRefinement.Standalone.InlineConwayRefinement.Surreal.ConwayConjecture

/-- Conway's refinement theorem for the fully displayed Mathlib construction of surreal numbers. -/
theorem proof : ConwayConjecture.{u} :=
  ConwayRefinement.Standalone.InlineConwayRefinement.Surreal.conwayRefinementProof

#print axioms proof

end ConwayRefinement.Standalone.InlineConwayRefinement.Surreal.ConwayConjecture
