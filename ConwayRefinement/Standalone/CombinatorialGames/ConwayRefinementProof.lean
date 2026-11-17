/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.Standalone.CombinatorialGames.ConwayRefinement
import ConwayRefinement.Blueprint
import ConwayRefinement.Standalone.CombinatorialGames.Support.ConwayNormalForm
import ConwayRefinement.Surreal.OmnificInteger.Refinement

set_option linter.hashCommand false

/-!
# Proof of Conway's refinement conjecture

The native omnific-integer theorem is transported to Conway's cut definition.
-/

public noncomputable section

universe u

namespace ConwayRefinement.Standalone.Oz.ConwayConjecture

/-- Every equality of products of cut-defined omnific integers has an omnific four-factor
refinement. -/
@[blueprint "thm:conway-refinement"
  (phase := "Surreal numbers and omnific integers")
  (title := "Conway's refinement theorem for omnific integers")
  (statement := /--
    Let $a,b,c,d\in\mathbf{No}$ be omnific integers, that is, satisfy Conway's equation
    $x=\{x-1\mid x+1\}$ [Con76]. If $ab=cd$, then there are omnific integers $e,f,g,h$ such that
    \[
      a=ef,\qquad b=gh,\qquad c=eg,\qquad d=fh.
    \]
    This is Conway's refinement conjecture [Con76, p. 46], listed as [LM24, Conj. 1.1.1(2)].
  -/)
  (proof := /--
    A surreal number satisfies $x=\{x-1\mid x+1\}$ exactly when it lies in the subring
    $\mathbf{Oz}$. By \ref{thm:signed-normal-form-omnific-integer-equivalence}, $\mathbf{Oz}$ is
    isomorphic to $\mathbb Z+\mathbb R((\mathbf{No}^{<0}))_\kappa$, in which every element is primal
    by \ref{thm:surreal-hahn-integer-part-primality}. So $\mathbf{Oz}$ is a pre-Schreier domain, and
    a domain is pre-Schreier exactly when it has the refinement property [LM24, §2.5].
  -/)
  (highlight)]
theorem proof : ConwayRefinement.Standalone.Oz.ConwayConjecture.{u} := by
  rw [ConwayRefinement.Standalone.Oz.conwayConjecture_iff_native]
  exact Surreal.OmnificInteger.conwayRefinement

#print axioms proof

end ConwayRefinement.Standalone.Oz.ConwayConjecture
