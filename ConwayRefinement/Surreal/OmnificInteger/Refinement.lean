/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.Surreal.HahnSeries.IntegerPart

import ConwayRefinement.Blueprint
import ConwayRefinement.Algebra.Divisibility.Refinement
import ConwayRefinement.HahnSeries.IntegerPart.Primality
import ConwayRefinement.Surreal.CommonTail

/-!
# Conway's refinement conjecture for omnific integers

Conway conjectured (*On Numbers and Games*, page 46; LM24, Conjecture 1.1.1(2)) that every equality
`a * b = c * d` of omnific integers refines as `a = e * f`, `b = g * h`, `c = e * g`, `d = f * h`.
Conway's normal form identifies the omnific integers with a bounded Hahn integer part, which is
pre-Schreier by the primality theorem for bounded Hahn integer parts. Hence the conjecture holds,
every irreducible omnific integer is prime, and factorisations into irreducibles are unique.
-/

/-!
## Conway's four-factor refinement conjecture

This file states the second conjecture on omnific integers from *On Numbers and Games*, page 46,
and LM24, Conjecture 1.1.1(2). There are no nonzero hypotheses: every equality `a * b = c * d`
must have factors `e`, `f`, `g`, and `h` satisfying the four displayed equations.

The four inputs and four witnesses range over `Surreal.OmnificInteger.{u}`.
-/

section

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

end
end

/-!
## Conway's refinement conjecture for omnific integers

The signed Conway normal form identifies the omnific integers with the cardinal-bounded
generalised-power-series integer part over the integer subring of the reals. Finite support-class
primality and the common-tail theorem prove that this integer part is pre-Schreier. Transporting
through signed normal form gives Conway's four-factor refinement theorem. Consequently every
irreducible omnific integer is prime, and factorisations into irreducibles are unique.
-/

section

open Cardinal FiniteArchimedeanClass
open HahnSeries.CardSuppLTTruncationIntegerPart

universe u

public noncomputable section

namespace Surreal.OmnificInteger

private theorem small_of_card_lt_smallSupportCardinal
    {S : Set (FiniteArchimedeanClass Surreal.{u})}
    (hS : #S < Surreal.smallSupportCardinal.{u}) : Small.{u} S := by
  rw [Cardinal.small_iff_lift_mk_lt_univ, Cardinal.lift_id]
  rw [Surreal.smallSupportCardinal_eq_univ] at hS
  exact hS

/-- Every element of the signed bounded Hahn integer part corresponding to the omnific integers
is primal. -/
@[blueprint "thm:surreal-hahn-integer-part-primality"
  (phase := "Surreal numbers and omnific integers")
  (title := "Primality in $\\mathbb Z+\\mathbb R((\\mathbf{No}^{<0}))_\\kappa$")
  (statement := /--
    Let $\mathbf{No}$ be the surreal numbers of a universe $u$ and $\kappa_u$
    the cardinal of that universe.  Every element of
    $\mathbb Z+\mathbb R((\mathbf{No}^{<0}))_{\kappa_u}$ is primal.
  -/)
  (proof := /--
    Apply \ref{thm:hahn-integer-part-primality} with $K=R=\mathbb R$,
    $Z=\mathbb Z$, which is pre-Schreier, and $\kappa=\kappa_u$, an uncountable
    regular cardinal.  Condition (1) is \ref{fact:surreal-archimedean-strata};
    condition (2) holds by \ref{fact:surreal-archimedean-ball-cofinality};
    condition (3) by \ref{lem:surreal-common-tail-cofinality}, since a set of
    classes of cardinality less than $\kappa_u$ is a set of the universe; and
    condition (4) by \ref{lem:surreal-common-tail-quotient-complete}.
  -/)]
theorem signedSmallSupportIntegerPart_isPrimal
    (a : SignedSmallSupportIntegerPart.{u}) : IsPrimal a := by
  refine isPrimal Surreal.realIntegerSubring Surreal.archimedeanStrata
    (fun c ↦ ⟨Surreal.stratumOrderAddMonoidIsoReal Surreal.archimedeanStrata c⟩)
    (fun c ↦ Or.inl (Surreal.smallSupportCardinal_le_ball_cof c))
    (fun T _ hTlimit hTcard ↦ ?_) (fun T hTne hTlimit hTcard ↦ ?_) a
  · letI : Small.{u} T := small_of_card_lt_smallSupportCardinal hTcard
    exact Or.inl (Surreal.smallSupportCardinal_le_tailSubmodule_cof T hTlimit)
  · letI : Small.{u} T := small_of_card_lt_smallSupportCardinal hTcard
    letI : Nonempty T := Set.nonempty_coe_sort.mpr hTne
    exact Surreal.completeSpace_rationalTailQuotient T hTlimit

/-- The signed bounded Hahn integer part corresponding to the omnific integers is pre-Schreier. -/
theorem signedSmallSupportIntegerPart_decompositionMonoid :
    DecompositionMonoid SignedSmallSupportIntegerPart.{u} :=
  ⟨signedSmallSupportIntegerPart_isPrimal⟩

/-- The omnific-integer subring has the four-factor refinement property. -/
theorem conwayRefinement : ConwayRefinementConjecture.{u} := by
  rw [conwayRefinementConjecture_def, ← hasFourFactorRefinement_def]
  letI : DecompositionMonoid SignedSmallSupportIntegerPart.{u} :=
    signedSmallSupportIntegerPart_decompositionMonoid
  exact signedSmallSupportIntegerPartRingEquiv.toMulEquiv.hasFourFactorRefinement_iff.mpr
    hasFourFactorRefinement_of_decompositionMonoid

/-- Every omnific integer is primal. -/
theorem isPrimal (x : Surreal.OmnificInteger.{u}) : IsPrimal x :=
  (RingEquiv.isPrimal_iff signedSmallSupportIntegerPartRingEquiv x).mp
    (signedSmallSupportIntegerPart_isPrimal _)

/-- Every irreducible omnific integer is prime. -/
@[blueprint "thm:omnific-factorisation"
  (phase := "Surreal numbers and omnific integers")
  (title := "Irreducible omnific integers are prime")
  (statement := /--
    Let $\mathbf{Oz}$ be the omnific integers of a fixed universe.  Every
    irreducible element of $\mathbf{Oz}$ is prime in $\mathbf{Oz}$.
  -/)
  (proof := /--
    By \ref{thm:signed-normal-form-omnific-integer-equivalence} and
    \ref{thm:surreal-hahn-integer-part-primality}, every element of
    $\mathbf{Oz}$ is primal.  An irreducible primal element is prime.
  -/)]
theorem prime_of_irreducible {x : Surreal.OmnificInteger.{u}} (hirr : Irreducible x) :
    Prime x :=
  hirr.prime_of_isPrimal (isPrimal x)

/-- Unique factorisation in the omnific integers: two factorisations of an omnific integer into
irreducibles agree up to order and units. -/
theorem factorization_unique {f g : Multiset Surreal.OmnificInteger.{u}}
    (hf : ∀ x ∈ f, Irreducible x) (hg : ∀ x ∈ g, Irreducible x)
    (hfg : Associated f.prod g.prod) :
    Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx ↦ prime_of_irreducible (hf x hx))
    (fun x hx ↦ prime_of_irreducible (hg x hx)) hfg

end Surreal.OmnificInteger

end
end
