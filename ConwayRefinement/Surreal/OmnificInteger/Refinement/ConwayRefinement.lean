/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.IntegerPart.LimitTailPrimality
public import ConwayRefinement.Algebra.Divisibility.Refinement
public import ConwayRefinement.Surreal.HahnSeries.CardinalIntegerPart
public import ConwayRefinement.Surreal.OmnificInteger.RefinementConjecture
public import ConwayRefinement.Surreal.RationalTailQuotient
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

import ConwayRefinement.Algebra.Divisibility.PrimalPreimage
import ConwayRefinement.Blueprint

/-!
# Conway's refinement conjecture for omnific integers

The signed Conway normal form identifies the omnific integers with the cardinal-bounded
generalised-power-series integer part over the integer subring of the reals. Finite support-class
primality and the common-tail theorem prove that this integer part is pre-Schreier. Transporting
through signed normal form gives Conway's four-factor refinement theorem. Consequently every
irreducible omnific integer is prime, and factorisations into irreducibles are unique.
-/

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
  (title := "Primality of the surreal Hahn integer part")
  (statement := /--
    Every element of
    \[
      \mathbb Z+\mathbb R((\mathbf{No}_u^{<0}))_{\kappa_u}
    \]
    is primal, where $\kappa_u$ is the universe cardinal.
  -/)
  (proof := /--
    The two Archimedean hypotheses follow from
    \ref{fact:surreal-archimedean-strata} and
    \ref{fact:surreal-archimedean-ball-cofinality}. Therefore
    \ref{thm:finite-support-classes-primality} handles series whose support
    meets finitely many Archimedean classes. For a small limit family, the
    quotient by its common tail is Cauchy complete by
    \ref{lem:surreal-common-tail-quotient-complete}.  The common tail has
    the required fraction-field property by
    \ref{thm:surreal-common-tail-integer-part-fraction-field}. Finally,
    \ref{thm:limit-tail-primality} proves primality for arbitrary support-class
    order type.
  -/)]
theorem signedSmallSupportIntegerPart_isPrimal
    (a : SignedSmallSupportIntegerPart.{u}) : IsPrimal a := by
  apply isPrimal_of_finite_classes_and_limit_tail_conditions Surreal.realIntegerSubring
  · exact isPrimal_of_supportArchimedeanClasses_finite
      Surreal.realIntegerSubring Surreal.archimedeanStrata
      (fun c ↦ ⟨Surreal.stratumOrderAddMonoidIsoReal Surreal.archimedeanStrata c⟩)
      (Surreal.assumptionA2AtFiniteClass Surreal.realIntegerSubring)
  · intro T hTne hTlimit hTcard
    letI : Small.{u} T := small_of_card_lt_smallSupportCardinal hTcard
    letI : Nonempty T := Set.nonempty_coe_sort.mpr hTne
    exact ⟨Surreal.completeSpace_rationalTailQuotient T hTlimit⟩
  · intro T _hTne hTlimit hTcard
    letI : Small.{u} T := small_of_card_lt_smallSupportCardinal hTcard
    exact Surreal.fracSubring_cardSuppLTTruncationIntegerPart_tailSubmodule_eq_top
      Surreal.realIntegerSubring T hTlimit

/-- The signed bounded Hahn integer part corresponding to the omnific integers is pre-Schreier. -/
theorem signedSmallSupportIntegerPart_decompositionMonoid :
    DecompositionMonoid SignedSmallSupportIntegerPart.{u} :=
  ⟨signedSmallSupportIntegerPart_isPrimal⟩

/-- The omnific-integer subring has the four-factor refinement property. -/
@[blueprint "thm:omnific-integer-refinement-property"
  (phase := "Surreal numbers and omnific integers")
  (title := "Refinement property of $\\mathbf{Oz}_u$")
  (statement := /--
    If $a,b,c,d\in\mathbf{Oz}$ and $ab=cd$, then there are
    $e,f,g,h\in\mathbf{Oz}$ such that
    \[
      a=ef,\qquad b=gh,\qquad c=eg,\qquad d=fh.
    \]
  -/)
  (proof := /--
    By \ref{thm:signed-normal-form-omnific-integer-equivalence},
    $\mathbf{Oz}_u$ is isomorphic to its bounded generalised-power-series
    integer part.
    By \ref{thm:surreal-hahn-integer-part-primality}, that integer part is
    pre-Schreier and therefore has four-factor refinement.  Transport the
    refinement back through signed normal form.
  -/)]
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
    Every irreducible element of $\mathbf{Oz}$ is prime in $\mathbf{Oz}$.
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
