/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import ConwayRefinement.Algebra.Divisibility.PrimalPreimage
import ConwayRefinement.HahnSeries.Germ.GermAt
import ConwayRefinement.HahnSeries.Tests.FiniteSupportGCD
import ConwayRefinement.Surreal.HahnSeries.Tests.CardinalIntegerPart
import ConwayRefinement.HahnSeries.FiniteSupportGCDProof
import ConwayRefinement.HahnSeries.FiniteSupportUnit
import ConwayRefinement.Surreal.OmnificInteger.RefinementConjecture
import ConwayRefinement.Surreal.ArchimedeanAssumptions
import Mathlib.Data.List.Chain
import Mathlib.RingTheory.HahnSeries.Addition
import ConwayRefinement.HahnSeries.Truncation
import CombinatorialGames.NatOrdinal.Pow
import Mathlib.SetTheory.Ordinal.Exponential
import ConwayRefinement.SetTheory.Ordinal.SetOrderType
import ConwayRefinement.Order.Archimedean
import Mathlib.RingTheory.HahnSeries.Multiplication
import ConwayRefinement.Surreal.HahnSeries.Full
import CombinatorialGames.Surreal.HahnSeries.Basic
import ConwayRefinement.Surreal.OmnificInteger.NormalForm

/-!
# Compiled signatures of the source results

Exact type ascriptions for the published results used in the proof and for the structures on which
they rest. A change in hypotheses, quantifier order, endpoints, or ordinal operations fails
elaboration here. Semantic boundary examples distinguish the intended definitions from nearby
incorrect ones.

The refinement theorem has two isolated statements. `ConwayRefinement/Standalone/Mathlib/` fixes
its Hahn-series form against Mathlib alone, while
`ConwayRefinement/Standalone/CombinatorialGames/` fixes its concrete omnific-integer form against
Mathlib and CombinatorialGames alone.

The hash-command linter is disabled because checked signatures are this module's purpose.
-/

set_option linter.hashCommand false

universe u v

open scoped HahnSeries

public section

section ExactSignatures

/- LM24, Fact 2.5.2: units and pairwise gcds in the nonpositive finite-support ring. -/
#check (@HahnSeries.Nonpositive.isUnit_finiteSupport_iff_exists_scalar :
  ∀ {G : Type u} {K : Type v} [LinearOrder G] [AddCommGroup G]
    [IsOrderedAddMonoid G] [Field K]
    (p : (HahnSeries.Nonpositive.finiteSupportSubring :
      Subring (HahnSeries.Nonpositive G K))),
      IsUnit p ↔
        ∃ k : K, k ≠ 0 ∧
          p = HahnSeries.Nonpositive.finiteSupportScalarHom (G := G) k)

#check (@HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists :
  ∀ {G : Type u} {K : Type v} [LinearOrder G] [AddCommGroup G]
    [IsOrderedAddMonoid G] [Field K]
    (p q : (HahnSeries.Nonpositive.finiteSupportSubring :
      Subring (HahnSeries.Nonpositive G K))),
      ∃ d : (HahnSeries.Nonpositive.finiteSupportSubring :
        Subring (HahnSeries.Nonpositive G K)),
        ∀ e : (HahnSeries.Nonpositive.finiteSupportSubring :
          Subring (HahnSeries.Nonpositive G K)),
          e ∣ p ∧ e ∣ q ↔ e ∣ d)

/- The same underlying `t⁻¹` distinguishes the nonpositive ring from the full group ring. -/
#check (Tests.nonpositiveNegativeMonomial_not_isUnit :
  ¬ IsUnit Tests.nonpositiveNegativeMonomial)

#check (Tests.fullNegativeMonomial_isUnit :
  IsUnit Tests.fullNegativeMonomial)

/- The zero-boundary gcd certificate retains both association and the defining orientation. -/
#check (Tests.finiteSupportGCD_zero_left :
  ∃ d : Tests.IntegerNonpositiveFiniteSupportRing,
    (d ∣ Tests.nonpositiveNegativeMonomial ∧
        Tests.nonpositiveNegativeMonomial ∣ d) ∧
      ∀ e : Tests.IntegerNonpositiveFiniteSupportRing,
        e ∣ 0 ∧ e ∣ Tests.nonpositiveNegativeMonomial ↔ e ∣ d)

/- Berarducci 2000, Definition 6.1: the germ of `b` at `γ` is the class of the translated
truncation `b^{|γ} = t^{-γ} b_{|γ}` modulo the ideal `J` of series whose support is bounded away
from zero. -/
#check (@HahnSeries.Nonpositive.mem_boundedAwayIdeal :
  ∀ {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Nontrivial G] [CommRing R] (b : HahnSeries.Nonpositive G R),
      b ∈ HahnSeries.Nonpositive.boundedAwayIdeal G R ↔
        ∃ c < (0 : G), (b : HahnSeries G R).support ⊆ Set.Iic c)

#check (@HahnSeries.Nonpositive.germAt_apply :
  ∀ {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field K]
    [Nontrivial G] (γ : G) (b : HahnSeries.Nonpositive G K),
      HahnSeries.Nonpositive.germAt γ b =
        Ideal.Quotient.mk (HahnSeries.Nonpositive.boundedAwayIdeal G K)
          (HahnSeries.Nonpositive.translatedTruncation γ b))

#check (@HahnSeries.Nonpositive.coe_translatedTruncation :
  ∀ {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field K]
    (γ : G) (b : HahnSeries.Nonpositive G K),
      (HahnSeries.Nonpositive.translatedTruncation γ b : HahnSeries G K) =
        HahnSeries.translate (-γ) (HahnSeries.truncLE γ (b : HahnSeries G K)))

/- Berarducci 2000, Lemma 7.5: the convolution formula for the germs of a product. -/
#check (@HahnSeries.Nonpositive.germAt_mul :
  ∀ {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field K]
    [Nontrivial G] [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [CompleteSpace G]
    (b c : HahnSeries.Nonpositive G K) (γ : G),
      HahnSeries.Nonpositive.germAt γ (b * c) =
        ∑ᶠ β, HahnSeries.Nonpositive.germAt β b * HahnSeries.Nonpositive.germAt (γ - β) c)

#check (@conwayRefinementConjecture_def :
  ConwayRefinementConjecture.{u} ↔
    ∀ a b c d : Surreal.OmnificInteger.{u}, a * b = c * d →
      ∃ e f g h : Surreal.OmnificInteger.{u},
        a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h)

/- *On Numbers and Games*, Theorem 31, as recalled in LM24, Section 1.1. -/
#check (@Surreal.isOmnificInteger_iff_normalForm :
  ∀ {x : Surreal.{u}},
    Surreal.IsOmnificInteger x ↔
      x.support ⊆ Set.Ici 0 ∧
        x.coeff 0 ∈ Set.range ((↑) : ℤ → ℝ))

/- LM24, Proposition 2.4.3: every nonzero surreal Archimedean stratum is order-additively
isomorphic to the reals. -/
#check (@Surreal.stratumOrderAddMonoidIsoReal :
  ∀ (s : HahnEmbedding.ArchimedeanStrata ℝ Surreal.{u})
    (c : FiniteArchimedeanClass Surreal.{u}), s.stratum c ≃+o ℝ)

/- Universe-bounded LM24, Proposition 2.4.4: every nonzero surreal Archimedean ball has
cofinality at least the cardinal bounding small Conway normal forms. -/
#check (@Surreal.smallSupportCardinal_le_ball_cof :
  ∀ (c : FiniteArchimedeanClass Surreal.{u}),
    Surreal.smallSupportCardinal.{u} ≤
      Order.cof ↥(FiniteArchimedeanClass.ball ℝ c))

end ExactSignatures
