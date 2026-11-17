/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.Standalone.Mathlib.GermPolynomialRing
public import ConwayRefinement.HahnSeries.Germ.PolynomialRing
public import ConwayRefinement.HahnSeries.NegativeMonomialIdeal
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Proof that the ring of germs is a polynomial ring

The standalone ideal `J`, spanned by the monomials `t^x` with `x < 0`, is the ideal of series whose
support is bounded away from zero. Its quotient is therefore the ring of germs, which is a
polynomial ring over `K` (`HahnSeries.Nonpositive.exists_mvPolynomial_algEquiv_germ`) and hence has
unique factorisation.
-/

public noncomputable section

namespace ConwayRefinement.Standalone.GermPolynomial

universe u

variable {K : Type u} [Field K]

/-- The ideal `J` is the span of the monomials `t^x` with `x < 0`. -/
theorem J_eq : J K = HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  rw [HahnSeries.Nonpositive.negativeMonomialIdeal_def]
  unfold J
  congr 1
  ext m
  constructor
  · rintro ⟨x, hx, hm⟩
    exact HahnSeries.Nonpositive.mem_negativeMonomials_iff.mpr
      ⟨⟨x, hx⟩, Subtype.ext (by rw [HahnSeries.Nonpositive.coe_single]; exact hm.symm)⟩
  · intro h
    obtain ⟨⟨x, hx⟩, rfl⟩ := HahnSeries.Nonpositive.mem_negativeMonomials_iff.mp h
    exact ⟨x, hx, HahnSeries.Nonpositive.coe_single _ _ _⟩

/-- The ideal spanned by the monomials `t^x`, `x < 0`, is the ideal of series whose support is
bounded away from zero. -/
theorem negativeMonomialIdeal_eq_supp [CharZero K] :
    HahnSeries.Nonpositive.negativeMonomialIdeal K =
      (HahnSeries.Nonpositive.boundedAwayIdeal ℝ K) := by
  ext b
  rw [HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero,
    HahnSeries.Nonpositive.mem_boundedAwayIdeal]
  by_cases hb : b = 0
  · subst hb
    exact ⟨fun _ => ⟨-1, by norm_num, by simp⟩, fun _ => by
      rw [HahnSeries.Nonpositive.supportSup_zero]; exact WithBot.bot_lt_coe 0⟩
  rw [HahnSeries.Nonpositive.supportSup_of_ne hb]
  have hne : (b : HahnSeries ℝ K).support.Nonempty :=
    HahnSeries.support_nonempty_iff.mpr (by simpa using hb)
  constructor
  · intro h
    exact ⟨_, by exact_mod_cast h, fun x hx =>
      le_csSup (HahnSeries.Nonpositive.bddAbove_support b) hx⟩
  · rintro ⟨c, hc, hsub⟩
    exact_mod_cast (csSup_le hne hsub).trans_lt hc

variable (K) in
/-- The standalone ring of germs is ring-equivalent to the quotient by the ideal of series whose
support is bounded away from zero. -/
def germRingEquiv [CharZero K] : Germ K ≃+*
    HahnSeries.Nonpositive ℝ K ⧸
      (HahnSeries.Nonpositive.boundedAwayIdeal ℝ K) :=
  Ideal.quotEquivOfEq (J_eq.trans negativeMonomialIdeal_eq_supp)

namespace GermIsPolynomialRing

/-- The germ ring is a polynomial ring over its coefficient field. -/
theorem of_polynomiality (K : Type u) [Field K] : GermIsPolynomialRing K := by
  intro hK
  letI := hK
  obtain ⟨ι, ⟨e⟩⟩ := HahnSeries.Nonpositive.exists_mvPolynomial_algEquiv_germ (G := ℝ) (K := K)
  exact ⟨ι, ⟨e.toRingEquiv.trans (germRingEquiv K).symm⟩⟩

end GermIsPolynomialRing

namespace GermHasUniqueFactorization

/-- Every nonzero germ factors uniquely into irreducibles, up to order and association. -/
theorem of_polynomiality (K : Type u) [Field K] :
    GermHasUniqueFactorization K := by
  intro hK
  letI := hK
  obtain ⟨ι, ⟨equiv⟩⟩ := GermIsPolynomialRing.of_polynomiality K hK
  haveI hdom : IsDomain (Germ K) :=
    Function.Injective.isDomain equiv.symm.toRingHom equiv.symm.injective
  haveI : UniqueFactorizationMonoid (Germ K) :=
    equiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  refine ⟨hdom, fun a ha ↦ ?_, fun f g hf hg h ↦ UniqueFactorizationMonoid.factors_unique hf hg h⟩
  obtain ⟨f, hf, hfa⟩ := UniqueFactorizationMonoid.exists_prime_factors a ha
  exact ⟨f, fun b hb ↦ (hf b hb).irreducible, hfa⟩

end GermHasUniqueFactorization

end ConwayRefinement.Standalone.GermPolynomial
