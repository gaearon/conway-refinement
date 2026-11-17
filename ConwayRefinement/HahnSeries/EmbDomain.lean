/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.HahnSeries.Cardinal

/-!
# Exponent embeddings of Hahn series

An order embedding of exponent groups embeds the Hahn series on the smaller group into those on the
larger one (Mathlib's `HahnSeries.embDomain`). This file gives the exact support formula for
injective embeddings and, for an ordered additive equivalence, the induced ring equivalence of
Hahn-series rings.
-/

/-!
## Exponent-domain embeddings of Hahn series

Mathlib's exponent-domain embedding has a one-sided support inclusion. Injectivity of the order
embedding gives the exact support formula needed by the translation and nonpositive-series APIs.
-/

section

universe u v w

public section

namespace HahnSeries

variable {G : Type u} {H : Type v} {K : Type w}
  [PartialOrder G] [PartialOrder H] [Zero K]

/-- Extending the exponent domain maps the support exactly onto its image. -/
@[simp]
theorem support_embDomain (f : G ↪o H) (x : K⟦G⟧) :
    (embDomain f x).support = f '' x.support := by
  apply Set.Subset.antisymm support_embDomain_subset
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_support] at hg ⊢
  intro hzero
  exact hg (embDomain_coeff.symm.trans hzero)

/-- Restrict a Hahn series along an ordered embedding by retaining the coefficients in its
range. This is a left inverse to `embDomain`; it is also a right inverse when the original
series is supported in the embedding's range. -/
noncomputable def restrictDomain (f : G ↪o H) (x : K⟦H⟧) : K⟦G⟧ where
  coeff g := x.coeff (f g)
  isPWO_support' := by
    rw [Set.isPWO_iff_exists_monotone_subseq]
    intro a ha
    have hfa : ∀ n, f (a n) ∈ x.support := fun n ↦ ha n
    obtain ⟨g, hg⟩ := x.isPWO_support.exists_monotone_subseq hfa
    exact ⟨g, fun _ _ h ↦ f.le_iff_le.mp (hg h)⟩

@[simp]
theorem restrictDomain_coeff (f : G ↪o H) (x : K⟦H⟧) (g : G) :
    (restrictDomain f x).coeff g = x.coeff (f g) :=
  (rfl)

/-- Extending an exponent domain after restricting it recovers a series supported in the
embedding's range. -/
theorem embDomain_restrictDomain (f : G ↪o H) (x : K⟦H⟧)
    (hx : x.support ⊆ Set.range f) :
    embDomain f (restrictDomain f x) = x := by
  ext h
  by_cases hh : h ∈ Set.range f
  · obtain ⟨g, rfl⟩ := hh
    rw [embDomain_coeff, restrictDomain_coeff]
  · rw [embDomain_notin_range hh]
    have hzero : x.coeff h = 0 := by
      by_contra hne
      exact hh (hx hne)
    exact hzero.symm

/-- Restricting an extended Hahn series recovers the original series. -/
@[simp]
theorem restrictDomain_embDomain (f : G ↪o H) (x : K⟦G⟧) :
    restrictDomain f (embDomain f x) = x := by
  ext g
  rw [restrictDomain_coeff, embDomain_coeff]

section Cardinal

universe u' v'

variable {G' H' : Type u'} {K' : Type v'}
variable [PartialOrder G'] [PartialOrder H'] [Zero K']

/-- Extending the exponent domain along an order embedding preserves support cardinality. -/
theorem cardSupp_embDomain (f : G' ↪o H') (x : K'⟦G'⟧) :
    (embDomain f x).cardSupp = x.cardSupp := by
  rw [cardSupp, cardSupp, support_embDomain]
  exact Cardinal.mk_image_eq f.injective

end Cardinal

end HahnSeries

end
end

/-!
## Reindexing Hahn series along an ordered additive equivalence

An ordered additive equivalence of exponent groups induces a ring equivalence of Hahn-series
rings. This packages Mathlib's one-way exponent-domain embedding together with its inverse.
-/

section

public noncomputable section

namespace HahnSeries

variable {R G H : Type*}
variable [Semiring R]
variable [AddCommMonoid G] [LinearOrder G] [IsOrderedCancelAddMonoid G]
variable [AddCommMonoid H] [LinearOrder H] [IsOrderedCancelAddMonoid H]

/-- Reindex Hahn-series exponents along an ordered additive equivalence. -/
def embDomainRingEquiv (e : G ≃+o H) : R⟦G⟧ ≃+* R⟦H⟧ := by
  let f : G →+ H := e.toAddEquiv.toAddMonoidHom
  let F : R⟦G⟧ →+* R⟦H⟧ :=
    embDomainRingHom f e.injective fun _ _ ↦ e.map_le_map_iff'
  apply RingEquiv.ofBijective F
  constructor
  · exact embDomain_injective
  · intro y
    refine ⟨embDomain e.symm.toOrderIso.toOrderEmbedding y, ?_⟩
    ext h
    dsimp [F, f]
    have outer := embDomain_coeff (f := e.toOrderIso.toOrderEmbedding)
      (x := embDomain e.symm.toOrderIso.toOrderEmbedding y) (a := e.symm h)
    have inner := embDomain_coeff (f := e.symm.toOrderIso.toOrderEmbedding) (x := y) (a := h)
    have heh : e.toOrderIso.toOrderEmbedding (e.symm h) = h := e.apply_symm_apply h
    rw [heh] at outer
    exact outer.trans inner

@[simp]
theorem embDomainRingEquiv_coeff (e : G ≃+o H) (x : R⟦G⟧) (g : G) :
    (embDomainRingEquiv e x).coeff (e g) = x.coeff g :=
  embDomain_coeff

/-- Reindexing exponents along an ordered additive equivalence maps support pointwise. -/
@[simp]
theorem support_embDomainRingEquiv (e : G ≃+o H) (x : R⟦G⟧) :
    (embDomainRingEquiv e x).support = e '' x.support := by
  change (embDomain e.toOrderIso.toOrderEmbedding x).support = _
  exact support_embDomain e.toOrderIso.toOrderEmbedding x

section Cardinal

universe u v

variable {S : Type v} {G' H' : Type u}
variable [Semiring S]
variable [AddCommMonoid G'] [LinearOrder G'] [IsOrderedCancelAddMonoid G']
variable [AddCommMonoid H'] [LinearOrder H'] [IsOrderedCancelAddMonoid H']

/-- Reindexing exponents along an ordered additive equivalence preserves support cardinality. -/
theorem cardSupp_embDomainRingEquiv (e : G' ≃+o H') (x : S⟦G'⟧) :
    (embDomainRingEquiv e x).cardSupp = x.cardSupp := by
  rw [cardSupp, cardSupp]
  have hsupport : (embDomainRingEquiv e x).support = (fun g ↦ e g) '' x.support := by
    ext h
    constructor
    · intro hh
      refine ⟨e.symm h, ?_, e.apply_symm_apply h⟩
      rw [HahnSeries.mem_support]
      have hhCoeff := (HahnSeries.mem_support _ _).mp hh
      rw [← e.apply_symm_apply h, embDomainRingEquiv_coeff] at hhCoeff
      exact hhCoeff
    · rintro ⟨g, hg, rfl⟩
      rw [HahnSeries.mem_support, embDomainRingEquiv_coeff]
      exact (HahnSeries.mem_support _ _).mp hg
  rw [hsupport]
  exact Cardinal.mk_image_eq (f := fun g : G' ↦ e g) e.injective

end Cardinal

end HahnSeries

end
end
