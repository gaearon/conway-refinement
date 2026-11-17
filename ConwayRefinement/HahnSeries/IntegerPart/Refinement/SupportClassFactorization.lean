/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.LimitTailQuotient
public import ConwayRefinement.HahnSeries.ConvexQuotientSplitting
public import ConwayRefinement.HahnSeries.SupportArchimedeanClasses
public import ConwayRefinement.HahnSeries.IntegerPart.Refinement.ConvexRestriction
public import ConwayRefinement.Algebra.Order.ArchimedeanBall

import ConwayRefinement.Blueprint

/-!
# Factoring at a support class in a tail quotient

After regrouping along a common tail, the Archimedean classes met by the support of a series are
cofinal among the classes of the quotient, and a class met by the support determines a nonzero
convex restriction. Factoring off that restriction leaves an integral cofactor with constant
coefficient one whose nonzero support classes have strictly smaller order type.
-/

public noncomputable section

open Cardinal
open scoped HahnSeries

universe u v

namespace HahnSeries

variable {G : Type u} {R : Type*}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Module ℚ G] [PosSMulMono ℚ G]
  [Semiring R]

/-- A quotient class met by the support bounds a strict initial segment of the original support
classes. -/
@[blueprint "lem:tail-quotient-class-bounds-support-classes"
  (phase := "Refinement over Archimedean classes")
  (title := "Support classes beyond a quotient Archimedean ball")
  (statement := /--
    Let $T$ be a family of nonzero Archimedean classes of an ordered rational
    vector space $G$, and let $q$ be a nonzero Archimedean class of the quotient
    by the common tail below $T$.  Suppose $q$ is met by the image of a set
    $S\subseteq G$.  If every nonzero element of $W\subseteq G$ maps outside
    the closed ball of $q$ and has an Archimedean class met by $S$, then there
    is a nonzero class $c$ met by $S$ such that every class met by $W$ is
    strictly below $c$ and is met by $S$.
  -/)
  (proof := /--
    Choose $y\in S$ whose image has class $q$.  For $g\in W\setminus\{0\}$,
    being outside the closed ball of $q$ says that the quotient class of $g$ is
    strictly larger in magnitude than that of $y$.  The common-tail quotient
    reflects this strict comparison to the original Archimedean-class order,
    so the class of $g$ lies strictly below the class of $y$.
  -/)]
theorem exists_nonzeroSupportClass_bound_tailQuotient
    (T : Set (FiniteArchimedeanClass G))
    (q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T))
    (S W : Set G)
    (hqocc : q.1 ∈ ArchimedeanClass.mk ''
      (Submodule.Quotient.mk (p := FiniteArchimedeanClass.tailSubmodule ℚ T) '' S))
    (hW : ∀ g ∈ W, g ≠ 0 →
      Submodule.Quotient.mk g ∉ FiniteArchimedeanClass.closedBallAddSubgroup q)
    (hWocc : ∀ g ∈ W, g ≠ 0 →
      ArchimedeanClass.mk g ∈ ArchimedeanClass.mk '' S) :
    ∃ c ∈ ArchimedeanClass.mk '' (S \ {0}),
      ArchimedeanClass.mk '' (W \ {0}) ⊆
        (ArchimedeanClass.mk '' (S \ {0})) ∩ Set.Iio c := by
  obtain ⟨yq, ⟨y, hyS, rfl⟩, hyq⟩ := hqocc
  have hy0 : y ≠ 0 := by
    intro hy
    subst y
    have hqtop : q.1 = ⊤ := by
      rw [← hyq]
      exact ArchimedeanClass.mk_eq_top_iff.mpr (Submodule.Quotient.mk_zero _)
    exact q.2 hqtop
  refine ⟨ArchimedeanClass.mk y, ⟨y, ⟨hyS, by simpa using hy0⟩, rfl⟩, ?_⟩
  rintro _ ⟨g, ⟨hgW, hg0⟩, rfl⟩
  rw [Set.mem_singleton_iff] at hg0
  obtain ⟨z, hzS, hzg⟩ := hWocc g hgW hg0
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    rw [ArchimedeanClass.mk_zero] at hzg
    exact hg0 (ArchimedeanClass.mk_eq_top_iff.mp hzg.symm)
  refine ⟨⟨z, ⟨hzS, by simpa using hz0⟩, hzg⟩, ?_⟩
  have hgq : ArchimedeanClass.mk
      (Submodule.Quotient.mk g : FiniteArchimedeanClass.TailQuotient T) <
      ArchimedeanClass.mk
        (Submodule.Quotient.mk y : FiniteArchimedeanClass.TailQuotient T) := by
    apply ArchimedeanClass.mk_lt_of_not_mem_closedBallAddSubgroup
    intro hmem
    apply hW g hgW hg0
    apply FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff.mpr
    intro hgq0
    change q.1 ≤ ArchimedeanClass.mk
      (Submodule.Quotient.mk g : FiniteArchimedeanClass.TailQuotient T)
    rw [← hyq]
    exact ArchimedeanClass.mem_closedBallAddSubgroup_iff.mp hmem
  exact FiniteArchimedeanClass.archimedeanClass_mk_lt_of_tailQuotient_mk_lt T hgq

/-- If the support meets every class of a limit block, its nonzero outer classes after tail
regrouping are cofinal in the tail quotient. -/
theorem isCofinal_supportArchimedeanClasses_convexQuotientSplit
    (T₀ T₁ : Set (ArchimedeanClass G))
    (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b)
    (x : HahnSeries G R)
    (hxclasses : ArchimedeanClass.mk '' x.support = T₀ ∪ T₁) :
    let T : Set (FiniteArchimedeanClass G) := {c | c.1 ∈ T₀}
    let P := FiniteArchimedeanClass.tailSubmodule ℚ T
    let y := convexQuotientSplitRingEquiv P x
    IsCofinal {q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T) |
      q.1 ∈ ArchimedeanClass.mk '' y.support} := by
  dsimp only
  intro q
  induction q using FiniteArchimedeanClass.ind with
  | mk z hz =>
    obtain ⟨c, hcz⟩ := FiniteArchimedeanClass.exists_tailQuotient_positiveRepresentative_le
      (T := {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) (abs_pos.mpr hz)
    obtain ⟨d, hdT₀, hcd⟩ := hT₀gt c.1 c.2
    obtain ⟨e, heT₀, hde⟩ := hT₀gt d hdT₀
    obtain ⟨f, _hfT₀, hef⟩ := hT₀gt e heT₀
    have hdOcc : d ∈ ArchimedeanClass.mk '' x.support := by
      rw [hxclasses]
      exact Or.inl hdT₀
    obtain ⟨g, hg, hgd⟩ := hdOcc
    let P := FiniteArchimedeanClass.tailSubmodule ℚ
      {c : FiniteArchimedeanClass G | c.1 ∈ T₀}
    let qp : (FiniteArchimedeanClass.TailQuotient
        {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) × P :=
      ofLex ((Submodule.quotientLexEquiv P).symm g)
    let zq : FiniteArchimedeanClass.TailQuotient
        {c : FiniteArchimedeanClass G | c.1 ∈ T₀} := qp.1
    let p : P := qp.2
    have hzqmk : Submodule.Quotient.mk g = zq := by
      have hrepr : Submodule.quotientLexEquiv P (toLex qp) = g := by
        change Submodule.quotientLexEquiv P
          ((Submodule.quotientLexEquiv P).symm g) = g
        exact (Submodule.quotientLexEquiv P).apply_symm_apply g
      rw [← hrepr, Submodule.quotientLexEquiv_apply,
        Submodule.mk_quotientProdLinearEquiv]
      rfl
    have hzq0 : zq ≠ 0 := by
      intro hzq
      have hgP : g ∈ P := by
        rw [← Submodule.Quotient.mk_eq_zero P, hzqmk, hzq]
      have heleg : e ≤ ArchimedeanClass.mk g :=
        FiniteArchimedeanClass.mem_tailKernel_iff.mp
          ((FiniteArchimedeanClass.mem_tailSubmodule_iff (K := ℚ)).mp hgP)
          ⟨⟨e, ne_top_of_lt hef⟩, heT₀⟩
      rw [hgd] at heleg
      exact (not_le_of_gt hde) heleg
    have hzqsupp : zq ∈ (convexQuotientSplitRingEquiv P x).support := by
      rw [mem_support]
      intro hzero
      have hcoeff := congrArg (fun s : R⟦P⟧ ↦ s.coeff p) hzero
      rw [convexQuotientSplitRingEquiv_coeff] at hcoeff
      have hlex : Submodule.quotientLexEquiv P (toLex (zq, p)) = g := by
        change Submodule.quotientLexEquiv P (toLex qp) = g
        exact (Submodule.quotientLexEquiv P).apply_symm_apply g
      rw [hlex] at hcoeff
      exact (mem_support _ _).mp hg hcoeff
    refine ⟨FiniteArchimedeanClass.mk zq hzq0, ?_, ?_⟩
    · exact ⟨zq, hzqsupp, rfl⟩
    · change ArchimedeanClass.mk z ≤ ArchimedeanClass.mk zq
      rw [ArchimedeanClass.mk_le_mk]
      have habs : |zq| ≤ |z| := calc
        |zq| = (Submodule.Quotient.mk |g| : FiniteArchimedeanClass.TailQuotient
            {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) := by
          rw [← hzqmk]
          exact FiniteArchimedeanClass.tailQuotient_abs
            {c : FiniteArchimedeanClass G | c.1 ∈ T₀} g
        _ ≤ (Submodule.Quotient.mk (FiniteArchimedeanClass.positiveRepresentative c.1) :
            FiniteArchimedeanClass.TailQuotient
              {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) := by
          apply ConvexQuotient.mk_le_mk
          have hcg : c.1 < ArchimedeanClass.mk g := hcd.trans_eq hgd.symm
          have hdom := ArchimedeanClass.mk_lt_mk.mp
            (FiniteArchimedeanClass.mk_positiveRepresentative c.1 ▸ hcg) 1
          simpa only [one_nsmul,
            abs_of_pos (FiniteArchimedeanClass.positiveRepresentative_pos c.1)] using hdom.le
        _ ≤ |z| := hcz
      exact ⟨1, by simpa only [one_nsmul] using habs⟩

end HahnSeries

namespace HahnSeries.CardSuppLTTruncationIntegerPart

open Classical in
/-- Factoring at a tail-quotient class met by the support strictly lowers the order type of the
nonzero support classes of the complementary factor. -/
@[blueprint "lem:support-class-factorisation"
  (phase := "Refinement over Archimedean classes")
  (title := "Factorisation at a quotient Archimedean class")
  (statement := /--
    Let $T$ be a set of nonzero Archimedean classes of an ordered rational
    vector space $G$, and let $q$ be a nonzero Archimedean class of the quotient
    of $G$ by the common tail below $T$.  Suppose the support of
    $b\in Z+R((G^{<0}))_\kappa$ meets $q$ and the restriction $t$ of $b$ to
    the inverse image of the closed ball of $q$ is nonzero.  Then
    \[
      b=tw,
    \]
    where $w$ has constant coefficient $1$ and the order type of the nonzero
    Archimedean support classes of $w$ is strictly smaller than that of $b$.
  -/)
  (proof := /--
    By \ref{lem:factorisation-by-convex-restriction}, the retained restriction
    gives a factorisation $b=tw$, and every nonzero class met by $w$ is also met
    by $b$.  The quotient class $q$ and
    \ref{lem:tail-quotient-class-bounds-support-classes} bound all those classes
    strictly below one class met by $b$.  The strict order-type inequality
    follows from \ref{lem:support-class-order-type-strict-decrease}.
  -/)]
theorem exists_factor_with_smaller_support_class_orderType
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)]
    (Z : Subring R)
    (T : Set (FiniteArchimedeanClass G))
    (q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T))
    (b : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z)
    (hqocc : q.1 ∈ ArchimedeanClass.mk ''
      (Submodule.Quotient.mk (p := FiniteArchimedeanClass.tailSubmodule ℚ T) ''
        (b : HahnSeries G R).support))
    (hne : HahnSeries.filter
      (· ∈ (FiniteArchimedeanClass.closedBallAddSubgroup q).comap
        (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ.toAddMonoidHom)
      (b : HahnSeries G R) ≠ 0) :
    ∃ t w : HahnSeries.cardSuppLTTruncationIntegerPart
        (G := G) (R := R) (κ := κ) Z,
      (t : HahnSeries G R) = HahnSeries.filter
        (· ∈ (FiniteArchimedeanClass.closedBallAddSubgroup q).comap
          (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ.toAddMonoidHom)
        (b : HahnSeries G R) ∧
      b = t * w ∧ (w : HahnSeries G R).coeff 0 = 1 ∧
      (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z w)).orderType <
      (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z b)).orderType := by
  classical
  let P := FiniteArchimedeanClass.tailSubmodule ℚ T
  let C : AddSubgroup G :=
    (FiniteArchimedeanClass.closedBallAddSubgroup q).comap P.mkQ.toAddMonoidHom
  letI : C.IsConvex := by
    constructor
    exact (FiniteArchimedeanClass.closedBall_ordConnected q).preimage_mono
      (fun _ _ h ↦ ConvexQuotient.mk_le_mk h)
  obtain ⟨t, w, ht, hfac, hw0, hwC, hwocc⟩ :=
    exists_factorization_by_restriction Z
      (inferInstance : C.IsConvex).ordConnected b hne
  refine ⟨t, w, ht, hfac, hw0, ?_⟩
  let bN := toNonpositiveRingHom Z b
  let wN := toNonpositiveRingHom Z w
  obtain ⟨c, hc, hsub⟩ :=
    HahnSeries.exists_nonzeroSupportClass_bound_tailQuotient
      T q (b : HahnSeries G R).support (w : HahnSeries G R).support hqocc
      (by
        intro g hg hg0
        exact hwC g hg hg0)
      hwocc
  have hc' : c ∈ bN.nonzeroSupportArchimedeanClasses := by
    rw [HahnSeries.Nonpositive.mem_nonzeroSupportArchimedeanClasses_iff]
    obtain ⟨g, ⟨hg, hg0⟩, hgc⟩ := hc
    exact ⟨g, by simpa only [bN, coe_toNonpositiveRingHom] using hg,
      by simpa only [Set.mem_singleton_iff] using hg0, hgc⟩
  apply HahnSeries.Nonpositive.orderType_nonzeroSupportArchimedeanClasses_lt bN wN hc'
  intro d hd
  rw [HahnSeries.Nonpositive.mem_nonzeroSupportArchimedeanClasses_iff] at hd
  obtain ⟨g, hg, hg0, hgd⟩ := hd
  have hg' : g ∈ (w : HahnSeries G R).support := by
    simpa only [wN, coe_toNonpositiveRingHom] using hg
  have hd' := hsub ⟨g, ⟨hg', by simpa only [Set.mem_singleton_iff] using hg0⟩, hgd⟩
  refine ⟨?_, hd'.2⟩
  rw [HahnSeries.Nonpositive.mem_nonzeroSupportArchimedeanClasses_iff]
  obtain ⟨z, ⟨hz, hz0⟩, hzd⟩ := hd'.1
  exact ⟨z, by simpa only [bN, coe_toNonpositiveRingHom] using hz,
    by simpa only [Set.mem_singleton_iff] using hz0, hzd⟩

end HahnSeries.CardSuppLTTruncationIntegerPart
