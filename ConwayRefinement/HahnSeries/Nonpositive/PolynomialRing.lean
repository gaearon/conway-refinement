/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Nonpositive.FiniteSupport
public import ConwayRefinement.HahnSeries.Germ.PolynomialRing
public import ConwayRefinement.RingTheory.TruncationGerms.Series

import ConwayRefinement.Blueprint
public import Mathlib.Data.Real.Basic
import ConwayRefinement.HahnSeries.Germ.GermSupport
import ConwayRefinement.RingTheory.TruncationGerms.Transcendence
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Topology.Algebra.Ring.Real

/-!
# The series ring is a polynomial ring over the series with finite support

For real exponents and a field `K` of characteristic zero, the germs of nonpositive series satisfy
the axioms of `SeriesTruncationGerms`. The exponents at which a series has a nonzero germ form
the closure of its support, a closed well-ordered subset of `(-∞, 0]`; every nonempty part of it
below a bound has a greatest element.

A series has a constant germ at every exponent exactly when it has finite support. Hence the
subalgebra of series all of whose germs are constants is the finite-support subring
`K(ℝ^{≤0})`, and `K((ℝ^{≤0}))` is a polynomial ring over `K(ℝ^{≤0})`.
-/

open Set Filter Topology
open scoped HahnSeries

universe v w

public noncomputable section

namespace HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

omit [CharZero K] in
/-- Each nonempty part, below a bound, of the set of exponents at which a series with real
exponents has a nonzero germ has a greatest element. -/
theorem exists_isGreatest_setOf_germAt_ne_zero_inter_Iic (b : Nonpositive ℝ K) (ε : ℝ)
    (hne : ({ξ | germAt ξ b ≠ 0} ∩ Set.Iic ε).Nonempty) :
    ∃ ζ ∈ {ξ | germAt ξ b ≠ 0} ∩ Set.Iic ε, ∀ ξ ∈ {ξ | germAt ξ b ≠ 0} ∩ Set.Iic ε, ξ ≤ ζ := by
  have hclosed : IsClosed ({ξ | germAt ξ b ≠ 0} ∩ Set.Iic ε) := by
    rw [setOf_germAt_ne_zero]; exact isClosed_closure.inter isClosed_Iic
  have hbdd : BddAbove ({ξ | germAt ξ b ≠ 0} ∩ Set.Iic ε) := ⟨ε, fun x hx => hx.2⟩
  exact ⟨sSup _, hclosed.csSup_mem hne hbdd, fun ξ hξ => le_csSup hbdd hξ⟩

omit [CharZero K] in
/-- A series with real exponents all of whose germs are constants has finite support. -/
theorem support_finite_of_forall_germAt_mem_range (b : Nonpositive ℝ K)
    (h : ∀ ξ, germAt ξ b ∈ Set.range (algebraMap K (Nonpositive ℝ K ⧸
        boundedAwayIdeal ℝ K))) :
    (b : HahnSeries ℝ K).support.Finite := by
  set T := (b : HahnSeries ℝ K).support
  -- Each exponent has a left gap containing no support point.
  have hgap : ∀ ξ : ℝ, ∃ ρ > 0, ∀ y, ξ - ρ < y → y < ξ → y ∉ T := by
    intro ξ
    obtain ⟨ε, hε, hvan⟩ := (germAt_mem_range_algebraMap_iff b ξ).mp (h ξ)
    refine ⟨-ε, by linarith, fun y hylo hyhi hyT => ?_⟩
    have := hvan (y - ξ) (by linarith) (by linarith)
    rw [add_sub_cancel] at this
    exact (germAt_ne_zero_iff b y).mpr (subset_closure hyT) this
  by_contra hinf
  have hTwf : T.IsWF := (b : HahnSeries ℝ K).isWF_support
  obtain ⟨lb, hlb⟩ : BddBelow T := by
    rcases T.eq_empty_or_nonempty with he | hne
    · rw [he]; exact bddBelow_empty
    · exact ⟨hTwf.min hne, fun a ha => hTwf.min_le hne ha⟩
  obtain ⟨ξ, -, hacc⟩ := (Set.not_finite.mp hinf).exists_accPt_of_subset_isCompact isCompact_Icc
    fun x hx => ⟨hlb hx, support_subset b hx⟩
  rw [accPt_iff_nhds] at hacc
  obtain ⟨ρ, hρ, hgapξ⟩ := hgap ξ
  -- The points of `T` just above `ξ` are bounded away from `ξ`.
  obtain ⟨σ, hσ, hright⟩ : ∃ σ > 0, ∀ y ∈ T, ξ < y → ξ + σ ≤ y := by
    rcases (T ∩ Set.Ioi ξ).eq_empty_or_nonempty with hUe | hUne
    · exact ⟨1, one_pos, fun y hyT hy => absurd (hUe ▸ ⟨hyT, hy⟩ : y ∈ (∅ : Set ℝ))
        (Set.notMem_empty y)⟩
    · have hUwf : (T ∩ Set.Ioi ξ).IsWF := hTwf.mono Set.inter_subset_left
      refine ⟨hUwf.min hUne - ξ, sub_pos.mpr (hUwf.min_mem hUne).2, fun y hyT hy => ?_⟩
      linarith [hUwf.min_le hUne ⟨hyT, hy⟩]
  obtain ⟨y, ⟨hyball, hyT⟩, hyne⟩ :=
    hacc (Metric.ball ξ (min ρ σ)) (Metric.ball_mem_nhds ξ (lt_min hρ hσ))
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hyball
  rcases lt_or_gt_of_ne hyne with hlt | hgt
  · exact hgapξ y (by linarith [min_le_left ρ σ]) hlt hyT
  · linarith [hright y hyT hgt, min_le_right ρ σ]

omit [CharZero K] in
/-- A series with real exponents has a constant germ at every exponent exactly when it has finite
support. -/
@[blueprint "lem:constant-germs-finite-support"
  (phase := "Polynomial presentations")
  (title := "Series with constant germs")
  (statement := /--
    Let $K$ be a field.  A series $b\in K((\mathbb R^{\le0}))$ has a constant
    germ $[b^{|\gamma}]\in K$ at every exponent $\gamma$ if and only if
    $\operatorname{supp}(b)$ is finite.
  -/)
  (proof := /--
    If the support is finite, then to the left of each $\gamma$ there is an
    interval containing no point of the closed support, so by
    \ref{lem:nonzero-germs} the germs at $\gamma+\zeta$ vanish for $\zeta<0$
    close to $0$, and the germ at $\gamma$ is constant by
    \ref{lem:constant-germs}.  Conversely, if every germ is constant, then by
    \ref{lem:constant-germs} and \ref{lem:nonzero-germs} every
    $\gamma\in\mathbb R$ has a left interval free of support points.  An
    infinite support would be bounded, hence have an accumulation point
    $\gamma$ in a compact interval; points of the support accumulate at
    $\gamma$ neither from the left, by the gap, nor from the right, because the
    support is well ordered.  So the support is finite.
  -/)]
theorem forall_germAt_mem_range_iff_support_finite (b : Nonpositive ℝ K) :
    (∀ ξ, germAt ξ b ∈ Set.range (algebraMap K (Nonpositive ℝ K ⧸
        boundedAwayIdeal ℝ K))) ↔
      (b : HahnSeries ℝ K).support.Finite :=
  ⟨support_finite_of_forall_germAt_mem_range b, germAt_mem_range_algebraMap_of_finite b⟩

variable (K) in
/-- For real exponents, the germs of nonpositive series satisfy the axioms of
`SeriesTruncationGerms` on `K((ℝ^{≤0}))`. -/
def seriesTruncationGerms : SeriesTruncationGerms K ℝ (Nonpositive ℝ K)
    (Nonpositive ℝ K ⧸ boundedAwayIdeal ℝ K) where
  __ := truncationGerms ℝ K
  eq_zero_of_germAt := by
    simpa only [truncationGerms_germAt] using eq_zero_of_forall_germAt_eq_zero
  exists_truncation := by simpa only [truncationGerms_germAt] using exists_germAt_truncation
  exists_monomial γ hγ := ⟨single γ 1 hγ, by
    simpa only [truncationGerms_germAt] using germAt_single_mul γ hγ⟩
  germSupport_isWF := by simpa only [truncationGerms_germAt] using isWF_setOf_germAt_ne_zero
  germSupport_exists_max := by
    simpa only [truncationGerms_germAt] using exists_isGreatest_setOf_germAt_ne_zero_inter_Iic

@[simp]
theorem seriesTruncationGerms_germAt (γ : ℝ) :
    (seriesTruncationGerms K).germAt γ = germAt γ :=
  truncationGerms_germAt γ

@[simp]
theorem seriesTruncationGerms_germ (b : Nonpositive ℝ K) :
    (seriesTruncationGerms K).germ b = Ideal.Quotient.mk (boundedAwayIdeal ℝ K) b :=
  truncationGerms_germ b

/-- The series all of whose germs are constants are exactly the series with finite support. -/
theorem mem_seriesWithConstantGerms_iff (b : Nonpositive ℝ K) :
    b ∈ (seriesTruncationGerms K).seriesWithConstantGerms ↔
      b ∈ (finiteSupportSubring : Subring (Nonpositive ℝ K)) := by
  rw [SeriesTruncationGerms.mem_seriesWithConstantGerms, mem_finiteSupportSubring_iff,
    ← forall_germAt_mem_range_iff_support_finite]
  simp only [seriesTruncationGerms_germAt]

private theorem toSubring_seriesWithConstantGerms :
    (finiteSupportSubring : Subring (Nonpositive ℝ K)) =
      (seriesTruncationGerms K).seriesWithConstantGerms.toSubring :=
  Subring.ext fun b => (mem_seriesWithConstantGerms_iff b).symm

/-- The nonpositive real series ring over a field of characteristic zero is a polynomial ring
over its finite-support subring `K(ℝ^{≤0})`. -/
@[blueprint "thm:hahn-series-polynomial-algebra"
  (phase := "Polynomial presentations")
  (title := "Polynomial presentation of $K((\\mathbb R^{\\le 0}))$")
  (statement := /--
    Let $K$ be a field of characteristic $0$ and $K(\mathbb R^{\le0})$ the
    subring of $K((\mathbb R^{\le0}))$ consisting of the series with finite
    support.  For some set $I$ there is a $K(\mathbb R^{\le0})$-algebra
    isomorphism
    \[
      K(\mathbb R^{\le0})[X_i:i\in I]\simeq K((\mathbb R^{\le0})).
    \]
  -/)
  (proof := /--
    Write $A=K((\mathbb R^{\le0}))$ and $Q=A/J$. For a $K$-subalgebra
    $S\subseteq Q$ let $A_S$ be the $K$-subalgebra of series all of whose
    germs lie in $S$; by \ref{lem:constant-germs-finite-support},
    $A_K=K(\mathbb R^{\le0})$. A $K$-subalgebra $R\subseteq A$ is closed
    under truncation if $b_{|\eta}\in R$ for all $b\in R$ and
    $\eta\in\mathbb R$; each $A_S$ is. For real exponents, a series all of
    whose germs vanish is $0$; the truncation $b_{|\eta}$ keeps exactly the
    germs of $b$ at exponents $\le\eta$; multiplication by $t^\gamma$
    translates germs by $\gamma$; and the exponents at which $b$ has a
    nonzero germ form the closure of $\operatorname{supp}(b)$, a closed
    well-ordered subset of $(-\infty,0]$ whose intersection with any ray
    $(-\infty,\varepsilon]$ has a greatest element when nonempty.

    Step 1: closure under truncation of a simple extension. Let $R$ be
    closed under truncation and let $X\in A$ with $X_{|\zeta}\in R$ for
    every $\zeta<0$; then $E=R[X]$ is closed under truncation. It suffices
    to show that if all truncations of $w$ lie in $E$, then so do all
    truncations of $wX$; induction on $n$ then handles $aX^n$ with $a\in R$,
    and these span $E$. Fix $\eta$, and show $(w_{|\beta}X)_{|\eta}\in E$ by
    well-founded induction on the exponents $\beta$ at which $w$ has a
    nonzero germ. If $\beta\le\eta$, then $w_{|\beta}X$ has no germs above
    $\eta$ and equals its own truncation. If $\beta>\eta$, well-foundedness
    gives $\beta'\in[\eta,\beta)$ such that $X$ has no nonzero germ at
    exponents in $(\eta-\beta,\eta-\beta')$. The series
    $v=w_{|\beta}-w_{|\beta'}$ has germs only in $(\beta',\beta]$, and the
    convolution formula gives $(vX)_{|\eta}=v\,X_{|\eta-\beta}\in E$ since
    $\eta-\beta<0$. The remaining term $(w_{|\beta'}X)_{|\eta}$ is covered
    by the induction hypothesis, because $w_{|\beta'}=w_{|\zeta}$ for the
    greatest $\zeta\le\beta'$ at which $w$ has a nonzero germ.

    Step 2: a series with transcendental germ is transcendental. Let
    $S\subseteq Q$ be a $K$-subalgebra, $R_0\subseteq A_S$ an
    $A_K$-subalgebra, and $X\in A$ with $[X]$ transcendental over $S$; then
    $X$ is transcendental over $R_0$. Indeed, let $\sum_kc_kX^k=0$ with
    $c_k\in R_0$ not all zero, and let $\eta$ be the greatest exponent at
    which some $c_k$ has a nonzero germ. No $c_k$ has germs above $\eta$, so
    the convolution formula gives $[(c_kX^k)^{|\eta}]=[c_k^{|\eta}]\,[X]^k$.
    Hence $\sum_k[c_k^{|\eta}]\,[X]^k=0$ is a nontrivial polynomial relation
    for $[X]$ over $S$.

    Step 3: generation. Let $S\subseteq Q$ be a $K$-subalgebra, and let
    $R\subseteq A$ be a $K$-subalgebra that is closed under truncation,
    contains $A_K$, and contains for every $a\in S$ some $r$ with $[r]=a$;
    then $A_S\subseteq R$. Let $b\in A_S$, and show $b_{|\eta}\in R$ by
    well-founded induction on the exponents $\eta$ at which $b$ has a
    nonzero germ. Choose $r\in R$ with $[r]=[b^{|\eta}]$ and put $c=t^\eta
    r$. The monomial $t^\eta$ has finite support, so $c\in R$, and $c$ has
    no germs above $\eta$. The difference $d=b_{|\eta}-c$ has
    $[d^{|\eta}]=0$ and no germs above $\eta$; by the characterisation of
    constant germs its germs vanish on some $(\varepsilon,\eta]$, so
    $d=b_{|\varepsilon}-c_{|\varepsilon}$. Here $c_{|\varepsilon}\in R$ by
    closure under truncation, and $b_{|\varepsilon}=b_{|\zeta}$ for the
    greatest $\zeta\le\varepsilon$ at which $b$ has a nonzero germ, which
    lies in $R$ by induction. Finally $b=b_{|\eta}$ for the greatest $\eta$
    at which $b$ has a nonzero germ.

    By Zorn's lemma choose a maximal set $\mathcal X\subseteq A$,
    algebraically independent over $A_K$, such that $R=A_K[\mathcal X]$ is
    closed under truncation and $R\subseteq A_S$ for $S=K[\{[X]:X\in\mathcal
    X\}]$. By Step 3, $R=A_S$. Suppose that $S\ne Q$. As in the polynomial
    presentation of the ring of germs, a germ outside $S$ with least
    Cantor--Bendixson value is $[X]$ for a series $X$ whose germs at
    negative exponents lie in $S$. By \ref{thm:bounded-away-ideal-prime},
    $Q$ is an integral domain, hence so is $S$. Every element of $S$ is the
    germ of an element of $R=A_S$, so the transcendence lemma makes $[X]$
    transcendental over $S$. By Step 2, $X$ is transcendental over $R$. For
    $\zeta<0$ all germs of $X_{|\zeta}$ lie in $S$, so $X_{|\zeta}\in
    A_S=R$, and by Step 1 $R[X]$ is closed under truncation. Thus $\mathcal
    X\cup\{X\}$ contradicts the maximality of $\mathcal X$. Hence $S=Q$ and
    $R=A_Q=A$, and evaluation at $\mathcal X$ is an isomorphism
    $A_K[X_i:i\in\mathcal X]\simeq A$ of $A_K$-algebras, with $A_K=K(\mathbb
    R^{\le0})$.
  -/)
  (highlight)]
theorem exists_mvPolynomial_algEquiv_finiteSupportRing :
    ∃ ι : Type (max v w), Nonempty (MvPolynomial ι (FiniteSupportRing (G := ℝ) (K := K)) ≃ₐ[
      FiniteSupportRing (G := ℝ) (K := K)] Nonpositive ℝ K) := by
  set B := (seriesTruncationGerms K).seriesWithConstantGerms
  obtain ⟨𝒳, hind, htop⟩ :=
    (seriesTruncationGerms K).exists_algebraicIndependent_series_generators
      fun S hS X hX hx ↦ by
        simp only [TruncationGerms.HasRepresentativesWithGermsIn, seriesTruncationGerms_germ,
          seriesTruncationGerms_germAt] at hS hX hx ⊢
        exact (transcendental_mk_of_germAt_mem S hS X hX hx).1
  let e : MvPolynomial 𝒳 B ≃ₐ[B] Nonpositive ℝ K := hind.mvPolynomialAlgEquivOfAdjoinEqTop htop
  let φ : FiniteSupportRing (G := ℝ) (K := K) ≃+* B :=
    RingEquiv.subringCongr toSubring_seriesWithConstantGerms
  let ψ : MvPolynomial (ULift.{w} 𝒳) (FiniteSupportRing (G := ℝ) (K := K)) ≃+* Nonpositive ℝ K :=
    ((MvPolynomial.renameEquiv _ Equiv.ulift).toRingEquiv.trans
      (MvPolynomial.mapEquiv 𝒳 φ)).trans e.toRingEquiv
  refine ⟨ULift.{w} 𝒳, ⟨AlgEquiv.ofRingEquiv (f := ψ) fun f => ?_⟩⟩
  change e (MvPolynomial.map (φ : FiniteSupportRing (G := ℝ) (K := K) →+* B)
    (MvPolynomial.rename Equiv.ulift (MvPolynomial.C f))) = (f : Nonpositive ℝ K)
  rw [MvPolynomial.rename_C, MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, e.commutes]
  rfl

end HahnSeries.Nonpositive
