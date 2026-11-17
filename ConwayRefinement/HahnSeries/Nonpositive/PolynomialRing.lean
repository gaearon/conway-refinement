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
public import ConwayRefinement.HahnSeries.Germ.GermSupport
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
    Let $G=\mathbb R$. A series $b\in A$ has all its germs in $K$ if and only if
    $\operatorname{supp}(b)$ is finite.
  -/)
  (proof := /--
    If the support is finite, then to the left of each $\gamma$ there is an interval containing no
    point of the closed support, so by \ref{lem:nonzero-germs} the germs at $\gamma+\zeta$ vanish
    for $\zeta<0$ close to $0$, and the germ at $\gamma$ is constant by \ref{lem:constant-germs}.
    Conversely, if every germ is constant, then by \ref{lem:constant-germs} and
    \ref{lem:nonzero-germs} every $\gamma\in\mathbb R$ has a left interval free of support points.
    An infinite support would be bounded, hence have an accumulation point $\gamma$ in a compact
    interval. Points of the support accumulate at $\gamma$ neither from the left, by the gap, nor
    from the right, because the support is well ordered. So the support is finite.
  -/)]
theorem forall_germAt_mem_range_iff_support_finite (b : Nonpositive ℝ K) :
    (∀ ξ, germAt ξ b ∈ Set.range (algebraMap K (Nonpositive ℝ K ⧸
        boundedAwayIdeal ℝ K))) ↔
      (b : HahnSeries ℝ K).support.Finite :=
  ⟨support_finite_of_forall_germAt_mem_range b, germAt_mem_range_algebraMap_of_finite b⟩

variable (K) in
/-- For real exponents, the germs of nonpositive series satisfy the axioms of `SeriesGerms` on
`K((ℝ^{≤0}))`. -/
def seriesGerms : SeriesGerms K ℝ (Nonpositive ℝ K) (Nonpositive ℝ K ⧸ boundedAwayIdeal ℝ K) where
  __ := convolutionGerms ℝ K
  eq_zero_of_germAt := by
    simp only [convolutionGerms_germAt]; exact eq_zero_of_forall_germAt_eq_zero
  exists_truncation := by simp only [convolutionGerms_germAt]; exact exists_germAt_truncation
  exists_monomial γ hγ := ⟨single γ 1 hγ, by
    simp only [convolutionGerms_germAt]; exact germAt_single_mul γ hγ⟩
  germSupport_isWF := by simp only [convolutionGerms_germAt]; exact isWF_setOf_germAt_ne_zero
  germSupport_exists_max := by
    simp only [convolutionGerms_germAt]; exact exists_isGreatest_setOf_germAt_ne_zero_inter_Iic

omit [CharZero K] in
@[simp]
theorem seriesGerms_germAt (γ : ℝ) : (seriesGerms K).germAt γ = germAt γ :=
  convolutionGerms_germAt γ

omit [CharZero K] in
@[simp]
theorem seriesGerms_germ (b : Nonpositive ℝ K) :
    (seriesGerms K).germ b = Ideal.Quotient.mk (boundedAwayIdeal ℝ K) b :=
  convolutionGerms_germ b

omit [CharZero K] in
@[simp]
theorem seriesGerms_truncation (b : Nonpositive ℝ K) (η : ℝ) :
    (seriesGerms K).truncation b η = truncation η b :=
  (seriesGerms K).truncation_eq fun ξ ↦ by simpa using germAt_truncation b η ξ

omit [CharZero K] in
theorem seriesGerms_isTruncationClosed_iff {R : Subalgebra K (Nonpositive ℝ K)} :
    (seriesGerms K).IsTruncationClosed R ↔ ∀ b ∈ R, ∀ η : ℝ, truncation η b ∈ R := by
  simp [SeriesGerms.isTruncationClosed_iff]

variable (K) in
/-- For real exponents, the germs of nonpositive series satisfy the axioms of
`SeriesTruncationGerms` on `K((ℝ^{≤0}))`. -/
def seriesTruncationGerms : SeriesTruncationGerms K ℝ (Nonpositive ℝ K)
    (Nonpositive ℝ K ⧸ boundedAwayIdeal ℝ K) :=
  { seriesGerms K with
    exists_translatedTruncation b ξ _ := ⟨translatedTruncation ξ b, fun _ hζ => by
      simpa using germAt_translatedTruncation b ξ hζ⟩
    germAt_eventually_eq_zero b hb := by
      simpa using (germAt_mem_range_algebraMap_iff b 0).mp (by simpa using hb)
    germ_mem_range_of_eventually b hb := by
      simpa using (germAt_mem_range_algebraMap_iff b 0).mpr (by simpa using hb) }

omit [CharZero K] in
@[simp]
theorem seriesTruncationGerms_germ (b : Nonpositive ℝ K) :
    (seriesTruncationGerms K).germ b = Ideal.Quotient.mk (boundedAwayIdeal ℝ K) b :=
  seriesGerms_germ b

omit [CharZero K] in
/-- The series all of whose germs are constants are exactly the series with finite support. -/
theorem mem_seriesWithConstantGerms_iff (b : Nonpositive ℝ K) :
    b ∈ (seriesGerms K).seriesWithConstantGerms ↔
      b ∈ (finiteSupportSubring : Subring (Nonpositive ℝ K)) := by
  rw [SeriesGerms.mem_seriesWithConstantGerms, mem_finiteSupportSubring_iff,
    ← forall_germAt_mem_range_iff_support_finite]
  simp only [seriesGerms_germAt]

omit [CharZero K] in
private theorem toSubring_seriesWithConstantGerms :
    (finiteSupportSubring : Subring (Nonpositive ℝ K)) =
      (seriesGerms K).seriesWithConstantGerms.toSubring :=
  Subring.ext fun b => (mem_seriesWithConstantGerms_iff b).symm

omit [CharZero K] in
/-- Let `R` be a subalgebra of `K((ℝ^{≤0}))` closed under the truncations `b ↦ b_{|η}`, and `X` a
series whose truncations at negative exponents lie in `R`. Then `R[X]` is closed under the
truncations. -/
@[blueprint "lem:truncations-of-simple-extension"
  (phase := "Polynomial presentations")
  (title := "Truncations in a simple extension")
  (statement := /--
    Let $G=\mathbb R$. Let $E\subseteq A$ be a $K$-subalgebra closed under truncation, and $X\in A$
    with $X_{|\zeta}\in E$ for all $\zeta<0$. Then $E[X]$ is closed under truncation.
  -/)
  (proof := /--
    Truncation at $\eta$ is $K$-linear, and $E[X]$ is spanned by the products $aX^n$ with $a\in E$.
    By induction on $n$ it suffices to show: if $u\in A$ satisfies $u_{|\eta}\in E[X]$ for all
    $\eta$, then $(uX)_{|\eta}\in E[X]$ for all $\eta$. Let $u\ne0$. By \ref{lem:nonzero-germs}, the
    exponents at which $u$ has a nonzero germ form the closed support $D$ of $u$, a well-ordered
    closed subset of $(-\infty,0]$. Applied to a difference, the same lemma shows that two series
    with the same germs are equal; and $u_{|\beta}=u_{|\zeta}$ if $\zeta$ is the greatest element of
    $D\cap(-\infty,\beta]$. Fix $\eta$. We show $(u_{|\beta}X)_{|\eta}\in E[X]$ for $\beta\in D$ by
    induction on $\beta$; for $\beta=\max D$ this is $(uX)_{|\eta}$.

    If $\beta\le\eta$, then by \ref{lem:convolution-formula}, a finite sum by
    \ref{lem:convolution-finite}, the series $u_{|\beta}X$ has no nonzero germ above $\eta$, so it
    equals its truncation at $\eta$, and it lies in $E[X]$.

    Let $\beta>\eta$. Choose $\beta'\in[\eta,\beta)$ such that $X$ has no nonzero germ at the
    exponents in $(\eta-\beta,\eta-\beta')$: let $\eta-\beta'$ be the least exponent above
    $\eta-\beta$ at which $X$ has a nonzero germ, or $\beta'=\eta$ if there is none. The series
    $v=u_{|\beta}-u_{|\beta'}\in E[X]$ has nonzero germs only in $(\beta',\beta]$. By
    \ref{lem:convolution-formula}, the germs of $(vX)_{|\eta}$ and $v\,X_{|\eta-\beta}$ at $\xi$ are
    sums of terms $[v^{|y}]\,[X^{|\xi-y}]$ with $y\in(\beta',\beta]$. For $\xi\le\eta$ we have
    $\xi-y<\eta-\beta'$, so the terms with $\xi-y>\eta-\beta$ vanish in both, and the remaining
    terms agree. For $\xi>\eta$ both germs vanish. Hence $(vX)_{|\eta}=v\,X_{|\eta-\beta}$, which
    lies in $E[X]$ because $X_{|\eta-\beta}\in E$, as $\eta-\beta<0$. Finally
    $u_{|\beta}X=u_{|\beta'}X+vX$, and $u_{|\beta'}$ is $0$ or $u_{|\zeta}$ for some $\zeta\in D$
    with $\zeta<\beta$, so $(u_{|\beta'}X)_{|\eta}\in E[X]$ by induction.
  -/)]
theorem truncation_mem_adjoin_insert {R : Subalgebra K (Nonpositive ℝ K)}
    (hR : ∀ b ∈ R, ∀ η : ℝ, truncation η b ∈ R) (X : Nonpositive ℝ K)
    (hX : ∀ ζ : ℝ, ζ < 0 → truncation ζ X ∈ R) :
    ∀ b ∈ Algebra.adjoin K (insert X (R : Set (Nonpositive ℝ K))), ∀ η : ℝ,
      truncation η b ∈ Algebra.adjoin K (insert X (R : Set (Nonpositive ℝ K))) := by
  have h := (seriesGerms K).isTruncationClosed_adjoin_insert
    (seriesGerms_isTruncationClosed_iff.mpr hR) X (by simpa using hX)
  exact seriesGerms_isTruncationClosed_iff.mp h

omit [CharZero K] in
/-- If the germ of `X` is transcendental over `S`, then `X` is transcendental over every
subalgebra, over the series with constant germs, of series all of whose germs lie in `S`. -/
@[blueprint "lem:transcendental-series"
  (phase := "Polynomial presentations")
  (title := "Transcendence of a series with transcendental germ")
  (statement := /--
    Let $G=\mathbb R$. Let $S\subseteq Q$ be a $K$-subalgebra, $E_0\subseteq A(S)$ an
    $A(K)$-subalgebra of $A$, and $X\in A$ with $[X]$ transcendental over $S$. Then $X$ is
    transcendental over $E_0$.
  -/)
  (proof := /--
    Let $\sum_kc_kX^k=0$ with $c_k\in E_0$ not all $0$. By \ref{lem:nonzero-germs}, each nonzero
    $c_k$ has a greatest exponent at which its germ is nonzero, namely the greatest element of its
    closed support. Let $\eta$ be the largest of these exponents. No $c_k$ has a nonzero germ above
    $\eta$. So in the convolution formula \ref{lem:convolution-formula}, a finite sum by
    \ref{lem:convolution-finite}, for the germ of $c_kX^k$ at $\eta$, the terms at $\beta>\eta$
    vanish, and so do those at $\beta<\eta$, where $X^k$ has exponent $\eta-\beta>0$. Hence
    $[(c_kX^k)^{|\eta}]=[c_k^{|\eta}]\,[X]^k$, and
    \[
      \textstyle\sum_k[c_k^{|\eta}]\,[X]^k=0.
    \]
    The coefficients lie in $S$ because $c_k\in A(S)$, and they are not all $0$ by the choice of
    $\eta$. This contradicts the transcendence of $[X]$ over $S$.
  -/)]
theorem transcendental_of_transcendental_mk
    {S : Subalgebra K (Nonpositive ℝ K ⧸ boundedAwayIdeal ℝ K)}
    {R₀ : Subalgebra (seriesGerms K).seriesWithConstantGerms (Nonpositive ℝ K)}
    (hsub : (R₀ : Set (Nonpositive ℝ K)) ⊆ (seriesGerms K).seriesWithGermsIn S)
    {X : Nonpositive ℝ K} (htr : Transcendental S (Ideal.Quotient.mk (boundedAwayIdeal ℝ K) X)) :
    Transcendental R₀ X :=
  (seriesGerms K).transcendental_of_transcendental_germ hsub (by simpa using htr)

omit [CharZero K] in
/-- A subalgebra closed under the truncations `b ↦ b_{|η}`, containing the series with constant
germs and representatives of every element of `S`, contains every series all of whose germs lie
in `S`. -/
@[blueprint "lem:series-generation"
  (phase := "Polynomial presentations")
  (title := "Generation by truncations and representatives")
  (statement := /--
    Let $G=\mathbb R$. Let $S\subseteq Q$ be a $K$-subalgebra, and $E\subseteq A$ a $K$-subalgebra
    that is closed under truncation, contains $A(K)$, and satisfies $S\subseteq[E]$. Then
    $A(S)\subseteq E$.
  -/)
  (proof := /--
    Let $b\in A(S)$ be nonzero, and let $D$ be the set of exponents at which $b$ has a nonzero germ.
    By \ref{lem:nonzero-germs}, $D$ is the closed support of $b$, so it is well ordered, has a
    greatest element, and every nonempty $D\cap(-\infty,\varepsilon]$ has a greatest element; also
    $b=b_{|\max D}$. We show $b_{|\eta}\in E$ for $\eta\in D$ by induction on $\eta$.

    Let $\eta\in D$. As $[b^{|\eta}]\in S\subseteq[E]$, choose $r\in E$ with $[r]=[b^{|\eta}]$, and
    put $c=t^\eta r$. By \ref{lem:convolution-formula}, whose sum is finite by
    \ref{lem:convolution-finite}, the germ of $t^\eta e$ at $\xi$ is the germ of $e$ at $\xi-\eta$,
    for every $e\in A$; with $e=1$ this shows $t^\eta\in A(K)\subseteq E$, so $c\in E$. The germ of
    $c$ at $\xi$ is the germ of $r$ at $\xi-\eta$; so $c$ has no nonzero germ above $\eta$, and
    $[c^{|\eta}]=[r]=[b^{|\eta}]$.

    Hence $u=b_{|\eta}-c$ has no nonzero germ above $\eta$, and $[u^{|\eta}]=0$. By
    \ref{lem:constant-germs} the germs of $u$ vanish on some interval $(\varepsilon,\eta]$. Two
    series with the same germs are equal (\ref{lem:nonzero-germs}), so
    $u=u_{|\varepsilon}=b_{|\varepsilon}-c_{|\varepsilon}$. Here $c_{|\varepsilon}\in E$, as $E$ is
    closed under truncation; and $b_{|\varepsilon}$ is $0$ or $b_{|\zeta}$ for the greatest
    $\zeta\in D$ with $\zeta\le\varepsilon$, which lies in $E$ by induction. So
    $b_{|\eta}=c+u\in E$.
  -/)]
theorem seriesWithGermsIn_le {S : Subalgebra K (Nonpositive ℝ K ⧸ boundedAwayIdeal ℝ K)}
    {R : Subalgebra K (Nonpositive ℝ K)} (hR : ∀ b ∈ R, ∀ η : ℝ, truncation η b ∈ R)
    (hBR : (seriesGerms K).seriesWithConstantGerms ≤ R)
    (hlift : ∀ a ∈ S, ∃ r ∈ R, Ideal.Quotient.mk (boundedAwayIdeal ℝ K) r = a) :
    (seriesGerms K).seriesWithGermsIn S ≤ R :=
  (seriesTruncationGerms K).seriesWithGermsIn_le (seriesGerms_isTruncationClosed_iff.mpr hR)
    hBR (by simpa using hlift)

/-- The nonpositive real series ring over a field of characteristic zero is a polynomial ring
over its finite-support subring `K(ℝ^{≤0})`. -/
@[blueprint "thm:hahn-series-polynomial-algebra"
  (phase := "Polynomial presentations")
  (title := "Polynomial presentation of $K((\\mathbb R^{\\le 0}))$")
  (statement := /--
    Let $G=\mathbb R$ and let $K$ have characteristic $0$. For some set $I$ there is a
    $K(\mathbb R^{\le0})$-algebra isomorphism
    \[
      K(\mathbb R^{\le0})[Y_i:i\in I]\simeq K((\mathbb R^{\le0})).
    \]
  -/)
  (proof := /--
    By \ref{lem:constant-germs-finite-support}, $A(K)=K(\mathbb R^{\le0})$. By Zorn's lemma choose a
    set $\mathcal X\subseteq A$, algebraically independent over $A(K)$, that is maximal such that
    $E=A(K)[\mathcal X]$ is closed under truncation and $E\subseteq A(S)$, where
    $S=K[\{[X]:X\in\mathcal X\}]$. The empty set qualifies, and so does the union of a chain. Every
    element of $S$ is the class of a polynomial over $K$ in the elements of $\mathcal X$, which lies
    in $E$; so $S\subseteq[E]$, and \ref{lem:series-generation} gives $E=A(S)$. In particular
    $S\subseteq[A(S)]$.

    Suppose that $S\ne Q$. By \ref{lem:new-germ} with $P=Q$, there is $X\in A$ whose germs at
    negative exponents lie in $S$, with $x=[X]\notin S$. Completeness of $\mathbb R$ gives (H).
    Thus $x$ is transcendental over $S$ by \ref{lem:transcendence}. Applying
    \ref{lem:transcendental-series} with $E_0=E$ gives transcendence of $X$ over $E$.
    For $\zeta<0$ all germs of $X_{|\zeta}$
    lie in $S$, so $X_{|\zeta}\in A(S)=E$. By \ref{lem:truncations-of-simple-extension} $E[X]$
    is closed under truncation. By \ref{lem:convolution-formula} the series with germs in $S[x]$
    form a subalgebra containing $E$ and $X$. Hence $E[X]\subseteq A(S[x])$, and
    $\mathcal X\cup\{X\}$ contradicts the maximality of $\mathcal X$.

    Hence $S=Q$ and $E=A(Q)=A$, and evaluation at $\mathcal X$ is an isomorphism
    $A(K)[Y_X:X\in\mathcal X]\simeq A$ of $A(K)$-algebras.
  -/)
  (highlight)]
theorem exists_mvPolynomial_algEquiv_finiteSupportRing :
    ∃ ι : Type (max v w), Nonempty (MvPolynomial ι (FiniteSupportRing (G := ℝ) (K := K)) ≃ₐ[
      FiniteSupportRing (G := ℝ) (K := K)] Nonpositive ℝ K) := by
  set B := (seriesGerms K).seriesWithConstantGerms
  obtain ⟨𝒳, hind, htop⟩ :=
    (seriesGerms K).exists_algebraicIndependent_series_generators
      (fun S hS ↦ by simpa using exists_germAt_mem_mk_notMem S hS)
      (fun S hS X hX hx ↦ by
        simp only [GermMaps.HasRepresentativesWithGermsIn, seriesGerms_germ,
          seriesGerms_germAt] at hS hX hx ⊢
        exact transcendental_mk_of_germAt_mem S hS X hX hx)
      (fun R hR X hX ↦ seriesGerms_isTruncationClosed_iff.mpr
        (truncation_mem_adjoin_insert (seriesGerms_isTruncationClosed_iff.mp hR) X
          (by simpa using hX)))
      (fun _ _ hsub _ htr ↦ transcendental_of_transcendental_mk hsub (by simpa using htr))
      (fun _ _ hR hBR hlift ↦ seriesWithGermsIn_le (seriesGerms_isTruncationClosed_iff.mp hR)
        hBR (by simpa using hlift))
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
