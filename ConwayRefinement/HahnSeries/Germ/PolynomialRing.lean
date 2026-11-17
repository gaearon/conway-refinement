/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import ConwayRefinement.Blueprint
public import ConwayRefinement.HahnSeries.Germ.GermAt
public import ConwayRefinement.RingTheory.TruncationGerms.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Algebraic.Defs
import ConwayRefinement.HahnSeries.Germ.GermSupport
import ConwayRefinement.RingTheory.TruncationGerms.Transcendence

/-!
# The ring of germs is a polynomial ring

Let `G` be a nontrivial ordered abelian group whose additive uniformity is Cauchy complete, `K` a
field of characteristic zero, and `J` the ideal of series in `K((G^{≤0}))` whose support is bounded
away from zero. The germs `germAt γ` of nonpositive series satisfy the axioms of `TruncationGerms`,
with the Cantor--Bendixson value of a representative as the rank of a germ. This gives the
transcendence lemma for germs of series (`transcendental_mk_of_germAt_mem`), and a Zorn argument
based on it shows that the ring of germs `K((G^{≤0}))/J` is a polynomial ring over `K`; in
particular `J` is prime.
-/

open Set
open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

/-- The Cantor--Bendixson value of a representative, as the rank of a germ. -/
private def germRank (g : Nonpositive G K ⧸ boundedAwayIdeal G K) : Ordinal.{u} :=
  ((Ideal.Quotient.mk_surjective g).choose : HahnSeries G K).cantorBendixsonValue

omit [IsUniformAddGroup G] [CompleteSpace G] [CharZero K] in
private theorem germRank_mk (b : Nonpositive G K) :
    germRank (Ideal.Quotient.mk (boundedAwayIdeal G K) b) =
      (b : HahnSeries G K).cantorBendixsonValue :=
  cantorBendixsonValue_eq_of_sub_mem (Ideal.Quotient.eq.mp
    (Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (boundedAwayIdeal G K) b)).choose_spec)

variable (G K) in
/-- The germ maps `germAt γ` of nonpositive series, with values in the ring of germs
`K((G^{≤0}))/J`. -/
def germMaps : GermMaps K G (Nonpositive G K) (Nonpositive G K ⧸ boundedAwayIdeal G K) where
  germAt := germAt
  germ := Ideal.Quotient.mkₐ K _
  germ_surjective := Ideal.Quotient.mkₐ_surjective K _
  germAt_zero := germAt_zero
  germAt_of_pos b _ hξ := germAt_of_pos b hξ
  germAt_algebraMap k _ hξ := germAt_algebraMap k hξ

omit [CompleteSpace G] [CharZero K] in
@[simp]
theorem germMaps_germAt (γ : G) : (germMaps G K).germAt γ = germAt γ := (rfl)

omit [CompleteSpace G] [CharZero K] in
@[simp]
theorem germMaps_germ (b : Nonpositive G K) :
    (germMaps G K).germ b = Ideal.Quotient.mk (boundedAwayIdeal G K) b := (rfl)

variable (G K) in
/-- The germ maps of nonpositive series satisfy the convolution formula. -/
def convolutionGerms : ConvolutionGerms K G (Nonpositive G K)
    (Nonpositive G K ⧸ boundedAwayIdeal G K) where
  __ := germMaps G K
  convolution_finite := finite_germAt_ne_zero_and_germAt_ne_zero
  convolution := germAt_mul

omit [CharZero K] in
@[simp]
theorem convolutionGerms_germAt (γ : G) : (convolutionGerms G K).germAt γ = germAt γ := (rfl)

omit [CharZero K] in
@[simp]
theorem convolutionGerms_germ (b : Nonpositive G K) :
    (convolutionGerms G K).germ b = Ideal.Quotient.mk (boundedAwayIdeal G K) b := (rfl)

variable (G K) in
/-- The germ maps of nonpositive series, with translated truncations and the characterisation of
constant germs. -/
def constantGerms :
    ConstantGerms K G (Nonpositive G K) (Nonpositive G K ⧸ boundedAwayIdeal G K) where
  __ := germMaps G K
  exists_translatedTruncation b ξ _ :=
    ⟨translatedTruncation ξ b, fun _ hζ => germAt_translatedTruncation b ξ hζ⟩
  germAt_eventually_eq_zero b hb := by
    simpa using (germAt_mem_range_algebraMap_iff b 0).mp (by simpa using hb)
  germ_mem_range_of_eventually b hb := by
    simpa using (germAt_mem_range_algebraMap_iff b 0).mpr (by simpa using hb)

omit [CompleteSpace G] [CharZero K] in
@[simp]
theorem constantGerms_germAt (γ : G) : (constantGerms G K).germAt γ = germAt γ := (rfl)

omit [CompleteSpace G] [CharZero K] in
@[simp]
theorem constantGerms_germ (b : Nonpositive G K) :
    (constantGerms G K).germ b = Ideal.Quotient.mk (boundedAwayIdeal G K) b := (rfl)

variable (G K) in
/-- The germ maps of nonpositive series, with cutoffs and the Cantor--Bendixson value of a
representative as the rank of a germ. -/
def rankedGerms : RankedGerms K G (Nonpositive G K) (Nonpositive G K ⧸ boundedAwayIdeal G K) where
  __ := germMaps G K
  rank := germRank
  rank_germAt_lt b hb := by
    have hvne : (b : HahnSeries G K).cantorBendixsonValue ≠ 0 := fun h =>
      hb ⟨0, by rw [map_zero]; exact
        ((mk_eq_zero_iff_cantorBendixsonValue_eq_zero b).mpr h).symm⟩
    obtain ⟨ε, hε, hdrop⟩ := cantorBendixsonValue_translatedTruncation_lt b hvne
    refine ⟨ε, hε, fun ξ hεξ hξ => ?_⟩
    change germRank (germAt ξ b) < germRank (Ideal.Quotient.mk _ b)
    rw [germAt_apply, germRank_mk, germRank_mk]
    exact hdrop ξ hεξ hξ
  exists_cutoff _ _ hε := (exists_germAt_cutoff _ hε).imp fun _ h ↦ ⟨h.1, h.2.1, h.2.2.1⟩

omit [CompleteSpace G] [CharZero K] in
@[simp]
theorem rankedGerms_germAt (γ : G) : (rankedGerms G K).germAt γ = germAt γ := (rfl)

omit [CompleteSpace G] [CharZero K] in
@[simp]
theorem rankedGerms_germ (b : Nonpositive G K) :
    (rankedGerms G K).germ b = Ideal.Quotient.mk (boundedAwayIdeal G K) b := (rfl)

variable (G K) in
/-- The germs `germAt γ` of nonpositive series at exponents `γ ∈ G` satisfy the axioms of
`TruncationGerms` on `K((G^{≤0}))`, with values in the ring of germs `K((G^{≤0}))/J`. -/
def truncationGerms : TruncationGerms K G (Nonpositive G K)
    (Nonpositive G K ⧸ boundedAwayIdeal G K) :=
  { convolutionGerms G K, constantGerms G K, rankedGerms G K with }

omit [CharZero K] in
@[simp]
theorem truncationGerms_germAt (γ : G) :
    (truncationGerms G K).germAt γ = germAt γ := (rfl)

omit [CharZero K] in
@[simp]
theorem truncationGerms_germ (b : Nonpositive G K) :
    (truncationGerms G K).germ b =
      Ideal.Quotient.mk (boundedAwayIdeal G K) b := (rfl)

omit [CharZero K] in
/-- **No linear relations.** Let `S` be a `K`-subalgebra of the ring of germs `K((G^{≤0}))/J` such
that every element of `S` is the germ of a series all of whose germs lie in `S`. Let `X` be a
series whose germs at negative exponents lie in `S` but whose germ does not. Then no nonzero
element of `S` multiplies the germ of `X` into `S`. -/
@[blueprint "lem:no-linear-relation"
  (phase := "Polynomial presentations")
  (title := "Absence of linear relations")
  (statement := /--
    Assume (H) and $x\notin S$.  Then $ax\notin S$ for every nonzero $a\in S$.
  -/)
  (proof := /--
    Suppose otherwise, and choose such an $a$ with $V_{\mathrm{CB}}(a)$ least; by
    \ref{lem:cantor-bendixson-value-class}, $V_{\mathrm{CB}}$ is defined on classes. Choose
    $P,W\in A(S)$ with $[P]=a$ and $[W]=-ax$. Then $[PX+W]=0$, so by \ref{lem:constant-germs} the
    germs of $PX+W$ vanish at all $\xi$ in some interval $(\varepsilon,0)$.

    Let $\xi\in(\varepsilon,0)$. By \ref{lem:convolution-formula}, a finite sum by
    \ref{lem:convolution-finite}, $[(PX)^{|\xi}]-[P^{|\xi}]\,x$ is the sum of the products
    $[P^{|\beta}]\,[X^{|\xi-\beta}]$ with $\beta\ne\xi$. Such a product vanishes if $\xi-\beta>0$,
    since germs at positive exponents vanish. It lies in $S$ if $\xi-\beta<0$, because $P\in A(S)$
    and the germs of $X$ at negative exponents lie in $S$. Since $[(PX)^{|\xi}]=-[W^{|\xi}]\in S$,
    it follows that $[P^{|\xi}]\,x\in S$; also $[P^{|\xi}]\in S$.

    If $a\in K$, then $x=a^{-1}(ax)\in S$, a contradiction. If $a\notin K$, then $a\ne0$, so
    $V_{\mathrm{CB}}(P)\ne0$, and \ref{lem:cantor-bendixson-value-drop} gives
    $V_{\mathrm{CB}}([P^{|\xi}])<V_{\mathrm{CB}}(a)$ for all $\xi<0$ close to $0$. These germs lie
    in $S$ and satisfy $[P^{|\xi}]\,x\in S$, so by the minimality of $V_{\mathrm{CB}}(a)$ they
    vanish. Then $a\in K$ by \ref{lem:constant-germs}, a contradiction.
  -/)]
theorem mul_mk_notMem
    (S : Subalgebra K (Nonpositive G K ⧸ boundedAwayIdeal G K))
    (hS : ∀ a ∈ S, ∃ b : Nonpositive G K,
      Ideal.Quotient.mk (boundedAwayIdeal G K) b = a ∧ ∀ ξ, germAt ξ b ∈ S)
    (X : Nonpositive G K) (hX : ∀ ξ < 0, germAt ξ X ∈ S)
    (hx : Ideal.Quotient.mk (boundedAwayIdeal G K) X ∉ S)
    {a : Nonpositive G K ⧸ boundedAwayIdeal G K} (ha : a ∈ S) (ha0 : a ≠ 0) :
    a * Ideal.Quotient.mk (boundedAwayIdeal G K) X ∉ S :=
  (truncationGerms G K).mul_germ_notMem S hS X hX hx a ha ha0

omit [CharZero K] in
/-- **Proportionality.** Let `S` be a `K`-subalgebra of the ring of germs that is an integral
domain and such that every element of `S` is the germ of a series all of whose germs lie in `S`.
Let `X` be a series whose germs at negative exponents lie in `S` but whose germ `x` does not. Let
`V` be a series with nonzero germ whose germs at nonpositive exponents lie in `S`, and `U` a series
whose germs at nonpositive exponents lie in `S + S x`. If the germs of `U` and `V` on a left
neighbourhood of `0` are in the ratio of the germs of `U` and `V`, then the germ of `U` is a
constant multiple of the germ of `V`. -/
@[blueprint "lem:proportionality"
  (phase := "Polynomial presentations")
  (title := "Proportional germs")
  (statement := /--
    Assume (H), $x\notin S$, and that $S$ is a domain.  Let $U,V\in A$ with
    $[V]\ne0$, $[V^{|\xi}]\in S$ and $[U^{|\xi}]\in S+Sx$ for all $\xi\le0$, and
    \[
      [V]\,[U^{|\xi}]=[U]\,[V^{|\xi}]\qquad\text{for all }\xi\text{ in some }
      (\varepsilon,0).
    \]
    Then $[U]=c\,[V]$ for some $c\in K$.
  -/)
  (proof := /--
    A nonzero $v\in S$ cancels from an equation $vn=vn'$ with $n,n'\in S+Sx$. Indeed, write
    $n-n'=s_0+s_1x$ with $s_0,s_1\in S$; then $(vs_1)x=-vs_0\in S$, so $vs_1=0$ by
    \ref{lem:no-linear-relation}, and then $vs_0=0$. As $S$ is a domain, $s_0=s_1=0$.

    Induct on $V_{\mathrm{CB}}([V])$. Suppose first that $[V]\in K$. By \ref{lem:constant-germs} the
    germs of $V$ vanish near $0$, so the relation makes the germs of $U$ vanish near $0$, as
    $[V]\ne0$. By \ref{lem:constant-germs} again $[U]\in K$, and $c=[U]/[V]$.

    Suppose that $[V]\notin K$. Since $[V]\ne0$, $V_{\mathrm{CB}}(V)\ne0$. By
    \ref{lem:constant-germs} and \ref{lem:cantor-bendixson-value-drop} there is
    $\xi\in(\varepsilon,0)$ with $[V^{|\xi}]\ne0$ and
    $V_{\mathrm{CB}}([V^{|\xi}])<V_{\mathrm{CB}}([V])$. Put $U'=U^{|\xi}$ and $V'=V^{|\xi}$. By
    \ref{lem:germs-of-translated-truncation} the germs of $U'$ and $V'$ at $\zeta\le0$ are those of
    $U$ and $V$ at $\xi+\zeta$, so $U'$ and $V'$ satisfy the hypotheses on germs. For
    $\zeta\in(\varepsilon-\xi,0)$, the relations at $\xi+\zeta$ and at $\xi$ give
    \[
      [V]\,[V']\,[U'^{|\zeta}]=[V']\,[U]\,[V'^{|\zeta}]=[V]\,[U']\,[V'^{|\zeta}].
    \]
    Both sides are $[V]$ times an element of $S+Sx$, so cancelling $[V]$ gives
    $[V']\,[U'^{|\zeta}]=[U']\,[V'^{|\zeta}]$. By induction $[U']=c\,[V']$ for some $c\in K$. The
    relation at $\xi$ now reads $[V']\,[U]=[V]\,[U']=[V']\,c\,[V]$, and cancelling $[V']\ne0$ gives
    $[U]=c\,[V]$.
  -/)]
theorem exists_mk_eq_smul_of_proportional
    (S : Subalgebra K (Nonpositive G K ⧸ boundedAwayIdeal G K)) [IsDomain S]
    (hS : ∀ a ∈ S, ∃ b : Nonpositive G K,
      Ideal.Quotient.mk (boundedAwayIdeal G K) b = a ∧ ∀ ξ, germAt ξ b ∈ S)
    (X : Nonpositive G K) (hX : ∀ ξ < 0, germAt ξ X ∈ S)
    (hx : Ideal.Quotient.mk (boundedAwayIdeal G K) X ∉ S)
    (U V : Nonpositive G K) (hV : Ideal.Quotient.mk (boundedAwayIdeal G K) V ≠ 0)
    (hVS : ∀ ξ ≤ 0, germAt ξ V ∈ S)
    (hUN : ∀ ξ ≤ 0, ∃ s₀ ∈ S, ∃ s₁ ∈ S,
      germAt ξ U = s₀ + s₁ * Ideal.Quotient.mk (boundedAwayIdeal G K) X)
    (h : ∃ ε < 0, ∀ ξ, ε < ξ → ξ < 0 →
      Ideal.Quotient.mk (boundedAwayIdeal G K) V * germAt ξ U =
        Ideal.Quotient.mk (boundedAwayIdeal G K) U * germAt ξ V) :
    ∃ c : K, Ideal.Quotient.mk (boundedAwayIdeal G K) U =
      c • Ideal.Quotient.mk (boundedAwayIdeal G K) V :=
  (truncationGerms G K).exists_germ_eq_smul_of_proportional S
    (fun _ ha ha0 ↦ mul_mk_notMem S hS X hX hx ha ha0) U V hV hVS hUN h

/-- **Transcendence lemma.** Let `S` be a `K`-subalgebra of the ring of germs `K((G^{≤0}))/J`
that is an integral domain and such that every element of `S` is the germ of a series all of whose
germs lie in `S`. Let `X` be a series whose germs at negative exponents lie in `S` but whose germ
does not. Then the germ of `X` is transcendental over `S`. -/
@[blueprint "lem:transcendence"
  (phase := "Polynomial presentations")
  (title := "Transcendence lemma")
  (statement := /--
    Let $K$ have characteristic $0$. Assume (H), $x\notin S$, and that $S$ is a domain. Then $x$ is
    transcendental over $S$.
  -/)
  (proof := /--
    Let $p\in S[Y]$ be nonzero of least degree $d$ with $p(x)=0$. Then $d\ge1$, and $d=1$ is
    excluded by \ref{lem:no-linear-relation}. Let $d\ge2$. Lift each coefficient $p_k$ to some
    $P_k\in A(S)$, and put $W=\sum_kP_kX^k$. Then $[W]=p(x)=0$, so by \ref{lem:constant-germs}
    $[W^{|\xi}]=0$ for all $\xi$ in some interval $(\varepsilon,0)$.

    Fix $\xi\le0$. Expanding $[(P_kX^k)^{|\xi}]$ by \ref{lem:convolution-formula} and inducting on
    $k$, as in the proof of \ref{lem:no-linear-relation}, gives $[(P_kX^k)^{|\xi}]=q_k(x)$ for a
    polynomial $q_k\in S[Y]$ of degree at most $k$ whose coefficient of $Y^k$ is $[P_k^{|\xi}]$ and
    whose coefficient of $Y^{k-1}$ is $k\,([(P_kX)^{|\xi}]-[P_k^{|\xi}]\,x)$. Put $q=\sum_kq_k$, so
    that $q(x)=[W^{|\xi}]$.

    Let $\xi\in(\varepsilon,0)$. The polynomial $p_d\,q-[P_d^{|\xi}]\,p$ vanishes at $x$ and has
    degree less than $d$, so it is $0$. Its coefficient of $Y^{d-1}$ says that $U=dP_dX+P_{d-1}$
    satisfies
    \[
      [P_d]\,[U^{|\xi}]=[U]\,[P_d^{|\xi}].
    \]
    The germs of $P_d$ lie in $S$, and by the computation in the second paragraph those of $U$ lie
    in $S+Sx$. So \ref{lem:proportionality}, with $V=P_d$ and $[V]=p_d\ne0$, gives $[U]=c\,p_d$ for
    some $c\in K$, that is, $d\,p_d\,x+p_{d-1}-c\,p_d=0$. As $K$ has characteristic $0$,
    $d\,p_d\ne0$, and this relation of degree one contradicts the minimality of $d$.
  -/)
  (highlight)]
theorem transcendental_mk_of_germAt_mem
    (S : Subalgebra K (Nonpositive G K ⧸ boundedAwayIdeal G K)) [IsDomain S]
    (hS : ∀ a ∈ S, ∃ b : Nonpositive G K,
      Ideal.Quotient.mk (boundedAwayIdeal G K) b = a ∧ ∀ ξ, germAt ξ b ∈ S)
    (X : Nonpositive G K) (hX : ∀ ξ < 0, germAt ξ X ∈ S)
    (hx : Ideal.Quotient.mk (boundedAwayIdeal G K) X ∉ S) :
    Transcendental S (Ideal.Quotient.mk (boundedAwayIdeal G K) X) :=
  (truncationGerms G K).transcendental_germ S hS X hX
    (fun _ ha ha0 ↦ mul_mk_notMem S hS X hX hx ha ha0)
    (exists_mk_eq_smul_of_proportional S hS X hX hx)

omit [CharZero K] in
/-- Adjoining to `S` the germ of a series whose germs at negative exponents lie in `S` preserves the
property that every element is the germ of a series all of whose germs lie in the subalgebra. -/
@[blueprint "lem:representatives-adjoin"
  (phase := "Polynomial presentations")
  (title := "Representatives after adjoining a germ")
  (statement := /--
    Assume (H). Then $S[x]\subseteq[A(S[x])]$.
  -/)
  (proof := /--
    Let $\mathcal T$ be the set of $a\in S[x]$ with $a=[b]$ for some $b\in A(S[x])$. It contains
    $S$, since $S\subseteq[A(S)]\subseteq[A(S[x])]$. It contains $x=[X]$: the germs of $X$ at
    $\xi<0$ lie in $S$, the germ at $0$ is $x$, and the germs at $\xi>0$ vanish. It is closed under
    sums, as the germ maps are linear. It is closed under products by \ref{lem:convolution-formula}:
    if all germs of $b$ and $c$ lie in $S[x]$, then so does each
    $[(bc)^{|\gamma}]=\sum_\beta[b^{|\beta}]\,[c^{|\gamma-\beta}]$, a finite sum by
    \ref{lem:convolution-finite}. Hence $\mathcal T=S[x]$.
  -/)]
theorem exists_mk_eq_of_mem_adjoin
    (S : Subalgebra K (Nonpositive G K ⧸ boundedAwayIdeal G K))
    (hS : ∀ a ∈ S, ∃ b : Nonpositive G K,
      Ideal.Quotient.mk (boundedAwayIdeal G K) b = a ∧ ∀ ξ, germAt ξ b ∈ S)
    (X : Nonpositive G K) (hX : ∀ ξ < 0, germAt ξ X ∈ S) :
    ∀ a ∈ Algebra.adjoin K (insert (Ideal.Quotient.mk (boundedAwayIdeal G K) X) (S : Set _)),
      ∃ b : Nonpositive G K, Ideal.Quotient.mk (boundedAwayIdeal G K) b = a ∧
        ∀ ξ, germAt ξ b ∈
          Algebra.adjoin K (insert (Ideal.Quotient.mk (boundedAwayIdeal G K) X) (S : Set _)) :=
  (convolutionGerms G K).hasRepresentativesWithGermsIn_adjoin S hS X hX

omit [CompleteSpace G] [CharZero K] in
/-- A proper `K`-subalgebra `S` of the ring of germs misses the germ of a series whose germs at
negative exponents lie in `S`. -/
@[blueprint "lem:new-germ"
  (phase := "Polynomial presentations")
  (title := "Existence of a new germ")
  (statement := /--
    Let $S\subsetneq Q$ be a $K$-subalgebra.  Then there is $X\in A$ with
    $[X^{|\xi}]\in S$ for all $\xi<0$ and $[X]\notin S$.
  -/)
  (proof := /--
    Choose $y\in Q\setminus S$ with $V_{\mathrm{CB}}(y)$ least
    (\ref{lem:cantor-bendixson-value-class}), and $X_0\in A$ with $[X_0]=y$. Since $K\subseteq S$,
    $y\notin K$; in particular $y\ne0$ and $V_{\mathrm{CB}}(X_0)\ne0$. By
    \ref{lem:cantor-bendixson-value-drop} there is $\varepsilon<0$ with
    $V_{\mathrm{CB}}([X_0^{|\xi}])<V_{\mathrm{CB}}(y)$ for all $\xi\in(\varepsilon,0)$; by the
    choice of $y$, these germs lie in $S$.

    Let $X$ be the part of $X_0$ with exponents greater than $\varepsilon$. Then $X_0-X\in J$, so
    $[X]=y\notin S$. For $\xi\in(\varepsilon,0)$, the series $X^{|\xi}$ and $X_0^{|\xi}$ differ by a
    series supported in $(-\infty,\varepsilon-\xi]$, so they have the same germ, which lies in $S$.
    For $\xi\le\varepsilon$, the translated truncation $X^{|\xi}$ is $0$, so the germ of $X$ at
    $\xi$ (\ref{def:germ-at}) is $0$.
  -/)]
theorem exists_germAt_mem_mk_notMem
    (S : Subalgebra K (Nonpositive G K ⧸ boundedAwayIdeal G K)) (hS : S ≠ ⊤) :
    ∃ X : Nonpositive G K, (∀ ξ < 0, germAt ξ X ∈ S) ∧
      Ideal.Quotient.mk (boundedAwayIdeal G K) X ∉ S :=
  (rankedGerms G K).exists_germAt_mem_germ_notMem S hS

/-- For a nontrivial ordered exponent group `G` that is Cauchy complete and a field `K` of
characteristic zero, the quotient of `K((G^{≤0}))` by the ideal of series whose support is
bounded away from zero is a polynomial algebra over `K`. -/
@[blueprint "thm:complete-hahn-germ-polynomial-algebra"
  (phase := "Polynomial presentations")
  (title := "Polynomial presentation of the ring of germs")
  (statement := /--
    Let $K$ have characteristic $0$ and $G$ be Cauchy complete. For some set $I$ there is a
    $K$-algebra isomorphism
    \[
      K[Y_i:i\in I]\simeq Q.
    \]
  -/)
  (proof := /--
    By Zorn's lemma choose a set $\mathcal T\subseteq Q$, algebraically independent over $K$, that
    is maximal with $K[\mathcal T]\subseteq[A(K[\mathcal T])]$. The empty set qualifies, because a
    constant $k$ has $[k^{|\xi}]=0$ for $\xi\ne0$. The union of a chain qualifies, since each
    element of its polynomial ring lies in the polynomial ring of one member of the chain. As a
    polynomial ring over $K$, $K[\mathcal T]$ is a domain.

    Suppose that $K[\mathcal T]\ne Q$. By \ref{lem:new-germ} there is $X\in A$ whose germs at
    negative exponents lie in $K[\mathcal T]$, with $x=[X]\notin K[\mathcal T]$. Then (H) holds with
    $S=K[\mathcal T]$, and by \ref{lem:transcendence}, $x$ is transcendental over $K[\mathcal T]$;
    so $\mathcal T\cup\{x\}$ is algebraically independent. By \ref{lem:representatives-adjoin},
    $K[\mathcal T\cup\{x\}]=K[\mathcal T][x]$ again satisfies the condition. This contradicts the
    maximality of $\mathcal T$. Hence $K[\mathcal T]=Q$, and evaluation at $\mathcal T$ is an
    isomorphism $K[Y_\tau:\tau\in\mathcal T]\simeq Q$.
  -/)
  (highlight)]
theorem exists_mvPolynomial_algEquiv_germ :
    ∃ ι : Type (max (u + 1) v), Nonempty
      (MvPolynomial ι K ≃ₐ[K]
        Nonpositive G K ⧸ boundedAwayIdeal G K) := by
  obtain ⟨T, hind, htop⟩ := exists_algebraicIndependent_adjoin_eq_top
    (germMaps G K).HasRepresentativesWithGermsIn
    (germMaps G K).hasRepresentativesWithGermsIn_bot
    (fun _ hcn hchain hc ↦
      (germMaps G K).hasRepresentativesWithGermsIn_adjoin_sUnion hcn hchain hc)
    fun S _ hS hne ↦ by
      obtain ⟨X, hX, hx⟩ := exists_germAt_mem_mk_notMem S hne
      exact ⟨_, transcendental_mk_of_germAt_mem S hS X hX hx,
        exists_mk_eq_of_mem_adjoin S hS X hX⟩
  exact ⟨ULift.{u + 1} T, ⟨(MvPolynomial.renameEquiv K Equiv.ulift).trans
    (hind.mvPolynomialAlgEquivOfAdjoinEqTop htop)⟩⟩

variable (G K) in
/-- For a nontrivial ordered exponent group `G` that is Cauchy complete and a field `K` of
characteristic zero, the ideal `J` of series in `K((G^{≤0}))` whose support is bounded away from
zero is prime: the ring of germs `K((G^{≤0}))/J` is an integral domain. For real exponents this is
Berarducci's theorem (Berarducci 2000, Corollary 9.8); for dense exponent groups it is due to
Pitteloud (2002, Theorem 6.1), and for arbitrary exponent groups to L'Innocente–Mantova (2024,
Corollary 8.1.5). Here it is a consequence of the polynomial presentation. -/
@[blueprint "thm:bounded-away-ideal-prime"
  (phase := "Polynomial presentations")
  (title := "Primality of $J$")
  (statement := /--
    Let $K$ have characteristic $0$ and $G$ be Cauchy complete. Then $Q$ is a domain; that is, $J$
    is a prime ideal. This is a special case of known results: [Ber00, Cor. 9.8] for $G=\mathbb R$,
    [Pit02, Thm. 6.1] for dense $G$, and [LM24, Cor. 8.1.5] for arbitrary $G$. It is recorded here
    as a corollary of the polynomial presentation.
  -/)
  (proof := /--
    By \ref{thm:complete-hahn-germ-polynomial-algebra}, $Q$ is isomorphic to a polynomial ring over
    the field $K$, which is a domain.
  -/)
  (highlight)]
theorem isDomain_germ : IsDomain (Nonpositive G K ⧸ boundedAwayIdeal G K) := by
  obtain ⟨ι, ⟨e⟩⟩ := exists_mvPolynomial_algEquiv_germ (G := G) (K := K)
  exact e.symm.toMulEquiv.isDomain _

instance : IsDomain (Nonpositive G K ⧸ boundedAwayIdeal G K) := isDomain_germ G K

instance : (boundedAwayIdeal G K).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

end HahnSeries.Nonpositive
