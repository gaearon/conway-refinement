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
import ConwayRefinement.HahnSeries.Germ.GermSupport
import ConwayRefinement.RingTheory.TruncationGerms.Transcendence

/-!
# The ring of germs is a polynomial ring

Let `G` be a nontrivial ordered abelian group whose additive uniformity is Cauchy complete, `K` a
field of characteristic zero, and `J` the ideal of series in `K((G^{≤0}))` whose support is bounded
away from zero. The germs `germAt γ` of nonpositive series satisfy the axioms of `TruncationGerms`,
with the Cantor--Bendixson value of a representative as the rank of a germ. Hence the ring of
germs `K((G^{≤0}))/J` is a polynomial ring over `K`, and in particular `J` is prime.
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
/-- The germs `germAt γ` of nonpositive series at exponents `γ ∈ G` satisfy the axioms of
`TruncationGerms` on `K((G^{≤0}))`, with values in the ring of germs `K((G^{≤0}))/J`. -/
@[blueprint "prop:hahn-germs-axioms"
  (phase := "Polynomial presentations")
  (title := "The germs of $K((G^{\\le 0}))$ form a system of germs")
  (statement := /--
    Let $K$ be a field of characteristic $0$ and $G$ a nontrivial ordered
    abelian group with its order topology and the associated group uniformity,
    and assume that $G$ is Cauchy complete.  The quotient map
    $K((G^{\le0}))\to K((G^{\le0}))/J$, the germs
    $g_\gamma(b)=[b^{|\gamma}]$ for $\gamma\in G$, and the rank
    $\operatorname{rk}([b])=V_{\mathrm{CB}}(b)$ form a system of germs on
    $K((G^{\le0}))$ with values in $K((G^{\le0}))/J$ in the sense of
    \ref{def:germ-axioms}.
  -/)
  (proof := /--
    We check the axioms of \ref{def:germ-axioms}.  The rank is well defined
    because series congruent modulo $J$ agree near
    $0$, and the Cantor--Bendixson value depends only on the support near $0$.
    Axiom (1) holds because $b^{|0}=b$ and, for $\xi>0$, $b^{|\xi}=t^{-\xi}b$
    has support bounded away from $0$.  Axiom (2) is
    \ref{lem:convolution-formula}.  Axiom (3) holds with $b'=b^{|\xi}$, since
    $(b^{|\xi})^{|\zeta}=b^{|\xi+\zeta}$ for $\zeta\le0$.  Axiom (4) is the case
    $\gamma=0$ of \ref{lem:constant-germs}.  For axiom (5), if $[b]$ is not a
    constant then $b\notin J$, so $V_{\mathrm{CB}}(b)\ne0$, and
    \ref{lem:cantor-bendixson-value-drop} applies because $g_\xi(b)$ is the class
    of $b^{|\xi}$.  Axiom (6) holds because the support of a constant is
    contained in $\{0\}$.  For axiom (7) take for $b'$ the part of $b$ with
    exponents greater than $\varepsilon$.
  -/)]
def truncationGerms : TruncationGerms K G (Nonpositive G K)
    (Nonpositive G K ⧸ boundedAwayIdeal G K) where
  germAt := germAt
  germ := Ideal.Quotient.mkₐ K _
  germ_surjective := Ideal.Quotient.mkₐ_surjective K _
  germAt_zero := germAt_zero
  germAt_of_pos b _ hξ := germAt_of_pos b hξ
  convolution_finite := finite_germAt_ne_zero_and_germAt_ne_zero
  convolution := germAt_mul
  exists_translatedTruncation b ξ _ :=
    ⟨translatedTruncation ξ b, fun _ hζ => germAt_translatedTruncation b ξ hζ⟩
  rank := germRank
  germAt_eventually_eq_zero b hb := by
    simpa using (germAt_mem_range_algebraMap_iff b 0).mp (by simpa using hb)
  germ_mem_range_of_eventually b hb := by
    simpa using (germAt_mem_range_algebraMap_iff b 0).mpr (by simpa using hb)
  rank_germAt_lt b hb := by
    have hvne : (b : HahnSeries G K).cantorBendixsonValue ≠ 0 := fun h =>
      hb ⟨0, by rw [map_zero]; exact
        ((mk_eq_zero_iff_cantorBendixsonValue_eq_zero b).mpr h).symm⟩
    obtain ⟨ε, hε, hdrop⟩ := cantorBendixsonValue_translatedTruncation_lt b hvne
    refine ⟨ε, hε, fun ξ hεξ hξ => ?_⟩
    change germRank (germAt ξ b) < germRank (Ideal.Quotient.mk _ b)
    rw [germAt_apply, germRank_mk, germRank_mk]
    exact hdrop ξ hεξ hξ
  germAt_algebraMap k _ hξ := germAt_algebraMap k hξ
  exists_cutoff _ _ hε := (exists_germAt_cutoff _ hε).imp fun _ h ↦ ⟨h.1, h.2.1, h.2.2.1⟩

@[simp]
theorem truncationGerms_germAt (γ : G) :
    (truncationGerms G K).germAt γ = germAt γ := (rfl)

@[simp]
theorem truncationGerms_germ (b : Nonpositive G K) :
    (truncationGerms G K).germ b =
      Ideal.Quotient.mk (boundedAwayIdeal G K) b := (rfl)

/-- For a nontrivial ordered exponent group `G` that is Cauchy complete and a field `K` of
characteristic zero, the quotient of `K((G^{≤0}))` by the ideal of series whose support is
bounded away from zero is a polynomial algebra over `K`. -/
@[blueprint "thm:complete-hahn-germ-polynomial-algebra"
  (phase := "Polynomial presentations")
  (title := "Polynomial presentation of the ring of germs")
  (statement := /--
    Let $K$ be a field of characteristic zero and let $G$ be a nontrivial
    ordered abelian group which is Cauchy complete for its additive
    uniformity.  If $J$ is the ideal of series in $K((G^{\le 0}))$ whose
    support is bounded away from zero, then for some set $I$ there is a
    $K$-algebra isomorphism
    \[
      K[X_i:i\in I]\simeq K((G^{\le 0}))/J.
    \]
  -/)
  (proof := /--
    By \ref{prop:hahn-germs-axioms}, the germs of $K((G^{\le0}))$ form a system
    of germs with values in $K((G^{\le0}))/J$.  By
    \ref{thm:germ-ring-generators}, $K((G^{\le0}))/J$ has a set $T$ of
    generators that is algebraically independent over $K$, and evaluation at
    $T$ is an isomorphism $K[X_t:t\in T]\simeq K((G^{\le0}))/J$.
  -/)]
theorem exists_mvPolynomial_algEquiv_germ :
    ∃ ι : Type (max (u + 1) v), Nonempty
      (MvPolynomial ι K ≃ₐ[K]
        Nonpositive G K ⧸ boundedAwayIdeal G K) :=
  (truncationGerms G K).exists_mvPolynomial_algEquiv.{_, u + 1}

variable (G K) in
/-- For a nontrivial ordered exponent group `G` that is Cauchy complete and a field `K` of
characteristic zero, the ideal `J` of series in `K((G^{≤0}))` whose support is bounded away from
zero is prime: the ring of germs `K((G^{≤0}))/J` is an integral domain. For real exponents this is
Berarducci's theorem (Berarducci 2000, Corollary 9.8); for general exponent groups it is due to
Pitteloud (2002, Theorem 6.1), see also L'Innocente–Mantova (2024, Corollary 8.1.5). Here it is a
consequence of the polynomial presentation. -/
@[blueprint "thm:bounded-away-ideal-prime"
  (phase := "Polynomial presentations")
  (title := "Primality of $J$")
  (statement := /--
    Let $K$ be a field of characteristic zero and let $G$ be a nontrivial
    ordered abelian group which is Cauchy complete for its additive
    uniformity.  If $J$ is the ideal of series in $K((G^{\le 0}))$ whose
    support is bounded away from zero, then $K((G^{\le 0}))/J$ is an
    integral domain; that is, $J$ is a prime ideal.  For $G=\mathbb R$ this
    is [Ber00, Cor. 9.8]; for general $G$ see [Pit02, Thm. 6.1] and
    [LM24, Cor. 8.1.5].  Here it is a consequence of the polynomial
    presentation.
  -/)
  (proof := /--
    By \ref{thm:complete-hahn-germ-polynomial-algebra}, $K((G^{\le 0}))/J$
    is isomorphic to a polynomial ring over the field $K$, which is an
    integral domain.
  -/)]
theorem isDomain_germ : IsDomain (Nonpositive G K ⧸ boundedAwayIdeal G K) := by
  obtain ⟨ι, ⟨e⟩⟩ := exists_mvPolynomial_algEquiv_germ (G := G) (K := K)
  exact e.symm.toMulEquiv.isDomain _

instance : IsDomain (Nonpositive G K ⧸ boundedAwayIdeal G K) := isDomain_germ G K

instance : (boundedAwayIdeal G K).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

end HahnSeries.Nonpositive
