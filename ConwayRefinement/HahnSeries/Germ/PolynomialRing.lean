/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import ConwayRefinement.Blueprint
public import ConwayRefinement.HahnSeries.Germ.GermAt
public import ConwayRefinement.RingTheory.TruncationGerms.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Algebraic.Defs
import ConwayRefinement.HahnSeries.Germ.GermSupport
import ConwayRefinement.RingTheory.TruncationGerms.Transcendence

/-!
# The ring of germs is a polynomial ring

Let `G` be a nontrivial ordered abelian group whose additive uniformity is Cauchy complete, `K` a
field of characteristic zero, and `J` the ideal of series in `K((G^{≤0}))` whose support is bounded
away from zero. The germs of nonpositive series satisfy the convolution formula and have
well-ordered support. The first germ outside a subalgebra with representatives whose germs lie
in it is transcendental over the subalgebra (`transcendental_mk_of_germAt_mem`).
By Zorn's lemma every subalgebra with such representatives is a polynomial ring over `K`.
Taking the full ring of germs gives polynomiality of `K((G^{≤0}))/J` and primality of `J`.
-/

open Set
open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

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
/-- The germs `germAt γ` of nonpositive series at exponents `γ ∈ G` satisfy the axioms of
`TruncationGerms` on `K((G^{≤0}))`, with values in the ring of germs `K((G^{≤0}))/J`. -/
def truncationGerms : TruncationGerms K G (Nonpositive G K)
    (Nonpositive G K ⧸ boundedAwayIdeal G K) :=
  { convolutionGerms G K, constantGerms G K with
    germSupport_isWF b := isWF_setOf_germAt_ne_zero b }

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
/-- A polynomial relation of positive degree on a germ has a monic relation of the same degree if
the coefficients have representatives with germs in the coefficient subalgebra and all earlier
germs of the given series belong to it. -/
@[blueprint "lem:monic-germ-relation"
  (phase := "Polynomial presentations")
  (title := "Monic polynomial relations for germs")
  (statement := /--
    Assume (H). If a nonzero polynomial $p\in S[Y]$ of degree $d\ge1$ satisfies $p(x)=0$,
    then some monic $q\in S[Y]$ of degree $d$ satisfies $q(x)=0$.
  -/)
  (proof := /--
    Write $L_\xi B=[B^{|\xi}]$ and form the series $L(B)=\sum_\xi (L_\xi B)t^\xi$ over $Q$.
    Its support is the closed support of $B$ by \ref{lem:nonzero-germs} and is well ordered
    by \ref{lem:well-ordered-closure}. The map $L$ preserves addition. It preserves products by
    \ref{lem:convolution-formula}, with finite sums by \ref{lem:convolution-finite}.
    Write $L(X)=x+U$. The constant coefficient of $U$ is zero and its coefficients lie in $S$.

    Lift $p_i$ to $P_i\in A(S)$ and put $W=\sum_{i=0}^d P_i X^i$. In the polynomial
    $\sum_i L(P_i)(Y+U)^i$, take the coefficient of $t^\xi$ at each power of $Y$ to obtain
    $q_\xi(Y)\in S[Y]$. Then $q_\xi(x)=L_\xi W$, its degree is at most $d$, and its
    coefficient at $Y^d$ is $L_\xi P_d$. Since $[W]=0$, its germs vanish on $(\varepsilon,0]$
    for some $\varepsilon<0$ by \ref{lem:constant-germs}.

    Take the least $\xi>\varepsilon$ with $L_\xi P_d\ne0$. Such an exponent exists and is at
    most $0$, since $L_0P_d=p_d\ne0$. The germs of $P_d$ vanish on $(\varepsilon,\xi)$, so
    $L_\xi P_d$ is a nonzero scalar by \ref{lem:constant-germs}. Dividing $q_\xi$ by this scalar
    gives the required monic relation.
  -/)]
theorem exists_monic_relation_of_aeval_eq_zero
    (S : Subalgebra K (Nonpositive G K ⧸ boundedAwayIdeal G K))
    (hS : ∀ a ∈ S, ∃ b : Nonpositive G K,
      Ideal.Quotient.mk (boundedAwayIdeal G K) b = a ∧ ∀ ξ, germAt ξ b ∈ S)
    (X : Nonpositive G K) (hX : ∀ ξ < 0, germAt ξ X ∈ S)
    {n : ℕ} (p : Polynomial S) (hd : p.natDegree = n + 1) (hp : p ≠ 0)
    (heval : Polynomial.aeval (Ideal.Quotient.mk (boundedAwayIdeal G K) X) p = 0) :
    ∃ q : Polynomial S, q.natDegree = n + 1 ∧ q.Monic ∧
      Polynomial.aeval (Ideal.Quotient.mk (boundedAwayIdeal G K) X) q = 0 :=
  (truncationGerms G K).exists_monic_relation S X hS hX p hd hp heval

/-- A germ outside a subalgebra is transcendental over it if every element of the subalgebra
has a representative with germs in it and all negative-exponent germs of the given series
belong to it. -/
@[blueprint "lem:transcendence"
  (phase := "Polynomial presentations")
  (title := "Transcendence lemma")
  (statement := /--
    Let $K$ have characteristic $0$. Assume (H) and $x\notin S$. Then $x$ is transcendental
    over $S$.
  -/)
  (proof := /--
    Choose a nonzero relation of least degree $d$. A nonzero constant cannot vanish in $Q$, so
    $d\ge1$. By \ref{lem:monic-germ-relation} we may take a monic relation
    $Y^d+p_{d-1}Y^{d-1}+\cdots$. Lift its leading coefficient to $1$ and its other coefficients
    to $P_i\in A(S)$. As in \ref{lem:monic-germ-relation}, write $L(X)=x+U$ and expand
    $\sum_i L(P_i)(Y+U)^i$. Its leading coefficient is $1$ and its coefficient at $Y^{d-1}$
    is $L(P_{d-1})+dU$ by the binomial theorem.

    For $\xi<0$ sufficiently close to $0$, the polynomial $q_\xi$ obtained at exponent $\xi$
    vanishes at $x$. Its coefficient at $Y^d$ is zero because $1$ is supported at $0$, so
    minimality forces $q_\xi=0$. In particular $L_\xi P_{d-1}+dL_\xi X=0$ throughout a left
    neighbourhood of $0$. By \ref{lem:constant-germs} the germ $p_{d-1}+dx$ is a scalar.
    Since $p_{d-1}\in S$ and $d$ is invertible in $K$, this puts $x$ in $S$, a contradiction.
  -/)
  (highlight)]
theorem transcendental_mk_of_germAt_mem
    (S : Subalgebra K (Nonpositive G K ⧸ boundedAwayIdeal G K))
    (hS : ∀ a ∈ S, ∃ b : Nonpositive G K,
      Ideal.Quotient.mk (boundedAwayIdeal G K) b = a ∧ ∀ ξ, germAt ξ b ∈ S)
    (X : Nonpositive G K) (hX : ∀ ξ < 0, germAt ξ X ∈ S)
    (hx : Ideal.Quotient.mk (boundedAwayIdeal G K) X ∉ S) :
    Transcendental S (Ideal.Quotient.mk (boundedAwayIdeal G K) X) :=
  (truncationGerms G K).transcendental_germ S X hS hX hx
    (fun p hd hp heval ↦ exists_monic_relation_of_aeval_eq_zero S hS X hX p hd hp heval)

omit [CharZero K] in
/-- No nonzero element of the subalgebra multiplies a new germ into the subalgebra. -/
theorem mul_mk_notMem
    (S : Subalgebra K (Nonpositive G K ⧸ boundedAwayIdeal G K))
    (hS : ∀ a ∈ S, ∃ b : Nonpositive G K,
      Ideal.Quotient.mk (boundedAwayIdeal G K) b = a ∧ ∀ ξ, germAt ξ b ∈ S)
    (X : Nonpositive G K) (hX : ∀ ξ < 0, germAt ξ X ∈ S)
    (hx : Ideal.Quotient.mk (boundedAwayIdeal G K) X ∉ S)
    {a : Nonpositive G K ⧸ boundedAwayIdeal G K} (ha : a ∈ S) (ha0 : a ≠ 0) :
    a * Ideal.Quotient.mk (boundedAwayIdeal G K) X ∉ S :=
  (truncationGerms G K).mul_germ_notMem S hS X hX hx a ha ha0

omit [CompleteSpace G] [CharZero K] in
/-- If the germs of two series are in the same ratio to the left of zero as at zero and the
second series has nonzero germ, their germs differ by a scalar factor. -/
theorem exists_mk_eq_smul_of_proportional (U V : Nonpositive G K)
    (hV : Ideal.Quotient.mk (boundedAwayIdeal G K) V ≠ 0)
    (h : ∃ ε < 0, ∀ ξ, ε < ξ → ξ < 0 →
      Ideal.Quotient.mk (boundedAwayIdeal G K) V * germAt ξ U =
        Ideal.Quotient.mk (boundedAwayIdeal G K) U * germAt ξ V) :
    ∃ c : K, Ideal.Quotient.mk (boundedAwayIdeal G K) U =
      c • Ideal.Quotient.mk (boundedAwayIdeal G K) V :=
  (constantGerms G K).exists_germ_eq_smul_of_proportional isWF_setOf_germAt_ne_zero U V hV h

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
/-- If every element of `P` has a representative with germs in `P`, any proper subalgebra `S`
of `P` misses a germ in `P` with all earlier germs in `S`. -/
@[blueprint "lem:new-germ"
  (phase := "Polynomial presentations")
  (title := "Existence of a new germ")
  (statement := /--
    Let $S\subsetneq P\subseteq Q$ be $K$-subalgebras with $P\subseteq[A(P)]$.
    There is $X\in A$ with $[X^{|\xi}]\in S$ for every $\xi<0$ and $[X]\in P\setminus S$.
  -/)
  (proof := /--
    Choose $g\in P\setminus S$ and $b\in A(P)$ with $[b]=g$. The exponents at which the germ of
    $b$ lies outside $S$ include $0$ and belong to the closed support by \ref{lem:nonzero-germs}.
    The closed support is well ordered by \ref{lem:well-ordered-closure}, so these exponents have
    a least member $\gamma$. Set $X=b^{|\gamma}$. Its germ lies in $P\setminus S$.
    For $\xi<0$, its germ at $\xi$ is $[b^{|\gamma+\xi}]$ by
    \ref{lem:germs-of-translated-truncation}, and $\gamma+\xi<\gamma$ puts that germ in $S$.
  -/)]
theorem exists_germAt_mem_mk_mem_notMem
    {P S : Subalgebra K (Nonpositive G K ⧸ boundedAwayIdeal G K)}
    (hP : (germMaps G K).HasRepresentativesWithGermsIn P) (hSP : S < P) :
    ∃ X : Nonpositive G K, (∀ ξ < 0, germAt ξ X ∈ S) ∧
      Ideal.Quotient.mk (boundedAwayIdeal G K) X ∈ P ∧
      Ideal.Quotient.mk (boundedAwayIdeal G K) X ∉ S :=
  (germMaps G K).exists_germAt_mem_germ_mem_notMem isWF_setOf_germAt_ne_zero
    (fun b ξ _ ↦ ⟨translatedTruncation ξ b, fun _ hζ ↦ germAt_translatedTruncation b ξ hζ⟩) hP hSP

omit [CompleteSpace G] [CharZero K] in
/-- Some germ outside a proper subalgebra has all its earlier germs in the subalgebra. -/
theorem exists_germAt_mem_mk_notMem
    (S : Subalgebra K (Nonpositive G K ⧸ boundedAwayIdeal G K)) (hS : S ≠ ⊤) :
    ∃ X : Nonpositive G K, (∀ ξ < 0, germAt ξ X ∈ S) ∧
      Ideal.Quotient.mk (boundedAwayIdeal G K) X ∉ S := by
  obtain ⟨X, hX, _, hx⟩ := exists_germAt_mem_mk_mem_notMem
    (germMaps G K).hasRepresentativesWithGermsIn_top (lt_top_iff_ne_top.mpr hS)
  exact ⟨X, hX, hx⟩

/-- A subalgebra of the ring of germs is a polynomial algebra if each element has a
representative with all its germs in the subalgebra. -/
@[blueprint "thm:germ-subalgebra-polynomial"
  (phase := "Polynomial presentations")
  (title := "Polynomial presentation of a subalgebra of germs")
  (statement := /--
    Let $K$ have characteristic $0$ and $G$ be Cauchy complete. Let $P\subseteq Q$ be a
    $K$-subalgebra with $P\subseteq[A(P)]$. For some set $I$ there is a
    $K$-algebra isomorphism $K[Y_i:i\in I]\simeq P$.
  -/)
  (proof := /--
    By Zorn's lemma choose a set of germs $T\subseteq P$, algebraically independent over $K$,
    maximal subject to $S=K[T]\subseteq[A(S)]$. The empty set qualifies because scalars have
    constant representatives. A union of a chain qualifies because each polynomial uses only
    finitely many variables, which all occur in one member of the chain.

    If $S\subsetneq P$, \ref{lem:new-germ} gives $X\in A$ with $x=[X]\in P\setminus S$ and all
    earlier germs in $S$. By \ref{lem:transcendence}, $x$ is transcendental over $S$, so
    $T\cup\{x\}$ is algebraically independent. By \ref{lem:representatives-adjoin},
    $S[x]\subseteq[A(S[x])]$. This contradicts maximality, so $S=P$. Evaluation at $T$ gives
    the required isomorphism.
  -/)]
theorem exists_mvPolynomial_algEquiv_of_representatives
    (P : Subalgebra K (Nonpositive G K ⧸ boundedAwayIdeal G K))
    (hP : (germMaps G K).HasRepresentativesWithGermsIn P) :
    ∃ ι : Type (max (u + 1) v), Nonempty (MvPolynomial ι K ≃ₐ[K] P) := by
  obtain ⟨T, hind, he⟩ := exists_algebraicIndependent_adjoin_eq P
    (germMaps G K).HasRepresentativesWithGermsIn
    (germMaps G K).hasRepresentativesWithGermsIn_bot
    (fun _ hcn hchain hc ↦
      (germMaps G K).hasRepresentativesWithGermsIn_adjoin_sUnion hcn hchain hc)
    fun S _ hS hSP ↦ by
      obtain ⟨X, hX, hxP, hx⟩ := exists_germAt_mem_mk_mem_notMem hP hSP
      exact ⟨_, hxP, transcendental_mk_of_germAt_mem S hS X hX hx,
        exists_mk_eq_of_mem_adjoin S hS X hX⟩
  have he' : Algebra.adjoin K (Set.range ((↑) : T → _)) = P := by
    rwa [Subtype.range_coe_subtype, Set.setOf_mem_eq]
  exact ⟨ULift.{u + 1} T, ⟨(MvPolynomial.renameEquiv K Equiv.ulift).trans
    (hind.aevalEquiv.trans (Subalgebra.equivOfEq _ _ he'))⟩⟩

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
    Every germ is represented by a series, and every germ of that series is again in $Q$.
    Apply \ref{thm:germ-subalgebra-polynomial} with $P=Q$.
  -/)
  (highlight)]
theorem exists_mvPolynomial_algEquiv_germ :
    ∃ ι : Type (max (u + 1) v), Nonempty
      (MvPolynomial ι K ≃ₐ[K]
        Nonpositive G K ⧸ boundedAwayIdeal G K) := by
  obtain ⟨ι, ⟨e⟩⟩ := exists_mvPolynomial_algEquiv_of_representatives ⊤
    (germMaps G K).hasRepresentativesWithGermsIn_top
  exact ⟨ι, ⟨e.trans Subalgebra.topEquiv⟩⟩

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
