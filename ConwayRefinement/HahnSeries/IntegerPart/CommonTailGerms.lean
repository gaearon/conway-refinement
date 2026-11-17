/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.ConvexSubgroup.CommonTail
public import ConwayRefinement.HahnSeries.Germ.BoundedSupport
public import ConwayRefinement.HahnSeries.ConvexSubgroup.Restriction

import ConwayRefinement.Algebra.Divisibility.RetractionPrimality
import ConwayRefinement.Blueprint
import ConwayRefinement.HahnSeries.Nonpositive.ArchimedeanClasses

/-!
# Germs of bounded series over a Cauchy-complete common-tail quotient

Let `C` be the quotient of an ordered rational vector space by the common tail below a family `T`
of nonzero Archimedean classes with no least member in the magnitude order. In the ring
`K((C^{≤0}))_κ` of `κ`-bounded nonpositive series, the ideal `J` of series whose support is
bounded away from zero is killed by restriction to the closed ball of every sufficiently small
Archimedean class. When `C` is Cauchy complete, every element of the ring of bounded germs
`K((C^{≤0}))_κ / J` is primal, because that ring is a polynomial ring over `K`.
-/

open Cardinal Set
open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.CardSuppLTNonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field K]
variable {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]

variable [Nontrivial G]

open Classical in
/-- An element of `J` is killed by restriction to the closed ball of every sufficiently small
Archimedean class. -/
theorem eventually_restrictToAddSubgroup_eq_zero [NoMaxOrder (FiniteArchimedeanClass G)]
    {x : CardSuppLTNonpositive (G := G) (L := K) (κ := κ)} (hx : x ∈ boundedAwayIdeal G K κ) :
    ∀ᶠ q in Filter.atTop, CardSuppLTTruncationIntegerPart.restrictToAddSubgroup ⊤
      (FiniteArchimedeanClass.closedBallAddSubgroup q) x = 0 := by
  obtain ⟨e, he, hxe⟩ := (mem_boundedAwayIdeal x).mp hx
  filter_upwards [Filter.eventually_gt_atTop (FiniteArchimedeanClass.mk e he.ne)] with q hq
  apply Subtype.ext; apply Subtype.ext
  ext g
  rw [CardSuppLTTruncationIntegerPart.coe_restrictToAddSubgroup, HahnSeries.coeff_filter]
  split_ifs with hg
  · by_contra hcoeff
    have hgs : g ∈ (x : K⟦G⟧).support := HahnSeries.mem_support _ _ |>.mpr hcoeff
    have hg0 : g ≠ 0 := fun h ↦ (not_le_of_gt he) (h ▸ hxe hgs)
    have hcg := (FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff).mp hg hg0
    have hge := ArchimedeanClass.mk_le_mk_of_le_of_nonpos (hxe hgs) he.le
    exact (not_le_of_gt hq) (hcg.trans hge)
  · rfl

end HahnSeries.CardSuppLTNonpositive

namespace FiniteArchimedeanClass

variable {G : Type u}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Module ℚ G] [PosSMulMono ℚ G]

private theorem zero_lt_mk_positiveRepresentative (T : Set (FiniteArchimedeanClass G))
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) (c : T) :
    (0 : TailQuotient T) < Submodule.Quotient.mk (positiveRepresentative c.1) := by
  rw [← Submodule.Quotient.mk_zero]
  apply ConvexQuotient.mk_lt_mk_iff.mpr
  refine ⟨positiveRepresentative_pos c.1, ?_⟩
  intro hmem
  have htail : positiveRepresentative c.1 ∈ tailKernel T := by
    rw [← tailSubmodule_toAddSubgroup ℚ T]
    simpa using hmem
  exact positiveRepresentative_not_mem_tailKernel hT c htail

/-- The quotient by the common tail below a nonempty family of Archimedean classes with no least
member in the magnitude order is nontrivial. -/
theorem nontrivial_tailQuotient (T : Set (FiniteArchimedeanClass G)) [Nonempty T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) : Nontrivial (TailQuotient T) :=
  ⟨⟨0, _, (zero_lt_mk_positiveRepresentative T hT (Classical.arbitrary T)).ne⟩⟩

end FiniteArchimedeanClass

namespace HahnSeries.CardSuppLTNonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Module ℚ G] [PosSMulMono ℚ G] [Field K] [CharZero K]

open CardSuppLTTruncationIntegerPart in
/-- Over a Cauchy-complete common-tail quotient, a bounded nonpositive series is primal as soon
as, at arbitrarily small Archimedean classes, its restriction to the closed ball is nonzero and
the complementary factor is primal. -/
@[blueprint "lem:primality-from-germs"
  (phase := "Reduction along Archimedean classes")
  (title := "Primality from germs and restrictions")
  (statement := /--
    Let $G$ be an ordered $\mathbb Q$-vector space, $L$ a field of characteristic $0$, and $T$ a
    nonempty set of nonzero Archimedean classes of $G$ without $\prec$-least element, satisfying
    (B2)$_T$. Put $\Gamma=G/G_T$, let $f\in L((\Gamma^{\le0}))_\kappa$, and for a nonzero class $q$
    of $\Gamma$ let $\rho_q$ be the restriction to $\Gamma_{\preceq q}$. Suppose that for every
    nonzero class $q_0$ of $\Gamma$ there is a nonzero class $q\preceq q_0$ with $\rho_q(f)\ne0$ and
    $f=\rho_q(f)\,w$ for some primal $w$. Then $f$ is primal in $L((\Gamma^{\le0}))_\kappa$.
  -/)
  (proof := /--
    Write $B=L((\Gamma^{\le0}))_\kappa$, which is $Z+R((\Gamma^{<0}))_\kappa$ with $Z=R=L$, and let
    $J'$ be its ideal of series whose support is bounded away from $0$. By
    \ref{lem:convex-restriction-ring-hom} each $\rho_q$ is a ring endomorphism of $B$, and it is
    idempotent. If $j\in J'$ has support in $(-\infty,\delta]$ with $\delta<0$, then $\rho_q(j)=0$
    for every nonzero class $q\prec[\delta]$. By \ref{thm:bounded-hahn-germ-polynomial-algebra},
    applied to the Cauchy complete group $\Gamma$, the ring $B/J'$ is a polynomial ring over $L$,
    hence a unique factorisation domain, so its elements are primal.

    Let $f\mid cd$, say $cd=fe$. Choose $p_1,p_2,r_1,r_2\in B$ with $f\equiv p_1p_2$,
    $c\equiv p_1r_1$ and $d\equiv p_2r_2$ modulo $J'$. The three differences have support bounded
    away from $0$. Since $T$ has no $\prec$-least element, $\Gamma\ne\{0\}$, so there are nonzero
    classes $q_0$ below the classes of these bounds. Take $q\preceq q_0$ as in the hypothesis: then
    $\rho_q$ kills the three differences, $\rho_q(f)\ne0$, and $f=\rho_q(f)\,w$ with $w$ primal.
    With $g_k=\rho_q(p_k)$ this gives $\rho_q(f)=g_1g_2$, $\rho_q(c)=g_1\rho_q(r_1)$ and
    $\rho_q(d)=g_2\rho_q(r_2)$. Each $g_k$ is nonzero and fixed by $\rho_q$, so
    \ref{lem:divisibility-from-convex-restriction}, applied with $Z=R=L$, exponent group $\Gamma$
    and the convex subgroup $\Gamma_{\preceq q}$, gives $g_1\mid c$ and $g_2\mid d$; write $c=g_1c'$
    and $d=g_2d'$. Cancelling $g_1g_2\ne0$ from $g_1g_2c'd'=fe=g_1g_2we$ gives $w\mid c'd'$, hence
    $w=w_1w_2$ with $w_1\mid c'$ and $w_2\mid d'$. Then $f=(g_1w_1)(g_2w_2)$ with $g_1w_1\mid c$ and
    $g_2w_2\mid d$.
  -/)]
theorem isPrimal_of_frequently_restriction_mul_isPrimal
    {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]
    (T : Set (FiniteArchimedeanClass G)) [Nonempty T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d)
    [CompleteSpace (FiniteArchimedeanClass.TailQuotient T)]
    {f : CardSuppLTNonpositive (G := FiniteArchimedeanClass.TailQuotient T) (L := K) (κ := κ)}
    (hf : ∃ᶠ q in Filter.atTop,
      restrictToAddSubgroup ⊤ (FiniteArchimedeanClass.closedBallAddSubgroup q) f ≠ 0 ∧
        ∃ w, f = restrictToAddSubgroup ⊤ (FiniteArchimedeanClass.closedBallAddSubgroup q) f * w ∧
          IsPrimal w) :
    IsPrimal f := by
  letI := FiniteArchimedeanClass.nontrivial_tailQuotient T hT
  letI : NoMaxOrder (FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T)) :=
    FiniteArchimedeanClass.quotient_noMax_of_eq_tailKernel T
      (FiniteArchimedeanClass.tailSubmodule ℚ T).toAddSubgroup
      (FiniteArchimedeanClass.tailSubmodule_toAddSubgroup ℚ T) hT
  let ρ : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T) →
      CardSuppLTNonpositive (G := FiniteArchimedeanClass.TailQuotient T) (L := K) (κ := κ) →+*
        CardSuppLTNonpositive (G := FiniteArchimedeanClass.TailQuotient T) (L := K) (κ := κ) :=
    fun q ↦ restrictToAddSubgroupRingHom ⊤ (FiniteArchimedeanClass.closedBall_ordConnected q)
  have hρ (q) (a) : ρ q a =
      restrictToAddSubgroup ⊤ (FiniteArchimedeanClass.closedBallAddSubgroup q) a :=
    restrictToAddSubgroupRingHom_apply _ _ a
  refine isPrimal_of_frequently_retraction_mul_isPrimal
    (boundedAwayIdeal _ K κ) Filter.atTop ρ
    (fun q a ↦ by rw [hρ, hρ, restrictToAddSubgroup_restrictToAddSubgroup])
    (fun j hj ↦ by simpa only [hρ] using eventually_restrictToAddSubgroup_eq_zero hj)
    (fun q a b ha ha0 hab ↦ dvd_of_dvd_restrictToAddSubgroup _
      (FiniteArchimedeanClass.closedBall_ordConnected q) ((hρ q a).symm.trans ha) ha0
        ((hρ q b) ▸ hab))
    isPrimal_germ ?_
  simpa only [hρ] using hf

end HahnSeries.CardSuppLTNonpositive
