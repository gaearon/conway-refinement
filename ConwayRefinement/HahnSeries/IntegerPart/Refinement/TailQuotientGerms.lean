/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.LimitTailQuotient
public import ConwayRefinement.HahnSeries.CardinalTruncationResidue
public import ConwayRefinement.HahnSeries.IntegerPart.Refinement.CardinalGermRefinement
public import ConwayRefinement.HahnSeries.IntegerPart.Refinement.ConvexRestriction
public import ConwayRefinement.Algebra.Order.ArchimedeanBall
public import ConwayRefinement.HahnSeries.SupportArchimedeanClasses
public import ConwayRefinement.HahnSeries.Germ.Basic
public import ConwayRefinement.Algebra.Divisibility.RetractionPrimality

import ConwayRefinement.Blueprint

/-!
# Germs of bounded series over a Cauchy-complete common-tail quotient

Let `C` be the quotient of an ordered rational vector space by the common tail below a family `T`
of nonzero Archimedean classes with no least member in the magnitude order. In the ring
`K((C^{≤0}))_κ` of `κ`-bounded nonpositive series, the ideal `J` of series whose support is
bounded away from zero is killed by restriction to the closed ball of every sufficiently small
Archimedean class. When
`C` is Cauchy complete and `#T < κ`, every divisibility relation in `K((C^{≤0}))_κ` refines
modulo `J`: this is the bounded form of refinement in the ring of germs, a polynomial ring.
-/

open Cardinal Set
open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.CardSuppLTNonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field K]
variable {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]

/-- Package a nonpositive Hahn series with an explicit support-cardinality bound. -/
def ofNonpositive (x : Nonpositive G K) (hx : (x : K⟦G⟧).cardSupp < κ) :
    CardSuppLTNonpositive (G := G) (L := K) (κ := κ) :=
  ⟨⟨x, (mem_cardSuppLTSubfield (Γ := G) (R := K) (κ := κ)).mpr hx⟩, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    exact ⟨x.2, Subring.mem_top _⟩⟩

/-- Forgetting the cardinal-bound package recovers the original nonpositive series. -/
@[simp]
theorem coe_ofNonpositive (x : Nonpositive G K) (hx : (x : K⟦G⟧).cardSupp < κ) :
    ((ofNonpositive x hx : CardSuppLTNonpositive (G := G) (L := K) (κ := κ)) :
      K⟦G⟧) = (x : K⟦G⟧) :=
  (rfl)

/-- Forgetting the support bound from a packaged nonpositive series recovers that series. -/
@[simp]
theorem toNonpositiveRingHom_ofNonpositive
    (x : Nonpositive G K) (hx : (x : K⟦G⟧).cardSupp < κ) :
    CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring K)
      (ofNonpositive x hx) = x := by
  apply Subtype.ext
  rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
  exact coe_ofNonpositive x hx

variable [Nontrivial G]

variable (G K κ) in
/-- The ideal `J` of `κ`-bounded nonpositive series whose support is bounded away from zero. -/
def boundedAwayIdeal : Ideal (CardSuppLTNonpositive (G := G) (L := K) (κ := κ)) :=
  (Nonpositive.boundedAwayIdeal G K).comap
    (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring K))

theorem mem_boundedAwayIdeal (x : CardSuppLTNonpositive (G := G) (L := K) (κ := κ)) :
    x ∈ boundedAwayIdeal G K κ ↔ ∃ c < (0 : G), (x : K⟦G⟧).support ⊆ Iic c := by
  rw [boundedAwayIdeal, Ideal.mem_comap, Nonpositive.mem_boundedAwayIdeal,
    CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]

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

/-- The positive representatives of the classes of `T` are coinitial among the positive elements
of the common-tail quotient. -/
theorem exists_mk_positiveRepresentative_le (T : Set (FiniteArchimedeanClass G))
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d) {y : TailQuotient T} (hy : 0 < y) :
    ∃ x ∈ Set.range (fun c : T ↦
        (Submodule.Quotient.mk (positiveRepresentative c.1) : TailQuotient T)),
      0 < x ∧ x ≤ y := by
  obtain ⟨c, hcy⟩ := exists_tailQuotient_positiveRepresentative_le (T := T) hy
  exact ⟨_, Set.mem_range_self c, zero_lt_mk_positiveRepresentative T hT c, hcy⟩

end FiniteArchimedeanClass

namespace HahnSeries.CardSuppLTNonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Module ℚ G] [PosSMulMono ℚ G] [Field K] [CharZero K]

/-- Over a Cauchy-complete common-tail quotient, every divisibility relation among
`κ`-bounded nonpositive series refines modulo the ideal `J` of series bounded away from zero. -/
@[blueprint "thm:complete-tail-quotient-refinement"
  (phase := "Refinement over Archimedean classes")
  (title := "Refinement modulo series bounded away from zero over a common-tail quotient")
  (statement := /--
    Let $T$ be a nonempty set of nonzero Archimedean classes with no least
    member in the magnitude order and cardinality less than $\kappa$, and let
    $C$ be the quotient of the exponent group by the common tail below $T$.
    Assume that $C$ is Cauchy complete for its additive uniformity.  If
    $f\mid xy$ in $K((C^{\le0}))_\kappa$, then there are
    $p_1,p_2,q_1,q_2\in K((C^{\le0}))_\kappa$ such that, modulo the ideal $J$
    of series whose support is bounded away from zero,
    \[
      f\equiv p_1p_2,\qquad x\equiv p_1q_1,\qquad y\equiv p_2q_2.
    \]
  -/)
  (proof := /--
    Write $xy=fz$.  Positive representatives of the classes in $T$ give a
    positive coinitial subset of $C$ of cardinality less than $\kappa$.  Apply
    \ref{thm:cardinal-bounded-germ-refinement} to $fz=xy$ and keep three of
    the four resulting congruences.
  -/)]
theorem exists_refinement_mod_boundedAwayIdeal
    {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]
    (T : Set (FiniteArchimedeanClass G)) [Nonempty T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d)
    [CompleteSpace (FiniteArchimedeanClass.TailQuotient T)]
    (hTcard : #T < κ)
    {f x y : CardSuppLTNonpositive
      (G := FiniteArchimedeanClass.TailQuotient T) (L := K) (κ := κ)}
    (hf : f ∣ x * y) :
    letI := FiniteArchimedeanClass.nontrivial_tailQuotient T hT
    ∃ p₁ p₂ q₁ q₂ : CardSuppLTNonpositive
        (G := FiniteArchimedeanClass.TailQuotient T) (L := K) (κ := κ),
      f - p₁ * p₂ ∈ boundedAwayIdeal (FiniteArchimedeanClass.TailQuotient T) K κ ∧
        x - p₁ * q₁ ∈ boundedAwayIdeal (FiniteArchimedeanClass.TailQuotient T) K κ ∧
        y - p₂ * q₂ ∈ boundedAwayIdeal (FiniteArchimedeanClass.TailQuotient T) K κ := by
  letI := FiniteArchimedeanClass.nontrivial_tailQuotient T hT
  obtain ⟨z, hz⟩ := hf
  let toN := CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
    (G := FiniteArchimedeanClass.TailQuotient T) (R := K) (κ := κ) (⊤ : Subring K)
  have hcard (w : CardSuppLTNonpositive
      (G := FiniteArchimedeanClass.TailQuotient T) (L := K) (κ := κ)) :
      (toN w : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ :=
    CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt _ w
  let scale : T → FiniteArchimedeanClass.TailQuotient T := fun c ↦
    Submodule.Quotient.mk (FiniteArchimedeanClass.positiveRepresentative c.1)
  have hEcard : #(Set.range scale) < κ := Cardinal.mk_range_le.trans_lt hTcard
  have hfz : toN f * toN z = toN x * toN y := by
    rw [← map_mul, ← map_mul, ← hz]
  obtain ⟨e, e', g, h, hfe, -, hxe, hye, hecard, he'card, hgcard, hhcard⟩ :=
    Nonpositive.exists_cardinal_germ_refinement (Set.range scale) hEcard
      (fun y hy ↦ FiniteArchimedeanClass.exists_mk_positiveRepresentative_le T hT hy)
      (toN f) (toN z) (toN x) (toN y) (hcard f) (hcard z) (hcard x) (hcard y) hfz
  have hmem {a : CardSuppLTNonpositive
      (G := FiniteArchimedeanClass.TailQuotient T) (L := K) (κ := κ)}
      {b c : Nonpositive (FiniteArchimedeanClass.TailQuotient T) K}
      (hb : (b : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ)
      (hc : (c : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ)
      (habc : ∃ r < (0 : FiniteArchimedeanClass.TailQuotient T), ∀ q > r,
        (toN a : HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).coeff q =
          (b * c : Nonpositive (FiniteArchimedeanClass.TailQuotient T) K).1.coeff q) :
      a - ofNonpositive b hb * ofNonpositive c hc ∈
        boundedAwayIdeal (FiniteArchimedeanClass.TailQuotient T) K κ := by
    rw [boundedAwayIdeal, Ideal.mem_comap, map_sub, map_mul,
      toNonpositiveRingHom_ofNonpositive, toNonpositiveRingHom_ofNonpositive]
    exact Ideal.Quotient.eq.mp ((Nonpositive.mk_eq_mk_iff_eventually_coeff_eq _ _).mpr habc)
  exact ⟨ofNonpositive e hecard, ofNonpositive e' he'card, ofNonpositive g hgcard,
    ofNonpositive h hhcard, hmem hecard he'card hfe, hmem hecard hgcard hxe,
    hmem he'card hhcard hye⟩

end HahnSeries.CardSuppLTNonpositive

namespace HahnSeries.CardSuppLTNonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Module ℚ G] [PosSMulMono ℚ G] [Field K] [CharZero K]

open CardSuppLTTruncationIntegerPart in
/-- Over a Cauchy-complete common-tail quotient, a bounded nonpositive series is primal as soon
as, at arbitrarily small Archimedean classes, its restriction to the closed ball is nonzero and
the complementary factor is primal. -/
theorem isPrimal_of_frequently_restriction_mul_isPrimal
    {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]
    (T : Set (FiniteArchimedeanClass G)) [Nonempty T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d)
    [CompleteSpace (FiniteArchimedeanClass.TailQuotient T)]
    (hTcard : #T < κ)
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
    (fun f a b h ↦ exists_refinement_mod_boundedAwayIdeal T hT hTcard h) ?_
  simpa only [hρ] using hf

end HahnSeries.CardSuppLTNonpositive
