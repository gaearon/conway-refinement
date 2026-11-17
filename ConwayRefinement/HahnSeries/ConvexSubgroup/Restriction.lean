/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.BoundedSupport.EmbDomain

import ConwayRefinement.Blueprint
import ConwayRefinement.HahnSeries.Nonpositive.SubgroupSupport
import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Restriction to a convex subgroup of the exponents

For a convex subgroup `C` of the exponent group, restriction of the support to `C` is a ring
endomorphism of the bounded integer part `Z + K((G^{<0}))_κ`: for nonpositive exponents, a sum
lies in `C` exactly when both summands do.

A divisor supported in `C` divides a series as soon as it divides the restriction: the discarded
part has all its exponents nonpositive and outside `C`, so multiplying it by the inverse of the
divisor keeps every exponent nonpositive and outside `C`, hence away from zero. The cofactor
therefore stays in the integral part. Dually, a series with nonzero restriction factors as that
restriction times a series of constant coefficient one supported away from `C`.
-/

public noncomputable section

open scoped HahnSeries

universe u

namespace HahnSeries.Nonpositive

variable {G R : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Ring R]

/-- A coefficient restriction is multiplicative on nonpositive series when membership of a sum
of two nonpositive exponents is equivalent to membership of both summands. -/
theorem filter_mul_of_add_iff (p : G → Prop) [DecidablePred p]
    (hpadd : ∀ {i j : G}, i ≤ 0 → j ≤ 0 → (p (i + j) ↔ p i ∧ p j))
    (x y : Nonpositive G R) :
    HahnSeries.filter p ((x * y : Nonpositive G R) : R⟦G⟧) =
      HahnSeries.filter p (x : R⟦G⟧) * HahnSeries.filter p (y : R⟦G⟧) := by
  change HahnSeries.filter p ((x : R⟦G⟧) * (y : R⟦G⟧)) = _
  ext g
  rw [HahnSeries.coeff_filter, HahnSeries.coeff_mul, HahnSeries.coeff_mul]
  by_cases hg : p g
  · rw [if_pos hg]
    apply Finset.sum_congr
    · ext ij
      simp only [Finset.mem_addAntidiagonal, HahnSeries.support_filter]
      constructor
      · rintro ⟨hi, hj, hij⟩
        have hp := (hpadd (support_subset x hi) (support_subset y hj)).mp (hij ▸ hg)
        exact ⟨⟨hi, hp.1⟩, ⟨hj, hp.2⟩, hij⟩
      · rintro ⟨⟨hi, _⟩, ⟨hj, _⟩, hij⟩
        exact ⟨hi, hj, hij⟩
    · intro ij hij
      rw [HahnSeries.coeff_filter, HahnSeries.coeff_filter]
      rw [Finset.mem_addAntidiagonal] at hij
      rw [HahnSeries.support_filter, HahnSeries.support_filter] at hij
      simp [hij.1.2, hij.2.1.2]
  · rw [if_neg hg]
    apply (Finset.sum_eq_zero fun ij hij ↦ ?_).symm
    rw [Finset.mem_addAntidiagonal] at hij
    rw [HahnSeries.support_filter] at hij
    rw [HahnSeries.support_filter] at hij
    have hpij := (hpadd (support_subset x hij.1.1) (support_subset y hij.2.1.1)).mpr
      ⟨hij.1.2, hij.2.1.2⟩
    rw [hij.2.2] at hpij
    exact (hg hpij).elim

end HahnSeries.Nonpositive

namespace HahnSeries.ConvexRestriction

variable {G K : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Field K]

private theorem add_nonpos_of_mem_of_nonpos_of_not_mem {C : AddSubgroup G}
    (hC : (C : Set G).OrdConnected) {a b : G}
    (ha : a ∈ C) (hb : b ≤ 0) (hbC : b ∉ C) : a + b ≤ 0 := by
  by_contra h
  have hab : 0 < a + b := lt_of_not_ge h
  apply hbC
  have hba : 0 < b + a := by simpa only [add_comm] using hab
  exact hC.out (C.neg_mem ha) C.zero_mem ⟨(neg_lt_iff_pos_add.mpr hba).le, hb⟩

/-- Adding an exponent in a convex subgroup to one outside it preserves the outside exponent's
Archimedean class. -/
private theorem archimedeanClass_add_eq_right_of_mem_of_not_mem {C : AddSubgroup G}
    (hC : (C : Set G).OrdConnected) {i j : G} (hi : i ∈ C) (hj : j ∉ C) :
    ArchimedeanClass.mk (i + j) = ArchimedeanClass.mk j := by
  apply ArchimedeanClass.mk_add_eq_mk_right
  rw [ArchimedeanClass.mk_lt_mk]
  intro n
  apply lt_of_not_ge
  intro hji
  have habsi : |i| ∈ C := abs_mem_iff.mpr hi
  have hni : n • |i| ∈ C := C.nsmul_mem habsi n
  have habsj : |j| ∈ C := hC.out C.zero_mem hni ⟨abs_nonneg j, hji⟩
  exact hj (abs_mem_iff.mp habsj)

open Classical in
/-- **Truncation-divisibility.** A nonzero divisor supported in a convex subgroup divides a
series with nonpositive support as soon as it divides the convex restriction, and the cofactor
stays in the integral part: nonpositive support with constant coefficient in the coefficient
subring. The discarded part has all exponents outside the subgroup, so dividing it by the
subgroup-supported divisor keeps every exponent nonpositive and nonzero. -/
private theorem exists_integral_cofactor {C : AddSubgroup G}
    (hC : (C : Set G).OrdConnected) (Z : Subring K)
    {q c w : K⟦G⟧} (hq : q.support ⊆ (C : Set G)) (hq0 : q ≠ 0)
    (hc : c.support ⊆ Set.Iic 0)
    (hw : w.support ⊆ Set.Iic 0) (hw0 : w.coeff 0 ∈ Z)
    (heq : HahnSeries.filter (· ∈ C) c = q * w) :
    ∃ w' : K⟦G⟧, w'.support ⊆ Set.Iic 0 ∧ w'.coeff 0 ∈ Z ∧ c = q * w' := by
  classical
  set r : K⟦G⟧ := HahnSeries.filter (fun g ↦ g ∉ C) c with hr
  have hsplit : HahnSeries.filter (· ∈ C) c + r = c := HahnSeries.filter_add_filter_not _ c
  have hrsupp : ∀ g ∈ r.support, g ≤ 0 ∧ g ∉ C := by
    intro g hg
    rw [hr, HahnSeries.support_filter] at hg
    exact ⟨hc hg.1, hg.2⟩
  -- The inverse of the divisor stays supported in the subgroup.
  have hone : (1 : K⟦G⟧).support ⊆ (C : Set G) := by
    intro g hg
    have hg0 : g = 0 := by
      simpa only [HahnSeries.support_one, Set.mem_singleton_iff] using hg
    exact hg0 ▸ C.zero_mem
  have hinv : (q⁻¹ : K⟦G⟧).support ⊆ (C : Set G) :=
    HahnSeries.support_subset_of_mul_eq (f := (1 : K⟦G⟧)) hq hq0 hone
      (mul_inv_cancel₀ hq0).symm
  -- The discarded part divided by the divisor keeps nonpositive, nonzero exponents.
  have hprod : ∀ g ∈ ((q⁻¹ : K⟦G⟧) * r).support, g ≤ 0 ∧ g ∉ C := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := HahnSeries.support_mul_subset hg
    obtain ⟨hb0, hbC⟩ := hrsupp b hb
    refine ⟨add_nonpos_of_mem_of_nonpos_of_not_mem hC (hinv ha) hb0 hbC, ?_⟩
    intro hab
    exact hbC (by simpa using C.sub_mem hab (hinv ha))
  refine ⟨w + q⁻¹ * r, ?_, ?_, ?_⟩
  · intro g hg
    rcases HahnSeries.support_add_subset _ _ hg with h | h
    · exact hw h
    · exact (hprod g h).1
  · have hzero : ((q⁻¹ : K⟦G⟧) * r).coeff 0 = 0 := by
      by_contra hne
      exact (hprod 0 ((HahnSeries.mem_support _ _).mpr hne)).2 C.zero_mem
    rw [HahnSeries.coeff_add, hzero, add_zero]
    exact hw0
  · rw [mul_add, ← heq, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul, hsplit]

open Classical in
/-- **The class-block factorisation.** An integral series with a nonzero convex restriction is
that restriction times an integral series whose constant coefficient is one and whose remaining
exponents all lie outside the subgroup. An induction over support classes can therefore split an
integral series into blocks and, with primality of each block, conclude primality of the whole by
`IsPrimal.mul`. -/
private theorem exists_complementary_factor {C : AddSubgroup G}
    (hC : (C : Set G).OrdConnected) {b : K⟦G⟧} (hb : b.support ⊆ Set.Iic 0)
    (hne : HahnSeries.filter (· ∈ C) b ≠ 0) :
    ∃ w : K⟦G⟧, w.support ⊆ Set.Iic 0 ∧ w.coeff 0 = 1 ∧
      (∀ g ∈ w.support, g ≠ 0 → g ∉ C) ∧
      (∀ g ∈ w.support, g ≠ 0 →
        ArchimedeanClass.mk g ∈ ArchimedeanClass.mk '' b.support) ∧
      b = HahnSeries.filter (· ∈ C) b * w := by
  classical
  set q : K⟦G⟧ := HahnSeries.filter (· ∈ C) b with hq_def
  set r : K⟦G⟧ := HahnSeries.filter (fun g ↦ g ∉ C) b with hr_def
  have hsplit : q + r = b := HahnSeries.filter_add_filter_not _ b
  have hqC : q.support ⊆ (C : Set G) := by
    intro g hg
    rw [hq_def, HahnSeries.support_filter] at hg
    exact hg.2
  have hrsupp : ∀ g ∈ r.support, g ≤ 0 ∧ g ∉ C := by
    intro g hg
    rw [hr_def, HahnSeries.support_filter] at hg
    exact ⟨hb hg.1, hg.2⟩
  have hone : (1 : K⟦G⟧).support ⊆ (C : Set G) := by
    intro g hg
    have hg0 : g = 0 := by
      simpa only [HahnSeries.support_one, Set.mem_singleton_iff] using hg
    exact hg0 ▸ C.zero_mem
  have hinv : (q⁻¹ : K⟦G⟧).support ⊆ (C : Set G) :=
    HahnSeries.support_subset_of_mul_eq (f := (1 : K⟦G⟧)) hqC hne hone
      (mul_inv_cancel₀ hne).symm
  have hprod : ∀ g ∈ ((q⁻¹ : K⟦G⟧) * r).support, g ≤ 0 ∧ g ∉ C := by
    intro g hg
    obtain ⟨a, ha, c', hc', rfl⟩ := HahnSeries.support_mul_subset hg
    obtain ⟨hc0, hcC⟩ := hrsupp c' hc'
    refine ⟨add_nonpos_of_mem_of_nonpos_of_not_mem hC (hinv ha) hc0 hcC, ?_⟩
    intro hab
    exact hcC (by simpa using C.sub_mem hab (hinv ha))
  have hzero : ((q⁻¹ : K⟦G⟧) * r).coeff 0 = 0 := by
    by_contra hnz
    exact (hprod 0 ((HahnSeries.mem_support _ _).mpr hnz)).2 C.zero_mem
  refine ⟨1 + q⁻¹ * r, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases HahnSeries.support_add_subset _ _ hg with h | h
    · have hg0 : g = 0 := by
        simpa only [HahnSeries.support_one, Set.mem_singleton_iff] using h
      exact hg0 ▸ Set.mem_Iic.mpr le_rfl
    · exact Set.mem_Iic.mpr (hprod g h).1
  · rw [HahnSeries.coeff_add, HahnSeries.coeff_one, if_pos rfl, hzero, add_zero]
  · intro g hg hg0
    rcases HahnSeries.support_add_subset _ _ hg with h | h
    · exact absurd (by
        simpa only [HahnSeries.support_one, Set.mem_singleton_iff] using h) hg0
    · exact (hprod g h).2
  · intro g hg hg0
    rcases HahnSeries.support_add_subset _ _ hg with h | h
    · exact absurd (by
        simpa only [HahnSeries.support_one, Set.mem_singleton_iff] using h) hg0
    · obtain ⟨i, hi, j, hj, hij⟩ := HahnSeries.support_mul_subset h
      have hiC : i ∈ C := hinv hi
      have hjr : j ∈ r.support := hj
      have hjb : j ∈ b.support := by
        rw [hr_def, HahnSeries.support_filter] at hjr
        exact hjr.1
      have hjC : j ∉ C := (hrsupp j hj).2
      refine ⟨j, hjb, ?_⟩
      rw [← hij]
      exact (archimedeanClass_add_eq_right_of_mem_of_not_mem hC hiC hjC).symm
  · rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hne, one_mul, hsplit]

end HahnSeries.ConvexRestriction

namespace HahnSeries.CardSuppLTTruncationIntegerPart

open Cardinal

variable {G K : Type*} {κ : Cardinal}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field K] [Fact (aleph0 < κ)]

/-- Restrict a bounded truncation-integer-part series to an exponent subgroup. -/
def restrictToAddSubgroup (Z : Subring K) (C : AddSubgroup G)
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z) :
    HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z := by
  classical
  let xf : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ) :=
    ⟨HahnSeries.filter (· ∈ C) (x : K⟦G⟧),
      (HahnSeries.mem_cardSuppLTSubfield (Γ := G) (R := K) (κ := κ)).mpr
        ((HahnSeries.cardSupp_mono (HahnSeries.support_filter_subset _ _)).trans_lt x.1.2)⟩
  have hxmem := (HahnSeries.mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2
  exact ⟨xf, by
    rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart]
    refine ⟨(HahnSeries.support_filter_subset _ _).trans hxmem.1, ?_⟩
    change (HahnSeries.filter (· ∈ C) (x : K⟦G⟧)).coeff 0 ∈ Z
    rw [HahnSeries.coeff_filter, if_pos C.zero_mem]
    exact hxmem.2⟩

open Classical in
/-- The subgroup restriction package has the expected underlying Hahn series. -/
@[simp]
theorem coe_restrictToAddSubgroup (Z : Subring K) (C : AddSubgroup G)
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z) :
    (restrictToAddSubgroup Z C x : K⟦G⟧) = HahnSeries.filter (· ∈ C) (x : K⟦G⟧) :=
  (rfl)

/-- For nonpositive exponents, a sum lies in a convex subgroup exactly when both summands do. -/
theorem add_mem_iff_of_nonpos {C : AddSubgroup G} (hC : (C : Set G).OrdConnected)
    {i j : G} (hi : i ≤ 0) (hj : j ≤ 0) : i + j ∈ C ↔ i ∈ C ∧ j ∈ C := by
  refine ⟨fun h ↦ ?_, fun h ↦ C.add_mem h.1 h.2⟩
  have hiC : i ∈ C := hC.out h C.zero_mem ⟨by simpa using add_le_add_left hj i, hi⟩
  exact ⟨hiC, by simpa using C.sub_mem h hiC⟩

open Classical in
/-- Restriction to a convex subgroup of the exponents, as a ring endomorphism of the bounded
integer part. -/
@[blueprint "lem:convex-restriction-ring-hom"
  (phase := "Reduction along Archimedean classes")
  (title := "Restriction to a convex subgroup")
  (statement := /--
    Let $C\subseteq G$ be a convex subgroup. Then $\rho_C$ is a ring endomorphism of
    $Z+R((G^{<0}))_\kappa$.
  -/)
  (proof := /--
    Restriction is additive, fixes $1$, and preserves the constant coefficient. For $i,j\le0$,
    convexity gives $i+j\in C$ if and only if $i\in C$ and $j\in C$: indeed $i+j\le i\le0$. Hence
    the coefficient of $\rho_C(xy)$ at $g\in C$ involves only pairs of exponents in $C$, and is the
    coefficient of $\rho_C(x)\rho_C(y)$.
  -/)]
def restrictToAddSubgroupRingHom (Z : Subring K) {C : AddSubgroup G}
    (hC : (C : Set G).OrdConnected) :
    HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z →+*
      HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z where
  toFun := restrictToAddSubgroup Z C
  map_zero' := by
    apply Subtype.ext; apply Subtype.ext
    exact map_zero (HahnSeries.filter (· ∈ C))
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    ext g
    change (HahnSeries.filter (· ∈ C) (1 : K⟦G⟧)).coeff g = (1 : K⟦G⟧).coeff g
    rw [HahnSeries.coeff_filter, HahnSeries.coeff_one]
    split_ifs with h1 h2 <;> simp_all [C.zero_mem]
  map_add' x y := by
    apply Subtype.ext; apply Subtype.ext
    exact HahnSeries.filter_add _ (x : K⟦G⟧) (y : K⟦G⟧)
  map_mul' x y := by
    have h := HahnSeries.Nonpositive.filter_mul_of_add_iff (· ∈ C)
      (fun hi hj ↦ add_mem_iff_of_nonpos hC hi hj)
      (toNonpositiveRingHom Z x) (toNonpositiveRingHom Z y)
    rw [← map_mul] at h
    simp only [coe_toNonpositiveRingHom] at h
    apply Subtype.ext; apply Subtype.ext
    change _ = (restrictToAddSubgroup Z C x : K⟦G⟧) * (restrictToAddSubgroup Z C y : K⟦G⟧)
    simp only [coe_restrictToAddSubgroup]
    exact h

@[simp]
theorem restrictToAddSubgroupRingHom_apply (Z : Subring K) {C : AddSubgroup G}
    (hC : (C : Set G).OrdConnected)
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z) :
    restrictToAddSubgroupRingHom Z hC x = restrictToAddSubgroup Z C x :=
  (rfl)

/-- Restriction to a subgroup is idempotent. -/
@[simp]
theorem restrictToAddSubgroup_restrictToAddSubgroup (Z : Subring K) (C : AddSubgroup G)
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z) :
    restrictToAddSubgroup Z C (restrictToAddSubgroup Z C x) = restrictToAddSubgroup Z C x := by
  classical
  apply Subtype.ext; apply Subtype.ext
  ext g
  simp only [coe_restrictToAddSubgroup, HahnSeries.coeff_filter]
  split_ifs <;> rfl

open Classical in
/-- A nonzero bounded integer-part factor supported in a convex subgroup divides an ambient
bounded integer-part series as soon as it factors the convex restriction. -/
private theorem dvd_of_restriction_factorization
    (Z : Subring K) {C : AddSubgroup G} (hC : (C : Set G).OrdConnected)
    (q w x : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := K) (κ := κ) Z)
    (hqsupp : (q : K⟦G⟧).support ⊆ (C : Set G)) (hq0 : q ≠ 0)
    (heq : HahnSeries.filter (· ∈ C) (x : K⟦G⟧) = (q * w : K⟦G⟧)) :
    q ∣ x := by
  have hqraw : (q : K⟦G⟧) ≠ 0 := fun h ↦ hq0 (Subtype.ext (Subtype.ext h))
  have hxmem := (HahnSeries.mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2
  have hwmem := (HahnSeries.mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp w.2
  obtain ⟨v, hv, hv0, hxv⟩ :=
    HahnSeries.ConvexRestriction.exists_integral_cofactor hC Z hqsupp hqraw
      hxmem.1 hwmem.1 hwmem.2 heq
  let vf : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ) :=
    (x : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) /
      (q : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ))
  have hvraw : (vf : K⟦G⟧) = v := by
    change (x : K⟦G⟧) / (q : K⟦G⟧) = v
    rw [hxv, mul_comm, mul_div_assoc, div_self hqraw, mul_one]
  let vI : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := K) (κ := κ) Z := ⟨vf, by
    rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart, hvraw]
    exact ⟨hv, hv0⟩⟩
  refine ⟨vI, ?_⟩
  apply Subtype.ext
  change (x : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) =
    (q : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) * vf
  have hqfield : (q : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) ≠ 0 :=
    fun h ↦ hq0 (Subtype.ext h)
  rw [mul_comm, div_mul_cancel₀ _ hqfield]

/-- **Divisibility from a convex restriction.** A nonzero element fixed by restriction to a
convex subgroup divides a series as soon as it divides the restriction of that series. -/
@[blueprint "lem:divisibility-from-convex-restriction"
  (phase := "Reduction along Archimedean classes")
  (title := "Divisibility from a convex restriction")
  (statement := /--
    Let $C\subseteq G$ be a convex subgroup and $q,x\in Z+R((G^{<0}))_\kappa$ with $q\ne0$ and
    $\rho_C(q)=q$. If $q\mid\rho_C(x)$, then $q\mid x$.
  -/)
  (proof := /--
    Write $\rho_C(x)=qw$ and divide $x$ by $q$ in the field $R((G))_\kappa$. The inverse of $q$ is
    supported in $C$, so the quotient is $w+q^{-1}(x-\rho_C(x))$. The exponents of the second term
    are sums of an element of $C$ and a nonpositive exponent outside $C$, and convexity keeps every
    such sum strictly negative. Hence the quotient has nonpositive support and the constant
    coefficient of $w$, so it lies in $Z+R((G^{<0}))_\kappa$.
  -/)]
theorem dvd_of_dvd_restrictToAddSubgroup
    (Z : Subring K) {C : AddSubgroup G} (hC : (C : Set G).OrdConnected)
    {q x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z}
    (hq : restrictToAddSubgroup Z C q = q) (hq0 : q ≠ 0)
    (hqx : q ∣ restrictToAddSubgroup Z C x) : q ∣ x := by
  classical
  obtain ⟨w, hw⟩ := hqx
  have hsupp : (q : K⟦G⟧).support ⊆ (C : Set G) := by
    rw [← hq, coe_restrictToAddSubgroup, HahnSeries.support_filter]
    exact fun _ hg ↦ hg.2
  refine dvd_of_restriction_factorization Z hC q w x hsupp hq0 ?_
  rw [← coe_restrictToAddSubgroup, hw]
  rfl

open Classical in
/-- Factor a bounded truncation-integer-part series by its nonzero restriction to a convex
exponent subgroup. The complementary factor remains bounded, has constant coefficient one, and
all its nonzero support exponents lie outside the subgroup in classes met by the original
support. -/
@[blueprint "lem:factorisation-by-convex-restriction"
  (phase := "Reduction along Archimedean classes")
  (title := "Factorisation by a convex restriction")
  (statement := /--
    Let $C\subseteq G$ be a convex subgroup and $b\in Z+R((G^{<0}))_\kappa$ with $u=\rho_C(b)\ne0$.
    Then $b=uw$ for some $w\in Z+R((G^{<0}))_\kappa$ with constant coefficient $1$, all of whose
    nonzero exponents lie outside $C$ and in Archimedean classes met by $b$.
  -/)
  (proof := /--
    Divide $b$ by $u$ in the field $R((G))_\kappa$; the quotient $w$ has constant coefficient $1$.
    Write $b=u+r$ with $\operatorname{supp}(r)$ disjoint from $C$; then $w=1+u^{-1}r$. By convexity
    every exponent of $u^{-1}r$ is the sum of an exponent of $r$ and an element of $C$, which is
    negative, lies outside $C$, and has the Archimedean class of that exponent of $r$. Hence
    $w\in Z+R((G^{<0}))_\kappa$, and $w$ has the stated support.
  -/)]
theorem exists_factorization_by_restriction
    (Z : Subring K) {C : AddSubgroup G} (hC : (C : Set G).OrdConnected)
    (b : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z)
    (hne : HahnSeries.filter (· ∈ C) (b : K⟦G⟧) ≠ 0) :
    ∃ t w : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z,
      (t : K⟦G⟧) = HahnSeries.filter (· ∈ C) (b : K⟦G⟧) ∧
      b = t * w ∧
      (w : K⟦G⟧).coeff 0 = 1 ∧
      (∀ g ∈ (w : K⟦G⟧).support, g ≠ 0 → g ∉ C) ∧
      (∀ g ∈ (w : K⟦G⟧).support, g ≠ 0 →
        ArchimedeanClass.mk g ∈ ArchimedeanClass.mk '' (b : K⟦G⟧).support) := by
  have hbmem := (HahnSeries.mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp b.2
  obtain ⟨wraw, hws, hw0, hwC, hwocc, hfac⟩ :=
    HahnSeries.ConvexRestriction.exists_complementary_factor hC hbmem.1 hne
  let tf : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ) :=
    ⟨HahnSeries.filter (· ∈ C) (b : K⟦G⟧),
      (HahnSeries.mem_cardSuppLTSubfield (Γ := G) (R := K) (κ := κ)).mpr
        ((HahnSeries.cardSupp_mono (HahnSeries.support_filter_subset _ _)).trans_lt b.1.2)⟩
  have ht0 : (tf : K⟦G⟧).coeff 0 = (b : K⟦G⟧).coeff 0 := by
    rw [HahnSeries.coeff_filter, if_pos C.zero_mem]
  let t : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z :=
    ⟨tf, by
      rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart]
      exact ⟨(HahnSeries.support_filter_subset _ _).trans hbmem.1, ht0 ▸ hbmem.2⟩⟩
  have htfield0 : (t : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) ≠ 0 := by
    intro ht
    apply hne
    exact congrArg (fun z : HahnSeries.CardSuppLTField
      (G := G) (R := K) (κ := κ) ↦ (z : K⟦G⟧)) ht
  let wf : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ) :=
    (b : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) /
      (t : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ))
  have hwraw : (wf : K⟦G⟧) = wraw := by
    change (b : K⟦G⟧) / (t : K⟦G⟧) = wraw
    rw [hfac, mul_comm, mul_div_assoc, div_self]
    · exact mul_one _
    · intro ht
      apply htfield0
      exact Subtype.ext ht
  let w : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z :=
    ⟨wf, by
      rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart, hwraw]
      exact ⟨hws, hw0 ▸ Z.one_mem⟩⟩
  refine ⟨t, w, rfl, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change (b : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) =
      (t : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) * wf
    rw [mul_comm, div_mul_cancel₀ _ htfield0]
  · simpa only [w, hwraw] using hw0
  · simpa only [w, hwraw] using hwC
  · simpa only [w, hwraw] using hwocc

/-- **Primality in a convex exponent subgroup.** If an injective additive order embedding has
order-connected range, it carries primal elements of the bounded integer part to primal elements.
-/
theorem isPrimal_mapDomain_of_isPrimal {G H : Type u} {κ : Cardinal.{u}} [Fact (aleph0 < κ)]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [AddCommGroup H] [LinearOrder H] [IsOrderedAddMonoid H]
    (Z : Subring K) (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') (hrange : (Set.range f).OrdConnected)
    {a : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z}
    (ha : IsPrimal a) : IsPrimal (mapDomain f hfi hf Z a) := by
  classical
  let M := mapDomain (κ := κ) f hfi hf Z
  let res := restrictDomain (κ := κ) f hfi hf Z
  have hC : ((f.range : AddSubgroup H) : Set H).OrdConnected := by
    simpa only [AddMonoidHom.coe_range] using hrange
  let ρ := restrictToAddSubgroupRingHom (κ := κ) Z hC
  have hMinj : Function.Injective M := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun z : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := H) (R := K) (κ := κ) Z ↦ (z : K⟦H⟧)) hxy
    simp only [M, coe_mapDomain] at h
    exact HahnSeries.embDomain_injective h
  have hρ (x) : ρ x = M (res x) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [restrictToAddSubgroupRingHom_apply, coe_restrictToAddSubgroup]
    exact (coe_mapDomain_restrictDomain f hfi hf Z x).symm
  have hρM (x) : ρ (M x) = M x := by
    rw [hρ]
    congr 1
    exact restrictDomain_mapDomain f hfi hf Z x
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [map_zero]
    exact isPrimal_zero
  intro x y ⟨q, hq⟩
  have hdvd : a ∣ res x * res y := by
    refine ⟨res q, hMinj ?_⟩
    rw [map_mul, map_mul, ← hρ, ← hρ, ← hρ, ← map_mul, hq, map_mul, hρM]
  obtain ⟨a₁, a₂, ⟨x', hx'⟩, ⟨y', hy'⟩, rfl⟩ := ha hdvd
  have h₁ : a₁ ≠ 0 := left_ne_zero_of_mul ha0
  have h₂ : a₂ ≠ 0 := right_ne_zero_of_mul ha0
  refine ⟨M a₁, M a₂, ?_, ?_, map_mul M a₁ a₂⟩
  · refine dvd_of_dvd_restrictToAddSubgroup Z hC (hρM a₁)
      (fun h ↦ h₁ (hMinj (h.trans (map_zero M).symm))) ⟨M x', ?_⟩
    rw [← restrictToAddSubgroupRingHom_apply Z hC, hρ, hx', map_mul]
  · refine dvd_of_dvd_restrictToAddSubgroup Z hC (hρM a₂)
      (fun h ↦ h₂ (hMinj (h.trans (map_zero M).symm))) ⟨M y', ?_⟩
    rw [← restrictToAddSubgroupRingHom_apply Z hC, hρ, hy', map_mul]

end HahnSeries.CardSuppLTTruncationIntegerPart
