/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Germ.Basic
public import ConwayRefinement.HahnSeries.Translation
public import ConwayRefinement.HahnSeries.Truncation
public import ConwayRefinement.HahnSeries.TruncationIntegerPartPrimal

public import Mathlib.RingTheory.Ideal.Quotient.Operations

import ConwayRefinement.HahnSeries.CantorBendixson.Convolution
import ConwayRefinement.HahnSeries.CantorBendixson.Truncation
import ConwayRefinement.Topology.Order.LeftNeighborhood

/-!
# The germ of a series at an exponent

Let `G` be an ordered abelian group whose additive uniformity is Cauchy complete and `K` a field of
characteristic zero. Let `J` be the ideal of nonpositive series `b ∈ K((G^{≤0}))` whose support is
bounded away from zero, that is, contained in `(-∞, c]` for some `c < 0`; `K((G^{≤0}))/J` is the
ring of germs. In Lean, `J` is `boundedAwayIdeal G K` (`mem_boundedAwayIdeal`).

For an exponent `γ`, the truncation of `b` at `γ` is `b_{|γ}`, the part of `b` with exponents
`≤ γ`, and the translated truncation is `b^{|γ} = t^{-γ} b_{|γ}`, again a nonpositive series.
The germ of `b` at `γ` is the class of `b^{|γ}` modulo `J` (Berarducci 2000, Def. 6.1).

This file proves the basic properties of `germAt`: its value at `0` is the germ of `b`, it
vanishes at positive exponents, it satisfies Berarducci's convolution formula (Berarducci 2000,
Lemma 7.5), the germs of a translated truncation are translated germs, a series has a constant germ
exactly when its germs vanish on a left neighbourhood of `0`, and a series agrees with a series
without germs below a negative cutoff in all germs above the cutoff.
-/

open Set Filter Topology
open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Field K]

/-- The translated truncation `b^{|γ} = t^{-γ} b_{|γ}` of a nonpositive series `b` at an
exponent `γ`. -/
def translatedTruncation (γ : G) (b : Nonpositive G K) : Nonpositive G K :=
  ⟨translate (-γ) (truncLE γ (b : HahnSeries G K)), support_translated_truncLE _ γ⟩

@[simp]
theorem coe_translatedTruncation (γ : G) (b : Nonpositive G K) :
    (translatedTruncation γ b : HahnSeries G K) = translate (-γ) (truncLE γ (b : HahnSeries G K)) :=
  (rfl)

theorem translatedTruncation_add (γ : G) (b b' : Nonpositive G K) :
    translatedTruncation γ (b + b') = translatedTruncation γ b + translatedTruncation γ b' :=
  Subtype.ext (by simp only [coe_translatedTruncation, Subring.coe_add, truncLE_add, map_add])

theorem translatedTruncation_smul (k : K) (γ : G) (b : Nonpositive G K) :
    translatedTruncation γ (k • b) = k • translatedTruncation γ b := by
  apply Subtype.ext
  rw [coe_translatedTruncation, coe_smul, coe_smul, coe_translatedTruncation]
  ext i
  simp only [coeff_translate, HahnSeries.coeff_smul, HahnSeries.coeff_truncLE]
  by_cases hi : i - -γ ≤ γ <;> simp

/-- The translated truncation at `0` is the series itself. -/
theorem translatedTruncation_zero (b : Nonpositive G K) : translatedTruncation 0 b = b :=
  Subtype.ext (by
    rw [coe_translatedTruncation, neg_zero, translate_zero_apply,
      truncLE_eq_self_of_support_subset_Iic (support_subset b)])

/-- Translated truncations compose: for `ζ ≤ 0`, `(b^{|γ})^{|ζ} = b^{|γ + ζ}`. -/
theorem translatedTruncation_translatedTruncation (γ ζ : G) (hζ : ζ ≤ 0) (b : Nonpositive G K) :
    translatedTruncation ζ (translatedTruncation γ b) = translatedTruncation (γ + ζ) b := by
  apply Subtype.ext
  rw [coe_translatedTruncation, coe_translatedTruncation, coe_translatedTruncation]
  ext j
  simp only [coeff_translate, HahnSeries.coeff_truncLE]
  by_cases hj : j ≤ 0
  · have h1 : j - -ζ ≤ ζ := by rw [sub_neg_eq_add]; simpa using hj
    have h2 : j - -(γ + ζ) ≤ γ + ζ := by rw [sub_neg_eq_add]; simpa using hj
    have h3 : j - -ζ - -γ ≤ γ := by
      rw [sub_neg_eq_add, sub_neg_eq_add]
      have := add_le_add_right (add_nonpos hj hζ) γ
      simpa [add_comm, add_left_comm, add_assoc] using this
    rw [if_pos h1, if_pos h2, if_pos h3]
    congr 1
    abel
  · have h1 : ¬ j - -ζ ≤ ζ := by rw [sub_neg_eq_add]; simpa using hj
    have h2 : ¬ j - -(γ + ζ) ≤ γ + ζ := by rw [sub_neg_eq_add]; simpa using hj
    rw [if_neg h1, if_neg h2]

private theorem coeff_coe_C (k : K) (δ : G) :
    ((C k : Nonpositive G K) : HahnSeries G K).coeff δ = if δ = 0 then k else 0 := by
  rw [coe_C, show (HahnSeries.C k : HahnSeries G K) = HahnSeries.single 0 k from rfl,
    HahnSeries.coeff_single]
  by_cases hδ : δ = 0 <;> simp [hδ]

variable [Nontrivial G]

set_option quotPrecheck false in
local notation "𝒥" => boundedAwayIdeal G K

/-- The germ of a nonpositive series `b` at an exponent `γ`: the class of the translated
truncation `b^{|γ}` modulo the ideal of series whose support is bounded away from zero
(Berarducci 2000, Def. 6.1). -/
def germAt (γ : G) : Nonpositive G K →ₗ[K] Nonpositive G K ⧸ 𝒥 where
  toFun b := Ideal.Quotient.mk 𝒥 (translatedTruncation γ b)
  map_add' b b' := by rw [translatedTruncation_add, map_add]
  map_smul' k b := by
    rw [RingHom.id_apply, translatedTruncation_smul]
    exact map_smul (Ideal.Quotient.mkₐ K 𝒥) k _

theorem germAt_apply (γ : G) (b : Nonpositive G K) :
    germAt γ b = Ideal.Quotient.mk 𝒥 (translatedTruncation γ b) := (rfl)

/-- The germ at the exponent `0` is the germ of the series. -/
@[simp]
theorem germAt_zero (b : Nonpositive G K) : germAt 0 b = Ideal.Quotient.mk 𝒥 b := by
  rw [germAt_apply, translatedTruncation_zero]

/-- The germs of the translated truncation `b^{|γ}` at nonpositive exponents are the germs of `b`
translated by `γ`. -/
theorem germAt_translatedTruncation (b : Nonpositive G K) (γ : G) {ζ : G} (hζ : ζ ≤ 0) :
    germAt ζ (translatedTruncation γ b) = germAt (γ + ζ) b := by
  rw [germAt_apply, germAt_apply, translatedTruncation_translatedTruncation γ ζ hζ]

variable [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G]

omit [IsUniformAddGroup G] in
/-- A germ vanishes exactly when the Cantor--Bendixson value of a representative vanishes. -/
theorem mk_eq_zero_iff_cantorBendixsonValue_eq_zero (c : Nonpositive G K) :
    Ideal.Quotient.mk 𝒥 c = 0 ↔ (c : HahnSeries G K).cantorBendixsonValue = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact mem_boundedAwayIdeal_iff_cantorBendixsonValue_eq_zero c

/-- The germ at an exponent outside the closed support vanishes. -/
theorem germAt_eq_zero_of_notMem_closure (γ : G) (b : Nonpositive G K)
    (h : γ ∉ closure (b : HahnSeries G K).support) : germAt γ b = 0 := by
  rw [germAt_apply, mk_eq_zero_iff_cantorBendixsonValue_eq_zero, coe_translatedTruncation,
    cantorBendixsonValue_translated_truncLE, if_neg]
  rwa [mem_closedSupport]

/-- The germ at a positive exponent vanishes. -/
theorem germAt_of_pos (b : Nonpositive G K) {γ : G} (hγ : 0 < γ) : germAt γ b = 0 :=
  germAt_eq_zero_of_notMem_closure γ b fun hmem =>
    absurd (Set.mem_Iic.mp (closure_minimal (support_subset b) isClosed_Iic hmem)) (not_le.mpr hγ)

private theorem mem_image_closedSupportAddFiber (b c : Nonpositive G K) (γ β : G)
    (h : germAt β b ≠ 0 ∧ germAt (γ - β) c ≠ 0) :
    β ∈ ((b : HahnSeries G K).closedSupportAddFiber (c : HahnSeries G K) γ).image Prod.fst := by
  have hb : β ∈ closure (b : HahnSeries G K).support := by
    by_contra hb; exact h.1 (germAt_eq_zero_of_notMem_closure β b hb)
  have hc : γ - β ∈ closure (c : HahnSeries G K).support := by
    by_contra hc; exact h.2 (germAt_eq_zero_of_notMem_closure (γ - β) c hc)
  refine Finset.mem_image.mpr ⟨(β, γ - β), ?_, rfl⟩
  exact (mem_closedSupportAddFiber _ _ γ (β, γ - β)).mpr
    ⟨(mem_closedSupport _ _).mpr hb, (mem_closedSupport _ _).mpr hc, by
      change β + (γ - β) = γ; abel⟩

/-- Only finitely many terms of the convolution formula are nonzero. -/
theorem finite_germAt_ne_zero_and_germAt_ne_zero (b c : Nonpositive G K) (γ : G) :
    {β : G | germAt β b ≠ 0 ∧ germAt (γ - β) c ≠ 0}.Finite :=
  (((b : HahnSeries G K).closedSupportAddFiber (c : HahnSeries G K) γ).image
    Prod.fst).finite_toSet.subset fun β hβ =>
      Finset.mem_coe.mpr (mem_image_closedSupportAddFiber b c γ β hβ)

omit [IsUniformAddGroup G] [Nontrivial G] in
private theorem closure_support_C_subset (k : K) :
    closure ((C k : Nonpositive G K) : HahnSeries G K).support ⊆ ({0} : Set G) := by
  refine closure_minimal (fun x hx => ?_) isClosed_singleton
  rw [HahnSeries.mem_support, coeff_coe_C] at hx
  by_contra hx0
  rw [Set.mem_singleton_iff] at hx0
  rw [if_neg hx0] at hx; exact hx rfl

/-- The germ of a constant at a nonzero exponent vanishes. -/
theorem germAt_algebraMap (k : K) {γ : G} (hγ : γ ≠ 0) :
    germAt γ (algebraMap K (Nonpositive G K) k) = 0 := by
  rw [algebraMap_apply]
  exact germAt_eq_zero_of_notMem_closure _ _ fun hmem => hγ (closure_support_C_subset k hmem)

/-- If the germ of `b` is a constant, the germs of `b` vanish on a left neighbourhood of `0`. -/
theorem exists_germAt_eq_zero_of_mk_mem_range (b : Nonpositive G K)
    (hb : Ideal.Quotient.mk 𝒥 b ∈ Set.range (algebraMap K (Nonpositive G K ⧸ 𝒥))) :
    ∃ ε < (0 : G), ∀ ξ, ε < ξ → ξ < 0 → germAt ξ b = 0 := by
  obtain ⟨k, hk⟩ := hb
  rw [← Ideal.Quotient.mk_algebraMap, algebraMap_apply, eq_comm, Ideal.Quotient.eq] at hk
  obtain ⟨c, hc, hsub⟩ := (mem_boundedAwayIdeal _).mp hk
  refine ⟨c, hc, fun ξ hcξ hξ0 => ?_⟩
  rw [show b = (b - C k) + C k by abel, map_add,
    germAt_eq_zero_of_notMem_closure ξ (b - C k) fun hmem =>
      absurd (Set.mem_Iic.mp (closure_minimal hsub isClosed_Iic hmem)) (not_le.mpr hcξ),
    ← algebraMap_apply, germAt_algebraMap k hξ0.ne, add_zero]

omit [IsUniformAddGroup G] in
private theorem coeff_eq_zero_of_germAt_eq_zero {b : Nonpositive G K} {ξ : G}
    (h : germAt ξ b = 0) : (b : HahnSeries G K).coeff ξ = 0 := by
  rw [germAt_apply, mk_eq_zero_iff_cantorBendixsonValue_eq_zero, coe_translatedTruncation,
    cantorBendixsonValue_eq_zero_iff] at h
  have h0 : (0 : G) ∉ (translate (-ξ) (truncLE ξ (b : HahnSeries G K))).support :=
    fun hh => h (subset_closure hh)
  rw [HahnSeries.mem_support, not_not, coeff_translate, HahnSeries.coeff_truncLE] at h0
  simpa using h0

omit [IsUniformAddGroup G] in
/-- If the germs of `b` vanish on a left neighbourhood of `0`, the germ of `b` is a constant. -/
theorem mk_mem_range_of_germAt_eq_zero (b : Nonpositive G K)
    (h : ∃ ε < (0 : G), ∀ ξ, ε < ξ → ξ < 0 → germAt ξ b = 0) :
    Ideal.Quotient.mk 𝒥 b ∈ Set.range (algebraMap K (Nonpositive G K ⧸ 𝒥)) := by
  obtain ⟨ε, hε, hzero⟩ := h
  refine ⟨(b : HahnSeries G K).coeff 0, ?_⟩
  rw [← Ideal.Quotient.mk_algebraMap, algebraMap_apply, Ideal.Quotient.eq,
    mem_boundedAwayIdeal]
  refine ⟨ε, hε, fun δ hδ => Set.mem_Iic.mpr (le_of_not_gt fun hδε => hδ ?_)⟩
  rw [AddSubgroupClass.coe_sub, HahnSeries.coeff_sub, coeff_coe_C]
  rcases lt_trichotomy δ 0 with hneg | rfl | hpos
  · rw [if_neg hneg.ne, coeff_eq_zero_of_germAt_eq_zero (hzero δ hδε hneg), sub_zero]
  · rw [if_pos rfl, sub_self]
  · have hbz : (b : HahnSeries G K).coeff δ = 0 := by
      by_contra hne
      exact absurd (support_subset b ((HahnSeries.mem_support _ _).mpr hne)) (by simp [hpos])
    rw [hbz, if_neg hpos.ne', sub_self]

/-- Cutting off a series below a negative exponent `ε` keeps its germ and its germs above `ε` and
kills its germs at or below `ε`. -/
theorem exists_germAt_cutoff (b : Nonpositive G K) {ε : G} (hε : ε < 0) :
    ∃ b' : Nonpositive G K, Ideal.Quotient.mk 𝒥 b' = Ideal.Quotient.mk 𝒥 b ∧
      (∀ ξ, ε < ξ → germAt ξ b' = germAt ξ b) ∧ (∀ ξ, ξ ≤ ε → germAt ξ b' = 0) := by
  have hmem : truncGT ε (b : HahnSeries G K) ∈ nonpositiveSubring G K := by
    rw [mem_nonpositiveSubring]
    exact (support_truncGT_subset ε _).trans (support_subset b)
  set b' : Nonpositive G K := ⟨truncGT ε (b : HahnSeries G K), hmem⟩
  have hb'coe : (b' : HahnSeries G K) = truncGT ε (b : HahnSeries G K) := rfl
  have hlowsub : ((b - b' : Nonpositive G K) : HahnSeries G K).support ⊆ Set.Iic ε := by
    intro δ hδ
    refine Set.mem_Iic.mpr (le_of_not_gt fun hδε => hδ ?_)
    rw [AddSubgroupClass.coe_sub, HahnSeries.coeff_sub, hb'coe, HahnSeries.coeff_truncGT,
      if_pos hδε, sub_self]
  refine ⟨b', ?_, fun ξ hξ => ?_, fun ξ hξ => ?_⟩
  · exact (Ideal.Quotient.eq.mpr ((mem_boundedAwayIdeal (b - b')).mpr ⟨ε, hε, hlowsub⟩)).symm
  · have hdiff : germAt ξ (b - b') = 0 := germAt_eq_zero_of_notMem_closure ξ _ fun hmem =>
      absurd (Set.mem_Iic.mp (closure_minimal hlowsub isClosed_Iic hmem)) (not_le.mpr hξ)
    rw [map_sub, sub_eq_zero] at hdiff
    exact hdiff.symm
  · rw [germAt_apply, show translatedTruncation ξ b' = 0 from ?_, map_zero]
    apply Subtype.ext
    rw [coe_translatedTruncation, hb'coe, ZeroMemClass.coe_zero]
    have hzero : truncLE ξ (truncGT ε (b : HahnSeries G K)) = 0 := by
      ext i
      rw [HahnSeries.coeff_truncLE, HahnSeries.coeff_truncGT]
      by_cases hiξ : i ≤ ξ
      · rw [if_pos hiξ, if_neg (not_lt.mpr (hiξ.trans hξ)), HahnSeries.coeff_zero]
      · rw [if_neg hiξ, HahnSeries.coeff_zero]
    rw [hzero, map_zero]

/-- If a series has nonzero Cantor--Bendixson value, its translated truncations at exponents in a
left neighbourhood of `0` have strictly smaller Cantor--Bendixson value. -/
theorem cantorBendixsonValue_translatedTruncation_lt (b : Nonpositive G K)
    (hb : (b : HahnSeries G K).cantorBendixsonValue ≠ 0) :
    ∃ ε < (0 : G), ∀ ξ, ε < ξ → ξ < 0 →
      (translatedTruncation ξ b : HahnSeries G K).cantorBendixsonValue <
        (b : HahnSeries G K).cantorBendixsonValue := by
  have hev : ∀ᶠ ξ in 𝓝[<] (0 : G), ξ ≠ 0 →
      (translate (-ξ) (truncLE ξ (b : HahnSeries G K))).cantorBendixsonValue <
        (b : HahnSeries G K).cantorBendixsonValue :=
    ((b : HahnSeries G K).eventually_value_translated_truncLE_lt hb).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨ε, hε, hall⟩ := (eventually_nhdsLT_iff_exists).mp hev
  exact ⟨ε, hε, fun ξ hεξ hξ0 => hall ξ hεξ hξ0 hξ0.ne⟩

variable [CompleteSpace G]

/-- The translated truncation of a product differs from the finite convolution sum of translated
truncations by a series of Cantor--Bendixson value zero. -/
private theorem cantorBendixsonValue_translatedTruncation_mul_sub_sum (b c : Nonpositive G K)
    (γ : G) :
    ((translatedTruncation γ (b * c) -
        ∑ p ∈ (b : HahnSeries G K).closedSupportAddFiber (c : HahnSeries G K) γ,
          translatedTruncation p.1 b * translatedTruncation p.2 c : Nonpositive G K) :
        HahnSeries G K).cantorBendixsonValue = 0 := by
  rw [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, coe_translatedTruncation]
  simp only [Subring.coe_mul, coe_translatedTruncation]
  exact (b : HahnSeries G K).cantorBendixsonValue_convolution_error (c : HahnSeries G K) γ

/-- The germ of a product at `γ` is the finite sum over the closed-support addition fibre. -/
private theorem germAt_mul_eq_sum_closedSupportAddFiber (b c : Nonpositive G K) (γ : G) :
    germAt γ (b * c) =
      ∑ p ∈ (b : HahnSeries G K).closedSupportAddFiber (c : HahnSeries G K) γ,
        germAt p.1 b * germAt (γ - p.1) c := by
  have hD := (mk_eq_zero_iff_cantorBendixsonValue_eq_zero _).mpr
    (cantorBendixsonValue_translatedTruncation_mul_sub_sum b c γ)
  rw [map_sub, sub_eq_zero, map_sum] at hD
  rw [germAt_apply, hD]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp2 : p.2 = γ - p.1 := eq_sub_of_add_eq'
    ((mem_closedSupportAddFiber (b : HahnSeries G K) (c : HahnSeries G K) γ p).mp hp).2.2
  rw [map_mul, hp2, germAt_apply, germAt_apply]

/-- **Convolution formula** (Berarducci 2000, Lemma 7.5): the germ of a product at `γ` is
`∑_β germAt β b * germAt (γ - β) c`. -/
theorem germAt_mul (b c : Nonpositive G K) (γ : G) :
    germAt γ (b * c) = ∑ᶠ β, germAt β b * germAt (γ - β) c := by
  set F := (b : HahnSeries G K).closedSupportAddFiber (c : HahnSeries G K) γ with hF
  have hsupp : Function.support (fun β => germAt β b * germAt (γ - β) c) ⊆ ↑(F.image Prod.fst) :=
    fun β hβ => Finset.mem_coe.mpr (mem_image_closedSupportAddFiber b c γ β
      ⟨left_ne_zero_of_mul hβ, right_ne_zero_of_mul hβ⟩)
  rw [germAt_mul_eq_sum_closedSupportAddFiber, finsum_eq_finsetSum_of_support_subset _ hsupp,
    Finset.sum_image fun p hp q hq hpq => ?_]
  have hp := (mem_closedSupportAddFiber (b : HahnSeries G K) (c : HahnSeries G K) γ p).mp hp
  have hq := (mem_closedSupportAddFiber (b : HahnSeries G K) (c : HahnSeries G K) γ q).mp hq
  refine Prod.ext hpq ?_
  have : p.1 + p.2 = q.1 + q.2 := by rw [hp.2.2, hq.2.2]
  rw [hpq] at this; exact add_left_cancel this

end HahnSeries.Nonpositive
