/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.SupportArchimedeanClasses
public import ConwayRefinement.HahnSeries.IntegerPart.FiniteClassPrimality
public import ConwayRefinement.HahnSeries.IntegerPart.Refinement.SupportClassFactorization
public import ConwayRefinement.HahnSeries.IntegerPart.Refinement.TailQuotientGerms
public import ConwayRefinement.HahnSeries.CardinalTruncationDomainEmbedding
public import ConwayRefinement.HahnSeries.CharZero
public import ConwayRefinement.Algebra.Divisibility.PrimalPreimage
public import ConwayRefinement.Algebra.Divisibility.RetractionPrimality

import ConwayRefinement.Blueprint

/-!
# Primality from common-tail quotients

The induction rank is the order type of the Archimedean classes met by the non-zero support. A
supplied theorem handles the case in which this set is finite. At every infinite rank, the classes
split into a non-zero limit initial segment `T₀` and a finite final segment. Let `C` be the common
tail below `T₀`, `Γ = G ⧸ C`, `L = R((C))_κ` and `D = Z + R((C^{<0}))_κ`. Regrouping exponents
along `C` identifies `Z + R((G^{<0}))_κ` with the `D + M` construction `D + L((Γ^{<0}))_κ` inside
`L((Γ^{≤0}))_κ`. The constant term meets only finitely many classes, so it is primal in `D`, and
the fraction-field hypothesis on `D` handles a zero constant term. Primality in
`L((Γ^{≤0}))_κ` follows from refinement in its ring of germs, which is a polynomial ring when `Γ`
is Cauchy complete: restriction to the closed ball of a small quotient class met by the support
refines every divisibility relation exactly, and the complementary factor has strictly smaller
rank, hence is primal by induction.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open HahnSeries.CardSuppLTTruncationIntegerPart
open scoped HahnSeries

universe u v w

namespace HahnSeries.CardSuppLTTruncationIntegerPart

section Regrouping

variable {G : Type u} {R : Type v} {K : Type w} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field K] [Module K G] [Field R]
variable [Fact (Cardinal.aleph0 < κ)] [Fact κ.IsRegular]

open Classical in
/-- Regrouping along a convex subspace `P` commutes with restriction to the preimage of a
subgroup of `G ⧸ P`. -/
theorem convexQuotientSplit_restrictToAddSubgroup_comap
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (D : AddSubgroup (G ⧸ P))
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z
        (restrictToAddSubgroup Z (D.comap P.mkQ.toAddMonoidHom) x) =
      restrictToAddSubgroup (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) D
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x) := by
  let t := restrictToAddSubgroup Z (D.comap P.mkQ.toAddMonoidHom) x
  apply Subtype.ext
  apply Subtype.ext
  ext z p
  rw [coe_restrictToAddSubgroup (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) D,
    HahnSeries.coeff_filter]
  have htcoeff := congrArg
    (fun y : (R⟦P⟧)⟦G ⧸ P⟧ ↦ (y.coeff z).coeff p)
    (boundedOuterCoefficientInclusion_split P t.1)
  rw [boundedOuterCoefficientInclusion_coeff] at htcoeff
  have hz : ((convexQuotientSplitRingEquiv P (t : R⟦G⟧)).coeff z).coeff p =
      (if z ∈ D then (convexQuotientSplitRingEquiv P (x : R⟦G⟧)).coeff z else 0).coeff p := by
    rw [coe_restrictToAddSubgroup, convexQuotientSplitRingEquiv_filter_comap,
      HahnSeries.coeff_filter]
  rw [coe_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z t]
  refine htcoeff.trans (hz.trans ?_)
  split_ifs
  · have hxcoeff := congrArg
      (fun y : (R⟦P⟧)⟦G ⧸ P⟧ ↦ (y.coeff z).coeff p)
      (boundedOuterCoefficientInclusion_split P x.1)
    rw [boundedOuterCoefficientInclusion_coeff] at hxcoeff
    rw [coe_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x]
    exact hxcoeff.symm
  · rfl

/-- In the `D + M` presentation inside bounded nonpositive series, regrouping turns restriction to
the preimage of a quotient subgroup into restriction to that subgroup. -/
theorem convexQuotientSplit_restrictToAddSubgroup_comap_ambient
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (D : AddSubgroup (G ⧸ P))
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    ((CardSuppLTNonpositive.truncationIntegerPartEquivResidueSubring
        (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z)
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z
          (restrictToAddSubgroup Z (D.comap P.mkQ.toAddMonoidHom) x)) :
        Subring.residueSubring CardSuppLTNonpositive.constantCoeffAlgHom _) :
          CardSuppLTNonpositive (G := G ⧸ P)
            (L := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)) =
      restrictToAddSubgroup ⊤ D
        ((CardSuppLTNonpositive.truncationIntegerPartEquivResidueSubring
          (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z)
          (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x) :
          Subring.residueSubring CardSuppLTNonpositive.constantCoeffAlgHom _) :
            CardSuppLTNonpositive (G := G ⧸ P)
              (L := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)) := by
  rw [convexQuotientSplit_restrictToAddSubgroup_comap]
  apply Subtype.ext
  apply Subtype.ext
  simp only [CardSuppLTNonpositive.coe_truncationIntegerPartEquivResidueSubring,
    coe_restrictToAddSubgroup]

/-- Regrouping preserves a nonzero constant coefficient. -/
theorem coeff_zero_convexQuotientSplit_ne_zero
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hx : (x : R⟦G⟧).coeff 0 ≠ 0) :
    ((cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x :
      CardSuppLTField (G := G ⧸ P) (R := CardSuppLTField (G := P) (R := R) (κ := κ))
        (κ := κ)) : (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).coeff 0 ≠ 0 := by
  intro h0
  apply hx
  rw [coe_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv] at h0
  have h := congrArg (fun y : (R⟦P⟧)⟦G ⧸ P⟧ ↦ (y.coeff 0).coeff 0)
    (boundedOuterCoefficientInclusion_split P x.1)
  simp only [boundedOuterCoefficientInclusion_coeff, convexQuotientSplitRingEquiv_coeff] at h
  rw [h0, Submodule.quotientLexEquiv_apply] at h
  change _ = (x : R⟦G⟧).coeff (Submodule.quotientProdLinearEquiv P (0, 0)) at h
  rw [Submodule.quotientProdLinearEquiv_zero_left] at h
  simpa using h.symm

/-- Regrouping into the `D + M` presentation, as a ring homomorphism into bounded nonpositive
series over the quotient. -/
def regroupAmbient (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R) :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z →+*
      CardSuppLTNonpositive (G := G ⧸ P)
        (L := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ) :=
  ((Subring.residueSubring CardSuppLTNonpositive.constantCoeffAlgHom
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z)).subtype.comp
    (CardSuppLTNonpositive.truncationIntegerPartEquivResidueSubring
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z)).toRingHom).comp
    (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z).toRingHom

theorem regroupAmbient_apply (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    regroupAmbient P Z x =
      ((CardSuppLTNonpositive.truncationIntegerPartEquivResidueSubring
        (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z)
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x) :
        Subring.residueSubring CardSuppLTNonpositive.constantCoeffAlgHom _) :
          CardSuppLTNonpositive (G := G ⧸ P)
            (L := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)) :=
  (rfl)

theorem regroupAmbient_injective (P : Submodule K G) [P.toAddSubgroup.IsConvex]
    (Z : Subring R) : Function.Injective (regroupAmbient (κ := κ) P Z) :=
  (Subtype.val_injective.comp (RingEquiv.injective _)).comp (RingEquiv.injective _)

/-- If `x = t w` where `t` is the restriction of `x` to the preimage of a subgroup `B` of
`G ⧸ P`, then the regrouped series is its restriction to `B` times the regrouping of `w`. -/
theorem regroupAmbient_eq_restrict_mul
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (B : AddSubgroup (G ⧸ P))
    (x t w : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (ht : restrictToAddSubgroup Z (B.comap P.mkQ.toAddMonoidHom) x = t)
    (hfac : x = t * w) :
    regroupAmbient P Z x =
      restrictToAddSubgroup ⊤ B (regroupAmbient P Z x) * regroupAmbient P Z w := by
  have hρt : regroupAmbient P Z t = restrictToAddSubgroup ⊤ B (regroupAmbient P Z x) := by
    rw [← ht]
    exact convexQuotientSplit_restrictToAddSubgroup_comap_ambient P Z B x
  rw [← hρt, ← map_mul, ← hfac]

/-- A primal series with nonzero constant coefficient stays primal after regrouping into
`L((Γ^{≤0}))_κ`. -/
theorem isPrimal_regroupAmbient
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (w : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hw : IsPrimal w) (hw0 : (w : R⟦G⟧).coeff 0 ≠ 0) :
    IsPrimal (regroupAmbient P Z w) :=
  CardSuppLTNonpositive.isPrimal_ambient_of_isPrimal _ _
    ((RingEquiv.isPrimal_iff _ w).mpr hw) (coeff_zero_convexQuotientSplit_ne_zero P Z w hw0)

/-- If `x ≠ 0` and `x = t w` where `t` is the restriction of `x` to the preimage of a subgroup
`B` of `G ⧸ P` and `w` is primal with nonzero constant coefficient, then in `L((Γ^{≤0}))_κ` the
regrouped series is its nonzero restriction to `B` times a primal factor. -/
theorem restriction_mul_isPrimal_of_factorization
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (B : AddSubgroup (G ⧸ P))
    (x t w : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hx0 : x ≠ 0) (ht : restrictToAddSubgroup Z (B.comap P.mkQ.toAddMonoidHom) x = t)
    (hfac : x = t * w) (hw : IsPrimal w) (hw0 : (w : R⟦G⟧).coeff 0 ≠ 0) :
    restrictToAddSubgroup ⊤ B (regroupAmbient P Z x) ≠ 0 ∧
      ∃ v, regroupAmbient P Z x = restrictToAddSubgroup ⊤ B (regroupAmbient P Z x) * v ∧
        IsPrimal v := by
  have hy := regroupAmbient_eq_restrict_mul P Z B x t w ht hfac
  have hy0 : regroupAmbient P Z x ≠ 0 := fun h ↦
    hx0 (regroupAmbient_injective P Z (h.trans (map_zero (regroupAmbient (κ := κ) P Z)).symm))
  refine ⟨fun h0 ↦ hy0 ?_, _, hy, isPrimal_regroupAmbient P Z w hw hw0⟩
  rw [hy, h0, zero_mul]

end Regrouping


open Classical in
/-- At a quotient class met by the support, the regrouped series is its closed-ball restriction
times a primal factor, when every series of smaller support-class order type is primal. -/
private theorem restriction_mul_isPrimal_at_support_class
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R] {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R) (T : Set (FiniteArchimedeanClass G))
    (q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T))
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hqocc : q.1 ∈ ArchimedeanClass.mk ''
      (Submodule.Quotient.mk (p := FiniteArchimedeanClass.tailSubmodule ℚ T) ''
        (x : HahnSeries G R).support))
    (ih : ∀ w : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z w)).orderType <
        (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z x)).orderType → IsPrimal w) :
    ∃ t w : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      restrictToAddSubgroup Z ((FiniteArchimedeanClass.closedBallAddSubgroup q).comap
        (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ.toAddMonoidHom) x = t ∧
      x = t * w ∧ IsPrimal w ∧ (w : R⟦G⟧).coeff 0 ≠ 0 := by
  let C : AddSubgroup G := (FiniteArchimedeanClass.closedBallAddSubgroup q).comap
    (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ.toAddMonoidHom
  have hfilter0 : HahnSeries.filter (· ∈ C) (x : HahnSeries G R) ≠ 0 := by
    obtain ⟨z, ⟨r, hr, hqr⟩, hzq⟩ := hqocc
    intro hzero
    have hcoeff := congrArg (fun y : HahnSeries G R ↦ y.coeff r) hzero
    rw [HahnSeries.coeff_filter, if_pos] at hcoeff
    · exact (HahnSeries.mem_support _ _).mp hr hcoeff
    · change (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ r ∈
        FiniteArchimedeanClass.closedBallAddSubgroup q
      apply FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff.mpr
      intro _hr0
      change q.1 ≤ ArchimedeanClass.mk ((FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ r)
      change (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ r = z at hqr
      rw [hqr, hzq]
  have hfactor := exists_factor_with_smaller_support_class_orderType Z T q x hqocc hfilter0
  obtain ⟨t, w, ht, hfac, hw1, hrank⟩ := hfactor
  refine ⟨t, w, ?_, hfac, ih w hrank, by rw [hw1]; exact one_ne_zero⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (coe_restrictToAddSubgroup Z C x).trans ht.symm

private theorem limit_family_exists_gt {G : Type u}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (T₀ : Set (ArchimedeanClass G)) (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b) :
    ∀ c ∈ {c : FiniteArchimedeanClass G | c.1 ∈ T₀},
      ∃ d ∈ {c : FiniteArchimedeanClass G | c.1 ∈ T₀}, c < d := by
  intro c hc
  obtain ⟨d, hd, hcd⟩ := hT₀gt c.1 hc
  obtain ⟨e, _he, hde⟩ := hT₀gt d hd
  exact ⟨⟨d, ne_top_of_lt hde⟩, hd, hcd⟩

private theorem limit_family_card_lt {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Field R] {κ : Cardinal} [Fact (ℵ₀ < κ)] {Z : Subring R}
    (T₀ T₁ : Set (ArchimedeanClass G))
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hxclasses : ArchimedeanClass.mk '' (x : HahnSeries G R).support = T₀ ∪ T₁) :
    #{c : FiniteArchimedeanClass G | c.1 ∈ T₀} < κ := by
  calc
    #{c : FiniteArchimedeanClass G | c.1 ∈ T₀} =
        #(Subtype.val '' {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) :=
      (Cardinal.mk_image_eq Subtype.val_injective).symm
    _ ≤ #T₀ := Cardinal.mk_le_mk_of_subset fun _ h ↦ by
      obtain ⟨c, hc, rfl⟩ := h
      exact hc
    _ ≤ #(ArchimedeanClass.mk '' (x : HahnSeries G R).support) :=
      Cardinal.mk_le_mk_of_subset fun c hc ↦ by
        rw [hxclasses]
        exact Or.inl hc
    _ ≤ #(x : HahnSeries G R).support := Cardinal.mk_image_le
    _ < κ := x.1.2

/-- Under the hypotheses of the limit step, the regrouped series is primal in
`L((Γ^{≤0}))_κ`. -/
private theorem isPrimal_regroupAmbient_of_limit_tail
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R] [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R)
    (T₀ T₁ : Set (ArchimedeanClass G)) (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b)
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hxclasses : ArchimedeanClass.mk '' (x : HahnSeries G R).support = T₀ ∪ T₁)
    [Nonempty {c : FiniteArchimedeanClass G | c.1 ∈ T₀}]
    [CompleteSpace (FiniteArchimedeanClass.TailQuotient
      {c : FiniteArchimedeanClass G | c.1 ∈ T₀})]
    (hx0 : x ≠ 0)
    (ih : ∀ w : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z w)).orderType <
        (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z x)).orderType → IsPrimal w) :
    IsPrimal (regroupAmbient
      (FiniteArchimedeanClass.tailSubmodule ℚ {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) Z x) := by
  let T : Set (FiniteArchimedeanClass G) := {c | c.1 ∈ T₀}
  let P := FiniteArchimedeanClass.tailSubmodule ℚ T
  have hT := limit_family_exists_gt T₀ hT₀gt
  haveI : Nonempty (FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T)) := by
    letI := FiniteArchimedeanClass.nontrivial_tailQuotient T hT
    obtain ⟨y, hy⟩ := exists_ne (0 : FiniteArchimedeanClass.TailQuotient T)
    exact ⟨FiniteArchimedeanClass.mk y hy⟩
  refine CardSuppLTNonpositive.isPrimal_of_frequently_restriction_mul_isPrimal T
    hT (limit_family_card_lt T₀ T₁ x hxclasses) ?_
  rw [Filter.frequently_atTop]
  intro q₀
  have hU : IsCofinal {q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T) |
      q.1 ∈ ArchimedeanClass.mk ''
        (HahnSeries.convexQuotientSplitRingEquiv P (x : HahnSeries G R)).support} :=
    HahnSeries.isCofinal_supportArchimedeanClasses_convexQuotientSplit
      T₀ T₁ hT₀gt (x : HahnSeries G R) hxclasses
  have hq₀ : ∃ q ∈ {q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T) |
      q.1 ∈ ArchimedeanClass.mk ''
        (HahnSeries.convexQuotientSplitRingEquiv P (x : HahnSeries G R)).support}, q₀ ≤ q :=
    hU q₀
  obtain ⟨q, hqU, hq₀q⟩ := hq₀
  have hqocc : q.1 ∈ ArchimedeanClass.mk ''
      (Submodule.Quotient.mk (p := P) '' (x : HahnSeries G R).support) := by
    obtain ⟨z, hz, hzq⟩ := hqU
    have hsupp := HahnSeries.support_convexQuotientSplitRingEquiv P (x : HahnSeries G R)
    rw [hsupp] at hz
    obtain ⟨r, hr, hzr⟩ := hz
    exact ⟨z, ⟨r, hr, hzr⟩, hzq⟩
  have hfactor := restriction_mul_isPrimal_at_support_class Z T q x hqocc ih
  obtain ⟨t, w, ht, hfac, hw, hw0⟩ := hfactor
  exact ⟨q, hq₀q, restriction_mul_isPrimal_of_factorization P Z _ x t w hx0 ht hfac hw hw0⟩

/-- **The limit step.** Suppose the Archimedean classes met by the support of `x` are `T₀ ∪ T₁`
with `T₁` finite and `T₀` without least member in the magnitude order. If the quotient by the
common tail below `T₀` is Cauchy complete, the bounded Hahn field on that tail is the fraction
field of its bounded integer part, finite-class primality holds, and every series of smaller
support-class order type is primal, then `x` is primal. -/
@[blueprint "thm:limit-tail-step"
  (phase := "Refinement over Archimedean classes")
  (title := "Primality at a limit of Archimedean classes")
  (statement := /--
    Let $G$ be an ordered rational vector space, $R$ a field of characteristic
    zero, $\kappa>\aleph_0$ a regular cardinal, and $Z\subseteq R$ a subring.
    Assume that every element of $Z+R((G^{<0}))_\kappa$ meeting only finitely
    many Archimedean classes is primal.  Let $x\in Z+R((G^{<0}))_\kappa$ and
    suppose the Archimedean classes met by its support are $T_0\cup T_1$,
    where $T_1$ is finite and $T_0$ contains a nonzero class and has no least
    member in the magnitude order.  Let $C$ be the common tail below $T_0$.
    Assume that $G/C$ is Cauchy complete for its additive uniformity, that
    $R((C))_\kappa$ is the fraction field of $Z+R((C^{<0}))_\kappa$, and that
    every element of $Z+R((G^{<0}))_\kappa$ whose nonzero Archimedean support
    classes have smaller order type than those of $x$ is primal.  Then $x$ is
    primal.
  -/)
  (proof := /--
    Put $\Gamma=G/C$, $L=R((C))_\kappa$ and $D=Z+R((C^{<0}))_\kappa$.
    Regrouping exponents along $C$ identifies $Z+R((G^{<0}))_\kappa$ with
    $D+L((\Gamma^{<0}))_\kappa$, the inverse image of $D$ under the constant
    coefficient on $T=L((\Gamma^{\le0}))_\kappa$.  The constant coefficient
    of $x$ is the restriction of $x$ to $C$; it meets only classes of $T_1$, so
    it is primal in $D$ by \ref{lem:convex-support-of-factors} and the
    finite-class hypothesis.  By \ref{lem:primality-in-d-plus-m} it remains to
    show that $x$ is primal in $T$.

    Apply \ref{lem:primality-from-germs-and-restrictions} in $T$ with $J$ the
    series bounded away from zero, and with the restrictions
    $\rho_q$ to closed Archimedean balls of $\Gamma$, which are ring
    endomorphisms by \ref{lem:convex-restriction-ring-hom}.  Every element of
    $J$ is killed by $\rho_q$ for all sufficiently small $q$;
    \ref{lem:divisibility-from-convex-restriction} tests divisibility after
    $\rho_q$; and \ref{thm:complete-tail-quotient-refinement} refines every
    divisibility relation modulo $J$.  The classes of $\Gamma$ met by the
    support of $x$ are arbitrarily small.  For such a class $q$,
    \ref{lem:support-class-factorisation} gives $x=tw$ with $t$ the
    restriction of $x$ to the inverse image of the closed ball of $q$, so that
    $t$ corresponds to $\rho_q(x)$, and with $w$ of constant coefficient $1$
    and smaller support-class order type.  By hypothesis $w$ is primal in
    $D+L((\Gamma^{<0}))_\kappa$; as its constant coefficient is a unit, it is
    primal in $T$.
  -/)]
theorem isPrimal_of_limit_tail
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R] [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R)
    (hfinite : ∀ y : HahnSeries.cardSuppLTTruncationIntegerPart
        (G := G) (R := R) (κ := κ) Z,
      (ArchimedeanClass.mk '' (y : HahnSeries G R).support).Finite → IsPrimal y)
    (T₀ T₁ : Set (ArchimedeanClass G))
    (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b) (hT₁ : T₁.Finite)
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hxclasses : ArchimedeanClass.mk '' (x : HahnSeries G R).support = T₀ ∪ T₁)
    [Nonempty {c : FiniteArchimedeanClass G | c.1 ∈ T₀}]
    [CompleteSpace (FiniteArchimedeanClass.TailQuotient
      {c : FiniteArchimedeanClass G | c.1 ∈ T₀})]
    (htailfrac : Subring.fracSubring (HahnSeries.cardSuppLTTruncationIntegerPart
      (G := FiniteArchimedeanClass.tailSubmodule ℚ {c : FiniteArchimedeanClass G | c.1 ∈ T₀})
      (R := R) (κ := κ) Z) = ⊤)
    (ih : ∀ w : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z w)).orderType <
        (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z x)).orderType → IsPrimal w) :
    IsPrimal x := by
  by_cases hx0 : x = 0
  · rw [hx0]
    exact isPrimal_zero
  have h := isPrimal_regroupAmbient_of_limit_tail Z T₀ T₁ hT₀gt x hxclasses hx0 ih
  rw [regroupAmbient_apply] at h
  rw [← RingEquiv.isPrimal_iff (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
    (FiniteArchimedeanClass.tailSubmodule ℚ {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) Z)]
  exact CardSuppLTNonpositive.isPrimal_of_isPrimal_ambient _ _ h
    (isPrimal_coeff_zero_convexQuotientSplitRingEquiv_of_ambient_finiteClasses
      Z hfinite T₀ T₁ hT₀gt hT₁ x hxclasses.le) htailfrac

/-- The common-tail hypotheses extend finite-class primality to every cardinal-bounded Hahn
integer-part series. -/
@[blueprint "thm:limit-tail-primality"
  (phase := "Refinement over Archimedean classes")
  (title := "Transfinite extension of finite-class primality")
  (statement := /--
    Let $G$ be an ordered rational vector space, $R$ a field of characteristic
    zero, $\kappa>\aleph_0$ a regular cardinal, and $Z\subseteq R$ a subring.
    Assume that every element of $Z+R((G^{<0}))_\kappa$ meeting only finitely
    many Archimedean classes is primal.  For every nonempty set $T$ of nonzero
    Archimedean classes with no least member in the magnitude order and
    cardinality less than $\kappa$, assume that the quotient by the common tail
    below $T$ is Cauchy complete for its additive uniformity and that the
    bounded Hahn field on the common tail is the fraction field of its bounded
    Hahn integer part.  Then every element of
    $Z+R((G^{<0}))_\kappa$ is primal.
  -/)
  (proof := /--
    Induct on the order type of the nonzero Archimedean support classes, which
    form a well-ordered set.  If the support meets finitely many classes, use
    the hypothesis.  Otherwise split the class set into a nonzero limit initial
    segment and a finite final segment and apply \ref{thm:limit-tail-step}; its
    induction hypothesis is the hypothesis of the ordinal induction.
  -/)]
theorem isPrimal_of_finite_classes_and_limit_tail_conditions
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R] [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R)
    (hfinite : ∀ y : HahnSeries.cardSuppLTTruncationIntegerPart
        (G := G) (R := R) (κ := κ) Z,
      (ArchimedeanClass.mk '' (y : HahnSeries G R).support).Finite → IsPrimal y)
    (hcomplete : ∀ (T : Set (FiniteArchimedeanClass G)), T.Nonempty →
      (∀ c ∈ T, ∃ d ∈ T, c < d) →
      (#T < κ) →
      Nonempty (CompleteSpace (FiniteArchimedeanClass.TailQuotient T)))
    (htailfrac : ∀ (T : Set (FiniteArchimedeanClass G)), T.Nonempty →
      (∀ c ∈ T, ∃ d ∈ T, c < d) →
      (#T < κ) →
      Subring.fracSubring (HahnSeries.cardSuppLTTruncationIntegerPart
        (G := FiniteArchimedeanClass.tailSubmodule ℚ T)
        (R := R) (κ := κ) Z) = ⊤)
    (a : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z) : IsPrimal a := by
  let S := HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z
  let rank : S → Ordinal := fun x ↦
    (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
      (toNonpositiveRingHom Z x)).orderType
  have hind : ∀ o : Ordinal, ∀ x : S, rank x = o → IsPrimal x := by
    intro o
    induction o using WellFoundedLT.induction with
    | ind o ih =>
        intro x hxrank
        rcases (toNonpositiveRingHom Z x).isPWO_supportArchimedeanClasses
            |>.finite_or_exists_limit_initial_finite_final
            with hfiniteClasses | ⟨T₀, T₁, hT₀pwo, _hT₁pwo, _hT₀sub, _hT₁sub, _hbefore,
              hT₀limit, hT₁finite, hclasses⟩
        · apply hfinite x
          simpa only [coe_toNonpositiveRingHom] using hfiniteClasses
        · have hT₀gt : ∀ c ∈ T₀, ∃ d ∈ T₀, c < d := fun c hc ↦
            hT₀pwo.exists_gt_of_isSuccLimit_orderType hT₀limit hc
          have hxclasses : ArchimedeanClass.mk '' (x : HahnSeries G R).support = T₀ ∪ T₁ := by
            simpa only [coe_toNonpositiveRingHom] using hclasses
          let T : Set (FiniteArchimedeanClass G) := {c | c.1 ∈ T₀}
          have hTne : T.Nonempty := by
            have hT₀ne : T₀.Nonempty := by
              by_contra hne
              rw [Set.not_nonempty_iff_eq_empty] at hne
              exact hT₀limit.ne_bot (hT₀pwo.orderType_eq_zero.mpr hne)
            obtain ⟨c, hc⟩ := hT₀ne
            obtain ⟨d, _hd, hcd⟩ := hT₀gt c hc
            exact ⟨⟨c, ne_top_of_lt hcd⟩, hc⟩
          letI : Nonempty T := hTne.to_subtype
          have hTgt := limit_family_exists_gt T₀ hT₀gt
          have hTcard := limit_family_card_lt T₀ T₁ x hxclasses
          letI : CompleteSpace (FiniteArchimedeanClass.TailQuotient T) :=
            Classical.choice (hcomplete T hTne hTgt hTcard)
          exact isPrimal_of_limit_tail Z hfinite T₀ T₁ hT₀gt hT₁finite x hxclasses
            (htailfrac T hTne hTgt hTcard)
            (fun w hw ↦ ih (rank w) (hxrank ▸ hw) w rfl)
  exact hind (rank a) a rfl

/-- Conditions `(A1)`--`(A3)` at finite Archimedean classes, together with the two
common-tail hypotheses at limit families, make every element of the bounded Hahn integer part
primal. -/
@[blueprint "thm:hahn-integer-part-primality"
  (phase := "Refinement over Archimedean classes")
  (title := "Primality under finite-class and common-tail hypotheses")
  (statement := /--
    Let $G$ be an ordered rational vector space, $R$ a field of characteristic
    zero, $\kappa>\aleph_0$ a regular cardinal, and $Z\subseteq R$ a
    pre-Schreier subring.  At every nonzero Archimedean class, choose an
    additive complement to the strict inner ball that is order additively
    isomorphic to $\mathbb R$.  Assume that each strict inner ball either has
    cofinality at least $\kappa$, or is zero and every element of $R$ is a
    fraction of elements of $Z$.

    For every nonempty set $T$ of fewer than $\kappa$ nonzero Archimedean
    classes having no least member in the magnitude order, let $H_T$ be the
    rational subspace of exponents lying beyond every class in $T$.  Assume
    that $G/H_T$ is Cauchy complete for its additive uniformity and that the
    bounded Hahn field on $H_T$ is the fraction field of its bounded Hahn
    integer part.  Then every element of
    $Z+R((G^{<0}))_\kappa$ is primal.
  -/)
  (proof := /--
    By \ref{thm:finite-support-classes-primality}, assumptions
    $(A1)_\sigma$--$(A3)$ make every series meeting finitely many Archimedean
    classes primal.  Apply \ref{thm:limit-tail-primality} to extend this result
    to arbitrary support-class order type.
  -/)]
theorem isPrimal_of_finite_class_assumptions_and_limit_tail_conditions
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [IsOrderedModule ℚ G]
    [Field R] [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R) [DecompositionMonoid Z]
    (s : HahnEmbedding.ArchimedeanStrata ℚ G)
    (hA1 : ∀ c : FiniteArchimedeanClass G, LM24.AssumptionA1AtFiniteClass s c)
    (hA2 : ∀ c : FiniteArchimedeanClass G,
      LM24.AssumptionA2AtFiniteClass (K := ℚ) κ Z c)
    (hcomplete : ∀ (T : Set (FiniteArchimedeanClass G)), T.Nonempty →
      (∀ c ∈ T, ∃ d ∈ T, c < d) →
      (#T < κ) →
      Nonempty (CompleteSpace (FiniteArchimedeanClass.TailQuotient T)))
    (htailfrac : ∀ (T : Set (FiniteArchimedeanClass G)), T.Nonempty →
      (∀ c ∈ T, ∃ d ∈ T, c < d) →
      (#T < κ) →
      Subring.fracSubring (HahnSeries.cardSuppLTTruncationIntegerPart
        (G := FiniteArchimedeanClass.tailSubmodule ℚ T)
        (R := R) (κ := κ) Z) = ⊤)
    (a : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z) : IsPrimal a := by
  apply isPrimal_of_finite_classes_and_limit_tail_conditions Z
  · intro y hy
    apply HahnSeries.Nonpositive.isPrimal_of_supportArchimedeanClasses_finite
      Z s (fun c ↦ (LM24.assumptionA1AtFiniteClass_iff s c).mp (hA1 c)) hA2 y
    rw [supportArchimedeanClasses_toNonpositiveRingHom]
    exact hy
  · exact hcomplete
  · exact htailfrac

end HahnSeries.CardSuppLTTruncationIntegerPart
