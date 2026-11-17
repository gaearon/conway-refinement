/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.BoundedSupport.Residue
public import ConwayRefinement.HahnSeries.ConvexSubgroup.Restriction

import ConwayRefinement.Blueprint
public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Data.Real.Basic
import ConwayRefinement.HahnSeries.Nonpositive.GCD
import ConwayRefinement.Algebra.Divisibility.PrimalPreimage
import ConwayRefinement.HahnSeries.BoundedSupport.Primality
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Primality through regrouping along a convex subgroup

Let `C` be a convex subspace of the exponent group `G`, `Γ = G ⧸ C`, `L = R((C))_κ` and
`D = Z + R((C^{<0}))_κ`. Regrouping exponents along `C` identifies `Z + R((G^{<0}))_κ` with the
`D + M` construction `D + L((Γ^{<0}))_κ`, the inverse image of `D` under the constant coefficient
`π` of `T = L((Γ^{≤0}))_κ`. The constant coefficient of a regrouped series is its restriction to
`C`. The `D + M` primality lemma therefore reduces primality in `Z + R((G^{<0}))_κ` to primality in
`T`, primality of the restriction to `C` in `D`, and the fraction-field condition on `D` when that
restriction vanishes. This step is used once at the leading Archimedean class and once at a limit
of Archimedean classes.
-/

public noncomputable section

open Cardinal
open HahnSeries.CardSuppLTTruncationIntegerPart
open scoped HahnSeries

universe u v w

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [Field K] [CharZero K]

/-- A nonpositive Hahn series whose exponent group is order-isomorphic to `ℝ` is primal. -/
theorem isPrimal_of_orderIso_real (e : G ≃+o ℝ) (a : Nonpositive G K) : IsPrimal a :=
  (RingEquiv.isPrimal_iff (embDomainRingEquiv e) a).mp
    (isPrimal (embDomainRingEquiv e a))

end HahnSeries.Nonpositive

namespace HahnSeries.CardSuppLTNonpositive

variable {Γ : Type u} {L : Type v} {κ : Cardinal.{u}}
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable [Field L] [CharZero L] [Fact (ℵ₀ < κ)]

/-- If the exponent group is order-isomorphic to `ℝ`, every element of `L((Γ^{≤0}))_κ` is primal:
supports are countable, so the bound `κ > ℵ₀` is no restriction. -/
theorem isPrimal_of_orderIso_real (e : Γ ≃+o ℝ)
    (x : CardSuppLTNonpositive (G := Γ) (L := L) (κ := κ)) : IsPrimal x := by
  haveI : Archimedean Γ := ⟨fun a b hb ↦ by
    have hb' : 0 < e b := by simpa using e.strictMono hb
    obtain ⟨n, hn⟩ := Archimedean.arch (e a) hb'
    exact ⟨n, by rw [← map_nsmul] at hn; exact (map_le_map_iff e).mp hn⟩⟩
  let φ := toNonpositiveRingHom (G := Γ) (R := L) (κ := κ) ⊤
  have hsurj : Function.Surjective φ := fun y ↦
    ⟨⟨⟨y, (cardSupp_le_aleph0_of_archimedean (y : L⟦Γ⟧)).trans_lt Fact.out⟩,
      (mem_cardSuppLTTruncationIntegerPart (Z := (⊤ : Subring L))).mpr
        ⟨y.2, Subring.mem_top _⟩⟩, Subtype.ext (coe_toNonpositiveRingHom _ _)⟩
  exact (RingEquiv.isPrimal_iff
    (RingEquiv.ofBijective φ ⟨toNonpositiveRingHom_injective _, hsurj⟩) x).mp
    (Nonpositive.isPrimal_of_orderIso_real e _)

end HahnSeries.CardSuppLTNonpositive

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

section Restriction

variable {G : Type u} {R : Type v} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field R] [Fact (ℵ₀ < κ)]

/-- The restriction of a series to a convex subgroup `C`, viewed in `Z + R((C^{<0}))_κ`, is primal
there as soon as it is primal in `Z + R((G^{<0}))_κ`. -/
theorem isPrimal_restrictDomain_of_isPrimal_restrictToAddSubgroup (Z : Subring R)
    (C : AddSubgroup G) (hC : (C : Set G).OrdConnected)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (h : IsPrimal (restrictToAddSubgroup Z C x)) :
    IsPrimal (restrictDomain C.subtype Subtype.val_injective (fun _ _ ↦ Iff.rfl) Z x) := by
  classical
  apply isPrimal_of_isPrimal_mapDomain C.subtype Subtype.val_injective (fun _ _ ↦ Iff.rfl) Z
    (by simpa using hC)
  convert h using 1
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_mapDomain_restrictDomain, coe_restrictToAddSubgroup]
  simp only [AddSubgroup.range_subtype]

end Restriction

section Step

variable {G : Type u} {R : Type v} {K : Type w} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field K] [Module K G] [Field R]
variable [Fact (Cardinal.aleph0 < κ)] [Fact κ.IsRegular]

/-- **Primality through regrouping.** A series is primal in `Z + R((G^{<0}))_κ` if its regrouping
along a convex subspace `C` is primal in `L((Γ^{≤0}))_κ`, its restriction to `C` is primal in
`D = Z + R((C^{<0}))_κ`, and `L` is the fraction field of `D` when that restriction is zero. -/
@[blueprint "lem:primality-through-regrouping"
  (phase := "Reduction along Archimedean classes")
  (title := "Primality through regrouping along a convex subgroup")
  (statement := /--
    Let $K$ be a field, $G$ an ordered abelian group that is a $K$-vector
    space, $C\subseteq G$ a convex $K$-subspace, $R$ a field, $Z\subseteq R$ a
    subring, and $\kappa>\aleph_0$ a regular cardinal.  Put $\Gamma=G/C$,
    $L=R((C))_\kappa$, $D=Z+R((C^{<0}))_\kappa$ and
    $T=L((\Gamma^{\le0}))_\kappa$.  Let $x\in Z+R((G^{<0}))_\kappa$, let
    $\hat x\in T$ be its regrouping along $C$, and let $x_{\vert C}\in D$ be
    its restriction to $C$.  If $\hat x$ is primal in $T$, $x_{\vert C}$ is
    primal in $D$, and $L=\operatorname{Frac}(D)$ in case $x_{\vert C}=0$, then
    $x$ is primal in $Z+R((G^{<0}))_\kappa$.
  -/)
  (proof := /--
    A $K$-linear complement of $C$ identifies $G$ with $C\times\Gamma$, ordered
    lexicographically with the $\Gamma$-coordinate first, and regrouping
    exponents along this decomposition identifies $Z+R((G^{<0}))_\kappa$ with
    the inverse image $D+L((\Gamma^{<0}))_\kappa$ of $D$ under the constant
    coefficient $\pi:T\to L$; moreover $\pi(\hat x)=x_{\vert C}$.  Apply
    \ref{lem:primality-in-d-plus-m}.
  -/)]
theorem isPrimal_of_isPrimal_regroupAmbient
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hT : IsPrimal (regroupAmbient P Z x))
    (hres : IsPrimal (restrictDomain P.toAddSubgroup.subtype Subtype.val_injective
      (fun _ _ ↦ Iff.rfl) Z x))
    (hfrac : restrictDomain P.toAddSubgroup.subtype Subtype.val_injective
        (fun _ _ ↦ Iff.rfl) Z x = 0 →
      Subring.fracSubring (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) = ⊤) :
    IsPrimal x := by
  rw [regroupAmbient_apply] at hT
  rw [← RingEquiv.isPrimal_iff (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z)]
  refine CardSuppLTNonpositive.isPrimal_of_isPrimal_ambient _ _ hT ?_ fun h0 ↦ hfrac ?_
  · rw [coeff_zero_convexQuotientSplitRingEquiv]
    exact hres
  · rw [← coeff_zero_convexQuotientSplitRingEquiv]
    exact Subtype.ext h0

end Step

end HahnSeries.CardSuppLTTruncationIntegerPart
