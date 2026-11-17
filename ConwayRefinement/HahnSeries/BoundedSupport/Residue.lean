/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.BoundedSupport.Basic
import Mathlib.Data.Rat.Floor

/-!
# Residues of bounded nonpositive Hahn series

The cardinal-bounded nonpositive Hahn series form an algebra over their coefficient field.
Coefficient at exponent zero is an algebra retraction, and imposing that this residue lie in a
coefficient subring recovers the usual cardinal-bounded truncation integer part.

This is the bounded counterpart of
`HahnSeries.Nonpositive.truncationIntegerPartEquivResidueSubring`. It allows equation-local
residue normalization without forgetting the support-cardinality bound.
-/

public noncomputable section

open Cardinal
open scoped HahnSeries

universe u v

namespace HahnSeries

variable {G : Type u} {L : Type v} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field L] [Fact (aleph0 < κ)]

/-- Cardinal-bounded Hahn series with nonpositive support. -/
abbrev CardSuppLTNonpositive := cardSuppLTTruncationIntegerPart
  (G := G) (R := L) (κ := κ) (⊤ : Subring L)

/-- Constant series as a ring map into cardinal-bounded nonpositive Hahn series. -/
noncomputable def CardSuppLTNonpositive.C :
    L →+* CardSuppLTNonpositive (G := G) (L := L) (κ := κ) where
  toFun r := ⟨⟨HahnSeries.C r, by
    exact (HahnSeries.cardSupp_single_le (0 : G) r).trans_lt
      (one_lt_aleph0.trans (Fact.out : aleph0 < κ))⟩, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    constructor
    · intro g hg
      have hg0 : g = 0 := HahnSeries.support_single_subset hg
      exact hg0 ▸ le_rfl
    · exact Subring.mem_top _⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one HahnSeries.C
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul HahnSeries.C x y
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_zero HahnSeries.C
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add HahnSeries.C x y

/-- Cardinal-bounded nonpositive Hahn series form an algebra over their coefficient field. -/
noncomputable instance : Algebra L (CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) where
  algebraMap := CardSuppLTNonpositive.C
  smul r x := CardSuppLTNonpositive.C r * x
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

namespace CardSuppLTNonpositive

/-- The scalar `r` is the constant series `r`. -/
@[simp]
theorem coe_algebraMap (r : L) :
    ((algebraMap L (CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) r : L⟦G⟧)) =
      HahnSeries.C r :=
  (rfl)

/-- Coefficient at exponent zero as an algebra retraction on bounded nonpositive series. -/
def constantCoeffAlgHom :
    CardSuppLTNonpositive (G := G) (L := L) (κ := κ) →ₐ[L] L where
  toFun x := (x : L⟦G⟧).coeff 0
  map_one' := by simp
  map_mul' x y := by
    have hx := (mem_cardSuppLTTruncationIntegerPart (Z := (⊤ : Subring L))).mp x.2
    have hy := (mem_cardSuppLTTruncationIntegerPart (Z := (⊤ : Subring L))).mp y.2
    let x' : HahnSeries.Nonpositive G L := ⟨x, hx.1⟩
    let y' : HahnSeries.Nonpositive G L := ⟨y, hy.1⟩
    exact HahnSeries.Nonpositive.coeff_zero_mul x' y'
  map_zero' := by simp
  map_add' x y := by simp
  commutes' r := by
    change (HahnSeries.C r : L⟦G⟧).coeff 0 = r
    simp

@[simp]
theorem constantCoeffAlgHom_apply
    (x : CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) :
    constantCoeffAlgHom x = (x : L⟦G⟧).coeff 0 :=
  (rfl)

/-- The canonical identity-on-series equivalence between the bounded truncation integer part and
the residue-preimage presentation inside bounded nonpositive Hahn series. -/
def truncationIntegerPartEquivResidueSubring (S : Subring L) :
    cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S ≃+*
      Subring.residueSubring
        (constantCoeffAlgHom (G := G) (L := L) (κ := κ)) S where
  toFun x := ⟨⟨x, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    exact ⟨((mem_cardSuppLTTruncationIntegerPart (Z := S)).mp x.2).1,
      Subring.mem_top _⟩⟩, by
        rw [Subring.mem_residueSubring, constantCoeffAlgHom_apply]
        exact ((mem_cardSuppLTTruncationIntegerPart (Z := S)).mp x.2).2⟩
  invFun x := ⟨x.1.1, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    exact ⟨((mem_cardSuppLTTruncationIntegerPart (Z := (⊤ : Subring L))).mp x.1.2).1,
      x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The residue-subring presentation does not change the underlying Hahn series. -/
@[simp]
theorem coe_truncationIntegerPartEquivResidueSubring (S : Subring L)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S) :
    ((((truncationIntegerPartEquivResidueSubring S x :
        Subring.residueSubring constantCoeffAlgHom S) :
      CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) : L⟦G⟧)) =
      (x : L⟦G⟧) :=
  (rfl)

end CardSuppLTNonpositive

end HahnSeries
