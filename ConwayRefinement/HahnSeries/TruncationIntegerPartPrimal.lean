/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.Algebra.Divisibility.PrimalPreimage
public import ConwayRefinement.HahnSeries.Nonpositive
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Primality in a Hahn-series truncation integer part

This module specializes the generic residue-preimage form of LM24, Lemma 9.2.1 to
`Z + L((H^{<0}))`, represented intrinsically as the nonpositive Hahn series whose coefficient at
zero belongs to `Z`. The coefficient-at-zero map is an algebra retraction of constant series.
-/

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {L : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field L]

/-- Coefficient at exponent zero as an algebra retraction of the constant-series embedding. -/
def constantCoeffAlgHom : Nonpositive G L →ₐ[L] L where
  __ := constantCoeff
  commutes' r := by
    change constantCoeff (C r : Nonpositive G L) = r
    simp

@[simp]
theorem constantCoeffAlgHom_apply (x : Nonpositive G L) :
    constantCoeffAlgHom x = (x : L⟦G⟧).coeff 0 :=
  constantCoeff_apply x

/-- The truncation integer part is definitionally the residue preimage under coefficient at
zero. -/
theorem truncationIntegerPart_eq_residueSubring (Z : Subring L) :
    truncationIntegerPart G Z =
      Subring.residueSubring (constantCoeffAlgHom (G := G) (L := L)) Z :=
  by
    ext x
    rw [mem_truncationIntegerPart, Subring.mem_residueSubring,
      constantCoeffAlgHom_apply]

/-- The canonical identity-on-elements equivalence with the residue-preimage presentation. -/
def truncationIntegerPartEquivResidueSubring (Z : Subring L) :
    truncationIntegerPart G Z ≃+*
      Subring.residueSubring (constantCoeffAlgHom (G := G) (L := L)) Z where
  toFun x := ⟨x, by rw [← truncationIntegerPart_eq_residueSubring Z]; exact x.2⟩
  invFun x := ⟨x, by rw [truncationIntegerPart_eq_residueSubring Z]; exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end HahnSeries.Nonpositive
