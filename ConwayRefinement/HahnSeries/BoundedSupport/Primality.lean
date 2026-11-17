/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.BoundedSupport.Residue
import ConwayRefinement.Algebra.Divisibility.PrimalPreimage
import Mathlib.Algebra.Field.IsField

/-!
# Primality in bounded truncation integer parts

Through the residue presentation of `S + L((G^{<0}))_κ` as the subring of `L((G^{≤0}))_κ` cut out
by the condition that the constant coefficient lie in `S`, primality in `S + L((G^{<0}))_κ` is
compared with primality in `L((G^{≤0}))_κ` and in `S`. An element of order zero is primal when `S`
is pre-Schreier.
-/

public noncomputable section

open Cardinal
open scoped HahnSeries

universe u v

namespace HahnSeries

variable {G : Type u} {L : Type v} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field L] [Fact (aleph0 < κ)]

namespace CardSuppLTNonpositive

/-- Primality in the bounded truncation integer part `S + L((G^{<0}))_κ` follows from primality
in `L((G^{≤0}))_κ`, primality of the constant coefficient in `S`, and the fraction-field
condition on `S` when that coefficient is zero. -/
theorem isPrimal_of_isPrimal_ambient (S : Subring L)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S)
    (hA : IsPrimal ((truncationIntegerPartEquivResidueSubring S x :
      Subring.residueSubring constantCoeffAlgHom S) :
        CardSuppLTNonpositive (G := G) (L := L) (κ := κ)))
    (hres : IsPrimal (⟨(x : L⟦G⟧).coeff 0,
      ((mem_cardSuppLTTruncationIntegerPart (Z := S)).mp x.2).2⟩ : S))
    (hfrac : (x : L⟦G⟧).coeff 0 = 0 → Subring.fracSubring S = ⊤) : IsPrimal x := by
  rw [← RingEquiv.isPrimal_iff (truncationIntegerPartEquivResidueSubring S)]
  exact Subring.isPrimal_residueSubring_of_isPrimal_of_residue _ hA
    (fun _ ↦ by convert hres using 2; simp) (by simpa using hfrac)

/-- An element of the bounded truncation integer part with nonzero constant coefficient that is
primal there is primal in `L((G^{≤0}))_κ`. -/
theorem isPrimal_ambient_of_isPrimal (S : Subring L)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S) (hx : IsPrimal x)
    (hx0 : (x : L⟦G⟧).coeff 0 ≠ 0) :
    IsPrimal ((truncationIntegerPartEquivResidueSubring S x :
      Subring.residueSubring constantCoeffAlgHom S) :
        CardSuppLTNonpositive (G := G) (L := L) (κ := κ)) :=
  Subring.isPrimal_of_isPrimal_residueSubring _
    ((RingEquiv.isPrimal_iff (truncationIntegerPartEquivResidueSubring S) x).mpr hx)
    (by simpa using hx0)

end CardSuppLTNonpositive

namespace CardSuppLTTruncationIntegerPart

private theorem isUnit_map_of_isUnit {M N : Type*} [Monoid M] [Monoid N]
    (f : M →* N) {x : M} (hx : IsUnit x) : IsUnit (f x) :=
  hx.map f

private theorem isPrimal_residueSubring_of_isUnit
    {F A : Type*} [Field F] [CommRing A] [Algebra F A] [IsDomain A]
    (π : A →ₐ[F] F) (S : Subring F) [DecompositionMonoid S]
    {x : A} (hx : π x ∈ S) (hx0 : π x ≠ 0) (hunit : IsUnit x) :
    IsPrimal (⟨x, hx⟩ : Subring.residueSubring π S) :=
  Subring.isPrimal_residueSubring_of_isPrimal
    hx hx0 (DecompositionMonoid.primal _) hunit.isPrimal

private theorem isPrimal_equiv_preimage
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {x : A}
    (hx : IsPrimal (e x)) : IsPrimal x :=
  (RingEquiv.isPrimal_iff e x).mp hx

/-- An order-zero element of a cardinal-bounded truncation integer part is primal when its
coefficient subring is pre-Schreier. -/
theorem isPrimal_of_order_eq_zero
    (S : Subring L) [DecompositionMonoid S]
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := L) (κ := κ) S)
    (horder : ((toNonpositiveRingHom S x : Nonpositive G L) : HahnSeries G L).order = 0) :
    IsPrimal x := by
  let A := CardSuppLTNonpositive (G := G) (L := L) (κ := κ)
  let π := CardSuppLTNonpositive.constantCoeffAlgHom (G := G) (L := L) (κ := κ)
  let Φ := CardSuppLTNonpositive.truncationIntegerPartEquivResidueSubring
    (G := G) (L := L) (κ := κ) S
  by_cases hx : x = 0
  · rw [hx]
    exact isPrimal_zero
  let xN := toNonpositiveRingHom S x
  have hconstant : (xN : HahnSeries G L) = HahnSeries.C ((xN : HahnSeries G L).coeff 0) := by
    ext g
    by_cases hg : g = 0
    · subst g
      simp
    · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hg]
      by_contra hcoeff
      have hgNonpos : g ≤ 0 := Nonpositive.support_subset xN
        ((HahnSeries.mem_support _ _).mpr hcoeff)
      have hzeroLe : 0 ≤ g := horder ▸ HahnSeries.order_le_of_coeff_ne_zero hcoeff
      exact hg (le_antisymm hgNonpos hzeroLe)
  have hcoeff : (x : HahnSeries G L).coeff 0 ≠ 0 := by
    intro hzero
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    change (x : HahnSeries G L) = 0
    simpa only [xN, coe_toNonpositiveRingHom, hzero, map_zero] using hconstant
  have hxC : (Φ x : A) = algebraMap L A ((x : HahnSeries G L).coeff 0) := by
    apply Subtype.ext
    apply Subtype.ext
    have h := hconstant.trans (CardSuppLTNonpositive.coe_algebraMap (G := G) (κ := κ) _).symm
    simpa only [Φ, CardSuppLTNonpositive.coe_truncationIntegerPartEquivResidueSubring, xN,
      coe_toNonpositiveRingHom] using h
  have hunit : IsUnit (Φ x : A) := by
    rw [hxC]
    have hcoeffUnit : IsUnit ((x : HahnSeries G L).coeff 0) :=
      isUnit_iff_ne_zero.mpr hcoeff
    exact isUnit_map_of_isUnit (algebraMap L A).toMonoidHom hcoeffUnit
  have hπ : π (Φ x : A) = (x : HahnSeries G L).coeff 0 := by
    simp [π, Φ]
  have hΦ : IsPrimal (Φ x) :=
    isPrimal_residueSubring_of_isUnit π S (Φ x).2 (hπ ▸ hcoeff) hunit
  exact isPrimal_equiv_preimage Φ hΦ

end CardSuppLTTruncationIntegerPart

end HahnSeries
