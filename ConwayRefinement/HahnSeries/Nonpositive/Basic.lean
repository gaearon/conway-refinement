/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.EmbDomain
public import ConwayRefinement.Algebra.Divisibility.PrimalPreimage
import Mathlib.Data.Rat.Floor

/-!
# The ring of nonpositive Hahn series

For an ordered abelian group `G` and a ring `R`, the series supported in `G^{≤0}` form a subring
`R((G^{≤0}))` of `R((G))`, on which the coefficient at `0` is a ring homomorphism. For a subring `Z
⊆ R`, its preimage is the generalised-power-series integer part `Z + R((G^{<0}))`. This file also
reindexes these rings along exponent equivalences and applies coefficient maps.
-/

/-!
## Hahn series with nonpositive support

This file constructs the subring of Hahn series supported on the nonpositive cone of a partially
ordered additive commutative group. On this subring, evaluation at exponent zero is a ring
homomorphism. Pulling a coefficient subring back along that homomorphism gives an intrinsic model
of a truncation integer part.

For a linearly ordered exponent group and a coefficient field, the construction is the ring used
in LM24, Section 2.1, especially Remark 2.1.2. Mathlib's `IsPWO` support condition then agrees with
the paper's well-ordered-support convention, so `K((G^{≤ 0}))` is represented without reversing
the order on `G`. The declarations below generalize the coefficient field to a ring and the linear
order to a partial order because the constructions and proofs require only those assumptions.
-/

section

universe u v

public noncomputable section

namespace HahnSeries

variable (Γ : Type u) (R : Type v)
variable [AddCommGroup Γ] [PartialOrder Γ] [IsOrderedAddMonoid Γ] [Ring R]

/-- The subring of Hahn series whose support consists of nonpositive exponents. -/
@[expose] def nonpositiveSubring : Subring R⟦Γ⟧ where
  carrier := {x | x.support ⊆ Set.Iic 0}
  zero_mem' := by simp
  one_mem' := by
    intro g hg
    have hg0 : g = 0 := support_single_subset hg
    simp [hg0]
  add_mem' := fun {x y} hx hy => by
    intro g hg
    rcases support_add_subset x y hg with hg | hg
    · exact hx hg
    · exact hy hg
  neg_mem' := fun {x} hx => (support_neg_subset x).trans hx
  mul_mem' := fun {x y} hx hy => by
    intro g hg
    obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hg
    exact add_nonpos (hx hi) (hy hj)

/-- Membership in `nonpositiveSubring` means that every support exponent is at most zero. -/
@[simp]
theorem mem_nonpositiveSubring {x : R⟦Γ⟧} :
    x ∈ nonpositiveSubring Γ R ↔ x.support ⊆ Set.Iic 0 :=
  (Iff.rfl)

/-- The type of Hahn series supported in the nonpositive exponents. -/
abbrev Nonpositive := ↥(nonpositiveSubring Γ R)

namespace Nonpositive

variable {Γ R}

/-- The support of a nonpositive Hahn series is contained in `Set.Iic 0`. -/
theorem support_subset (x : Nonpositive Γ R) :
    (x : R⟦Γ⟧).support ⊆ Set.Iic 0 :=
  x.2

/-- A constant Hahn series, regarded as a nonpositive Hahn series. -/
def C : R →+* Nonpositive Γ R :=
  (HahnSeries.C : R →+* R⟦Γ⟧).codRestrict (nonpositiveSubring Γ R) fun r g hg => by
    have hg0 : g = 0 := support_single_subset hg
    simp [hg0]

@[simp]
theorem coe_C (r : R) : ((C : R →+* Nonpositive Γ R) r : R⟦Γ⟧) = HahnSeries.C r :=
  (rfl)

/-- A single monomial with nonpositive exponent, regarded as a nonpositive Hahn series. -/
def single (g : Γ) (r : R) (hg : g ≤ 0) : Nonpositive Γ R :=
  ⟨HahnSeries.single g r, fun i hi => by
    rw [eq_of_mem_support_single hi]
    exact hg⟩

@[simp]
theorem coe_single (g : Γ) (r : R) (hg : g ≤ 0) :
    (single g r hg : R⟦Γ⟧) = HahnSeries.single g r :=
  (rfl)

private theorem eq_zero_of_mem_addAntidiagonal_zero {x y : Nonpositive Γ R} {ij : Γ × Γ}
    (hij : ij ∈ Finset.addAntidiagonal (x : R⟦Γ⟧).isPWO_support
      (y : R⟦Γ⟧).isPWO_support 0) :
    ij = (0, 0) := by
  rcases Finset.mem_addAntidiagonal.mp hij with ⟨hi, hj, hij⟩
  have hi_zero := eq_zero_of_add_nonneg_left (support_subset x hi) (support_subset y hj) hij.ge
  have hj_zero := eq_zero_of_add_nonneg_right (support_subset x hi) (support_subset y hj) hij.ge
  exact Prod.ext hi_zero hj_zero

/-- The coefficient at exponent zero of a product of nonpositive Hahn series is the product of
their coefficients at exponent zero. -/
@[simp]
theorem coeff_zero_mul (x y : Nonpositive Γ R) :
    ((x : R⟦Γ⟧) * (y : R⟦Γ⟧)).coeff 0 =
      (x : R⟦Γ⟧).coeff 0 * (y : R⟦Γ⟧).coeff 0 := by
  rw [HahnSeries.coeff_mul]
  by_cases hx : (x : R⟦Γ⟧).coeff 0 = 0
  · rw [hx, zero_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [eq_zero_of_mem_addAntidiagonal_zero hij]
    simp [hx]
  · by_cases hy : (y : R⟦Γ⟧).coeff 0 = 0
    · rw [hy, mul_zero]
      apply Finset.sum_eq_zero
      intro ij hij
      rw [eq_zero_of_mem_addAntidiagonal_zero hij]
      simp [hy]
    · apply Finset.sum_eq_single (0, 0)
      · intro ij hij hne
        exact (hne (eq_zero_of_mem_addAntidiagonal_zero hij)).elim
      · simp [Finset.mem_addAntidiagonal, HahnSeries.mem_support, hx, hy]

/-- Evaluation at exponent zero as a ring homomorphism on nonpositive Hahn series. -/
def constantCoeff : Nonpositive Γ R →+* R where
  toFun x := (x : R⟦Γ⟧).coeff 0
  map_zero' := HahnSeries.coeff_zero
  map_one' := by simp
  map_add' x y := HahnSeries.coeff_add
  map_mul' := coeff_zero_mul

/-- Evaluating `constantCoeff` returns the coefficient at exponent zero. -/
@[simp]
theorem constantCoeff_apply (x : Nonpositive Γ R) :
    constantCoeff x = (x : R⟦Γ⟧).coeff 0 :=
  (rfl)

section Algebra

variable {G : Type*} {L : Type*}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field L]

/-- Nonpositive Hahn series form an algebra over their coefficient field by constant series. -/
instance : Algebra L (Nonpositive G L) where
  algebraMap := C
  smul r x := C r * x
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

/-- The coefficient-field algebra map is the constant-series embedding. -/
@[simp]
theorem algebraMap_apply (r : L) :
    algebraMap L (Nonpositive G L) r = C r := (rfl)

/-- Scalar multiplication commutes with the coercion to Hahn series. -/
@[simp, norm_cast]
theorem coe_smul (r : L) (x : Nonpositive G L) :
    ((r • x : Nonpositive G L) : L⟦G⟧) = r • (x : L⟦G⟧) := by
  rw [Algebra.smul_def, algebraMap_apply, Subring.coe_mul, coe_C,
    HahnSeries.C_mul_eq_smul]

end Algebra

end Nonpositive

/-- The subring of nonpositive Hahn series whose coefficient at exponent zero lies in `Z`. -/
def truncationIntegerPart (Γ : Type u) {R : Type v} [AddCommGroup Γ] [PartialOrder Γ]
    [IsOrderedAddMonoid Γ] [Ring R] (Z : Subring R) : Subring (Nonpositive Γ R) :=
  Z.comap Nonpositive.constantCoeff

/-- Membership in a truncation integer part is membership of the constant coefficient in `Z`. -/
@[simp]
theorem mem_truncationIntegerPart {Z : Subring R} {x : Nonpositive Γ R} :
    x ∈ truncationIntegerPart Γ Z ↔ (x : R⟦Γ⟧).coeff 0 ∈ Z :=
  (Iff.rfl)

end HahnSeries

end
end

/-!
## Reindexing nonpositive Hahn series along an exponent equivalence

An ordered additive equivalence of exponent groups induces a ring equivalence of their
nonpositive Hahn-series rings. Since the exponent types may live in different universes, support
order types are compared after lifting both ordinals to a common universe.

It is used when an Archimedean stratum is identified with the ordered additive group of real
numbers.
-/

section

public noncomputable section

namespace HahnSeries.Nonpositive

universe u v w

variable {G : Type u} {H : Type v} {K : Type w}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [LinearOrder H] [AddCommGroup H] [IsOrderedAddMonoid H]
variable [CommRing K]

/-- Reindex nonpositive Hahn series along an ordered additive equivalence of exponent groups. -/
def embDomainRingEquiv (e : G ≃+o H) : Nonpositive G K ≃+* Nonpositive H K where
  toFun x := ⟨HahnSeries.embDomainRingEquiv e x, by
    rw [HahnSeries.mem_nonpositiveSubring]
    intro h hh
    rw [HahnSeries.support_embDomainRingEquiv] at hh
    obtain ⟨g, hg, rfl⟩ := hh
    change e g ≤ 0
    simpa only [map_zero] using e.strictMono.monotone (support_subset x hg)⟩
  invFun x := ⟨HahnSeries.embDomainRingEquiv e.symm x, by
    rw [HahnSeries.mem_nonpositiveSubring]
    intro g hg
    rw [HahnSeries.support_embDomainRingEquiv] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    change e.symm h ≤ 0
    simpa only [map_zero] using e.symm.strictMono.monotone (support_subset x hh)⟩
  left_inv x := by
    apply Subtype.ext
    ext g
    have h := HahnSeries.embDomainRingEquiv_coeff e.symm
      (HahnSeries.embDomainRingEquiv e (x : K⟦G⟧)) (e g)
    rw [e.symm_apply_apply, HahnSeries.embDomainRingEquiv_coeff] at h
    exact h
  right_inv x := by
    apply Subtype.ext
    ext h
    have hh := HahnSeries.embDomainRingEquiv_coeff e
      (HahnSeries.embDomainRingEquiv e.symm (x : K⟦H⟧)) (e.symm h)
    rw [e.apply_symm_apply, HahnSeries.embDomainRingEquiv_coeff] at hh
    exact hh
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (HahnSeries.embDomainRingEquiv e) (x : K⟦G⟧) y
  map_add' x y := by
    apply Subtype.ext
    exact map_add (HahnSeries.embDomainRingEquiv e) (x : K⟦G⟧) y

/-- The underlying Hahn series is the unrestricted exponent-domain equivalence. -/
@[simp]
theorem coe_embDomainRingEquiv (e : G ≃+o H) (x : Nonpositive G K) :
    (embDomainRingEquiv e x : K⟦H⟧) = HahnSeries.embDomainRingEquiv e x :=
  (rfl)

end HahnSeries.Nonpositive

end
end

/-!
## Coefficientwise ring homomorphisms of Hahn series

A ring homomorphism on coefficients acts coefficientwise on Hahn series and on their
nonpositive-support subrings. Injective coefficient maps preserve support exactly. These bundled
maps provide the module-safe interface needed when a bounded Hahn field is embedded in the full
Hahn field.
-/

section

public noncomputable section

namespace HahnSeries

universe u v w

section Full

variable {Γ : Type u} {R : Type v} {S : Type w}
variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
variable [Semiring R] [Semiring S]

/-- Apply a ring homomorphism to every coefficient of a Hahn series. -/
def coefficientMapRingHom (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧ where
  toFun x := x.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero f.toMonoidWithZeroHom.toZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom

/-- Coefficientwise mapping evaluates by applying the coefficient homomorphism. -/
@[simp]
theorem coefficientMapRingHom_coeff (f : R →+* S) (x : R⟦Γ⟧) (g : Γ) :
    (coefficientMapRingHom f x).coeff g = f (x.coeff g) :=
  (rfl)

/-- An injective coefficient homomorphism preserves Hahn-series support. -/
theorem support_coefficientMapRingHom (f : R →+* S) (hf : Function.Injective f)
    (x : R⟦Γ⟧) :
    (coefficientMapRingHom f x).support = x.support := by
  ext g
  rw [mem_support, mem_support, coefficientMapRingHom_coeff]
  exact not_congr (map_eq_zero_iff f hf)

end Full

namespace Nonpositive

variable {Γ : Type u} {R : Type v} {S : Type w}
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable [Ring R] [Ring S]

end Nonpositive

end HahnSeries

end
end

/-!
## Primality in a Hahn-series truncation integer part

This module specializes the generic residue-preimage form of LM24, Lemma 9.2.1 to
`Z + L((H^{<0}))`, represented intrinsically as the nonpositive Hahn series whose coefficient at
zero belongs to `Z`. The coefficient-at-zero map is an algebra retraction of constant series.
-/

section

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

end
end
