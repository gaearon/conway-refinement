/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Nonpositive.Basic

import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Algebra.Field.IsField
import Mathlib.Data.Rat.Floor

/-!
# Finite-support nonpositive series

The series of finite support in `K((G^{≤0}))` form the subring `K(G^{≤0})` of L'Innocente and
Mantova (LM24, Notation 2.1.5). Its units are the nonzero constants (LM24, Fact 2.5.2), and every
nonzero element has a unique normalized associate, whose coefficient at the largest exponent is `1`.
-/

/-!
## Finite-support Hahn series

This file packages finite-support Hahn series as the specialization at `Cardinal.aleph0` of
Mathlib's cardinal-bounded Hahn-series subring. It also pulls that subring back to nonpositive
Hahn series. The latter is the ring denoted by `K(G^{≤ 0})` in LM24.
-/

section

universe u v

public noncomputable section

namespace HahnSeries

variable {G : Type u} {K : Type v}

section HahnSeries

variable [PartialOrder G] [AddCommMonoid G] [IsOrderedCancelAddMonoid G] [Ring K]

/-- The subring of Hahn series with finite support. -/
def finiteSupportSubring : Subring K⟦G⟧ :=
  let _ : Fact (Cardinal.aleph0 ≤ Cardinal.aleph0) := ⟨le_rfl⟩
  HahnSeries.cardSuppLTSubring G K Cardinal.aleph0

/-- Membership in the finite-support subring is finiteness of the Hahn-series support. -/
@[simp]
theorem mem_finiteSupportSubring_iff (b : K⟦G⟧) :
    b ∈ (finiteSupportSubring : Subring K⟦G⟧) ↔ b.support.Finite := by
  letI : Fact (Cardinal.aleph0 ≤ Cardinal.aleph0) := ⟨le_rfl⟩
  rw [finiteSupportSubring, HahnSeries.mem_cardSuppLTSubring, HahnSeries.cardSupp]
  exact Cardinal.lt_aleph0_iff_set_finite

end HahnSeries

namespace Nonpositive

variable [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [Ring K]

/-- The subring of nonpositive Hahn series with finite support. -/
def finiteSupportSubring : Subring (Nonpositive G K) :=
  HahnSeries.finiteSupportSubring.comap (HahnSeries.nonpositiveSubring G K).subtype

/-- The type of finite-support nonpositive Hahn series. -/
abbrev FiniteSupportRing :=
  (finiteSupportSubring : Subring (Nonpositive G K))

/-! The structures on the finite-support ring, named here rather than rebuilt at each use.
`Zero` is the one that matters: it is asked for by every comparison against `0`, and resolving it
through the `Subring` membership classes is not cheap. -/

instance : Zero (FiniteSupportRing (G := G) (K := K)) := inferInstance

instance : One (FiniteSupportRing (G := G) (K := K)) := inferInstance

instance : Semiring (FiniteSupportRing (G := G) (K := K)) := inferInstance

/-- Membership in the nonpositive finite-support subring is finiteness of the underlying support.
-/
@[simp]
theorem mem_finiteSupportSubring_iff (b : Nonpositive G K) :
    b ∈ (finiteSupportSubring : Subring (Nonpositive G K)) ↔
      (b : K⟦G⟧).support.Finite := by
  rw [finiteSupportSubring, Subring.mem_comap]
  rw [HahnSeries.mem_finiteSupportSubring_iff]
  simp only [Subring.subtype_apply]

end Nonpositive

namespace Nonpositive

variable [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [CommRing K]

instance : CommRing (FiniteSupportRing (G := G) (K := K)) := inferInstance

/-- The coefficient field embeds in the finite-support ring as constant Hahn series. -/
def finiteSupportScalarHom :
    K →+* (finiteSupportSubring : Subring (Nonpositive G K)) :=
  (C : K →+* Nonpositive G K).codRestrict finiteSupportSubring fun k ↦ by
    rw [mem_finiteSupportSubring_iff, coe_C]
    exact Set.Finite.subset (Set.finite_singleton (0 : G))
      HahnSeries.support_single_subset

/-- The scalar map is the constant-series embedding on underlying Hahn series. -/
@[simp]
theorem coe_finiteSupportScalarHom (k : K) :
    ((((finiteSupportScalarHom (G := G) k :
        (finiteSupportSubring : Subring (Nonpositive G K))) :
          Nonpositive G K) : K⟦G⟧)) = HahnSeries.C k :=
  coe_C k

end Nonpositive

end HahnSeries

end
end

/-!
## Units of the nonpositive Hahn-series ring

Half of LM24, Fact 2.5.2: the units of the finite-support nonpositive Hahn-series ring are
exactly the nonzero constant series.

Finiteness of the support is not used. The order of a nonzero series is the least exponent of its
support, so it is at most zero here, and it is additive on products over a domain. A product equal
to one therefore forces both orders to vanish, which leaves the whole support at zero.
-/

section

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [Field K]

/-- A factor of a product equal to one, among series supported in the nonpositive exponents, has
order zero. -/
private theorem order_eq_zero_of_mul_eq_one {x y : K⟦G⟧}
    (hx : x.support ⊆ Set.Iic 0) (hy : y.support ⊆ Set.Iic 0) (hxy : x * y = 1) :
    x.order = 0 := by
  have hx0 : x ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  have hy0 : y ≠ 0 := right_ne_zero_of_mul_eq_one hxy
  have hmem : ∀ {z : K⟦G⟧}, z ≠ 0 → z.support ⊆ Set.Iic 0 → z.order ≤ 0 := by
    intro z hz hsub
    exact hsub ((HahnSeries.mem_support _ _).mpr
      fun hc ↦ hz (HahnSeries.coeff_order_eq_zero.mp hc))
  have hsum := HahnSeries.order_mul hx0 hy0
  rw [hxy, HahnSeries.order_one] at hsum
  refine le_antisymm (hmem hx0 hx) ?_
  by_contra hlt
  rw [not_le] at hlt
  refine absurd ?_ (lt_irrefl (0 : G))
  calc (0 : G) = x.order + y.order := hsum
    _ < 0 + 0 := add_lt_add_of_lt_of_le hlt (hmem hy0 hy)
    _ = 0 := add_zero 0

/-- A nonpositive series of order zero is a constant. -/
private theorem eq_C_coeff_of_order_eq_zero {x : K⟦G⟧} (hx : x.support ⊆ Set.Iic 0)
    (horder : x.order = 0) : x = HahnSeries.C (x.coeff 0) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hg]
    by_contra hne
    exact hg (le_antisymm (hx hne) (horder ▸ HahnSeries.order_le_of_coeff_ne_zero hne))

/-- LM24, Fact 2.5.2: the units of the finite-support nonpositive Hahn-series ring are exactly
the nonzero constant series. -/
theorem isUnit_finiteSupport_iff_exists_scalar
    (p : (finiteSupportSubring : Subring (Nonpositive G K))) :
    IsUnit p ↔
      ∃ k : K, k ≠ 0 ∧ p = finiteSupportScalarHom (G := G) k := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, (u : (finiteSupportSubring : Subring (Nonpositive G K))) * q = 1 :=
      ⟨↑u⁻¹, u.mul_inv⟩
    have hmul : (((u : (finiteSupportSubring : Subring (Nonpositive G K))) :
          Nonpositive G K) : K⟦G⟧) * ((q : Nonpositive G K) : K⟦G⟧) = 1 := by
      have hcast := congrArg (fun r : (finiteSupportSubring : Subring (Nonpositive G K)) ↦
        ((r : Nonpositive G K) : K⟦G⟧)) hq
      simpa using hcast
    have hsub : ∀ r : (finiteSupportSubring : Subring (Nonpositive G K)),
        ((r : Nonpositive G K) : K⟦G⟧).support ⊆ Set.Iic 0 :=
      fun r ↦ (HahnSeries.mem_nonpositiveSubring (Γ := G) (R := K)).mp (r : Nonpositive G K).2
    have horder := order_eq_zero_of_mul_eq_one (hsub _) (hsub q) hmul
    refine ⟨(((u : (finiteSupportSubring : Subring (Nonpositive G K))) :
      Nonpositive G K) : K⟦G⟧).coeff 0, ?_, ?_⟩
    · rw [← horder]
      intro hc
      have h0 : (((u : (finiteSupportSubring : Subring (Nonpositive G K))) :
          Nonpositive G K) : K⟦G⟧) = 0 := HahnSeries.coeff_order_eq_zero.mp hc
      rw [h0, zero_mul] at hmul
      exact one_ne_zero hmul.symm
    · apply Subtype.ext
      apply Subtype.ext
      rw [coe_finiteSupportScalarHom]
      exact eq_C_coeff_of_order_eq_zero (hsub _) horder
  · rintro ⟨k, hk, rfl⟩
    exact (Ne.isUnit hk).map (finiteSupportScalarHom (G := G))

end HahnSeries.Nonpositive

end
end

/-!
## Normalized finite-support Hahn series

A nonzero finite-support Hahn series is normalized when the coefficient at its greatest support
exponent is `1`. This is the normalization used in LM24, Notation 5.4.5. The definition uses the
intrinsic order-theoretic predicate `IsGreatest`; it does not choose a basis or identify the
greatest exponent with a real supremum.

Every nonzero finite-support series is associated to such a normalized series. Consequently every
associate class has a canonical, choice-defined normalized representative, with the zero class
represented by zero. Uniqueness is stated separately under the exact hypothesis that all units are
nonzero constant series.
-/

section

open scoped HahnSeries

universe u v

namespace HahnSeries.Nonpositive

public noncomputable section

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [Field K]

/-- A finite-support nonpositive Hahn series is monic when its coefficient at the greatest
exponent in its support is one. -/
def IsMonicFiniteSupport
    (p : finiteSupportSubring (G := G) (K := K)) : Prop :=
  ∃ x : G,
    IsGreatest (((p : Nonpositive G K) : K⟦G⟧).support) x ∧
      ((p : Nonpositive G K) : K⟦G⟧).coeff x = 1

/-- Characterization of a monic finite-support series by its greatest support exponent. -/
theorem isMonicFiniteSupport_iff
    (p : finiteSupportSubring (G := G) (K := K)) :
    IsMonicFiniteSupport p ↔
      ∃ x : G,
        IsGreatest (((p : Nonpositive G K) : K⟦G⟧).support) x ∧
          ((p : Nonpositive G K) : K⟦G⟧).coeff x = 1 :=
  Iff.rfl

/-- The multiplicative identity is a monic finite-support series. -/
@[simp]
theorem isMonicFiniteSupport_one :
    IsMonicFiniteSupport
      (1 : finiteSupportSubring (G := G) (K := K)) := by
  rw [isMonicFiniteSupport_iff]
  refine ⟨0, ?_, ?_⟩ <;> simp

/-- The product of two monic finite-support series is monic. -/
theorem IsMonicFiniteSupport.mul
    {p q : finiteSupportSubring (G := G) (K := K)}
    (hp : IsMonicFiniteSupport p) (hq : IsMonicFiniteSupport q) :
    IsMonicFiniteSupport (p * q) := by
  obtain ⟨x, hxGreatest, hxCoeff⟩ := (isMonicFiniteSupport_iff p).mp hp
  obtain ⟨y, hyGreatest, hyCoeff⟩ := (isMonicFiniteSupport_iff q).mp hq
  let P : K⟦G⟧ := ((p : Nonpositive G K) : K⟦G⟧)
  let Q : K⟦G⟧ := ((q : Nonpositive G K) : K⟦G⟧)
  have hantidiagonal :
      Finset.addAntidiagonal P.isPWO_support Q.isPWO_support (x + y) = {(x, y)} := by
    ext ⟨i, j⟩
    simp only [Finset.mem_addAntidiagonal, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hi, hj, hij⟩
      have hix := hxGreatest.2 hi
      have hjy := hyGreatest.2 hj
      have hix' : i = x := by
        apply le_antisymm hix
        by_contra hxi
        have hixStrict : i < x := lt_of_not_ge hxi
        have : i + j < x + y := add_lt_add_of_lt_of_le hixStrict hjy
        exact (ne_of_lt this) hij
      subst i
      exact ⟨rfl, add_left_cancel hij⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨hxGreatest.1, hyGreatest.1, rfl⟩
  have hcoeff :
      ((((p * q : finiteSupportSubring (G := G) (K := K)) :
          Nonpositive G K) : K⟦G⟧).coeff (x + y)) = 1 := by
    have hPx : P.coeff x = 1 := by
      simpa [P] using hxCoeff
    have hQy : Q.coeff y = 1 := by
      simpa [Q] using hyCoeff
    change (P * Q).coeff (x + y) = 1
    rw [HahnSeries.coeff_mul, hantidiagonal]
    simp [hPx, hQy]
  rw [isMonicFiniteSupport_iff]
  refine ⟨x + y, ?_, hcoeff⟩
  constructor
  · exact (HahnSeries.mem_support _ _).mpr (hcoeff.trans_ne one_ne_zero)
  · intro z hz
    change z ∈ (P * Q).support at hz
    obtain ⟨i, hi, j, hj, rfl⟩ := HahnSeries.support_mul_subset hz
    exact add_le_add (hxGreatest.2 hi) (hyGreatest.2 hj)

/-- Multiplication by a nonzero constant preserves the support of a finite-support series. -/
theorem support_finiteSupportScalarHom_mul
    {k : K} (hk : k ≠ 0)
    (p : finiteSupportSubring (G := G) (K := K)) :
    (((finiteSupportScalarHom (G := G) k * p :
        finiteSupportSubring (G := G) (K := K)) : Nonpositive G K) :
          K⟦G⟧).support =
      ((p : Nonpositive G K) : K⟦G⟧).support := by
  rw [Subring.coe_mul, Subring.coe_mul, coe_finiteSupportScalarHom,
    HahnSeries.C_mul_eq_smul]
  ext x
  simp [HahnSeries.mem_support, HahnSeries.coeff_smul, hk]

/-- Multiplication by a constant scales each coefficient of a finite-support series. -/
theorem coeff_finiteSupportScalarHom_mul
    (k : K) (p : finiteSupportSubring (G := G) (K := K)) (x : G) :
    ((((finiteSupportScalarHom (G := G) k * p :
        finiteSupportSubring (G := G) (K := K)) : Nonpositive G K) :
          K⟦G⟧).coeff x) =
      k * ((p : Nonpositive G K) : K⟦G⟧).coeff x := by
  rw [Subring.coe_mul, Subring.coe_mul, coe_finiteSupportScalarHom,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
  rfl

/-- Every nonzero finite-support series is associated to a monic finite-support series. -/
theorem exists_isMonicFiniteSupport_associated
    (p : finiteSupportSubring (G := G) (K := K)) (hp : p ≠ 0) :
    ∃ q : finiteSupportSubring (G := G) (K := K),
      IsMonicFiniteSupport q ∧ Associates.mk q = Associates.mk p := by
  let support : Set G := ((p : Nonpositive G K) : K⟦G⟧).support
  have hsupportFinite : support.Finite := by
    exact (mem_finiteSupportSubring_iff
      (G := G) (K := K) (p : Nonpositive G K)).mp p.2
  have hsupportNonempty : support.Nonempty := by
    rw [HahnSeries.support_nonempty_iff]
    intro hzero
    apply hp
    apply Subtype.ext
    apply Subtype.ext
    exact hzero
  obtain ⟨x, hxSupport, hxGreatest⟩ :=
    Set.exists_max_image support id hsupportFinite hsupportNonempty
  let a : K := ((p : Nonpositive G K) : K⟦G⟧).coeff x
  have ha : a ≠ 0 := (HahnSeries.mem_support _ _).mp hxSupport
  let q : finiteSupportSubring (G := G) (K := K) :=
    finiteSupportScalarHom (G := G) a⁻¹ * p
  have hsupportQ :
      ((q : Nonpositive G K) : K⟦G⟧).support = support := by
    exact support_finiteSupportScalarHom_mul (G := G) (K := K)
      (inv_ne_zero ha) p
  have hqMonic : IsMonicFiniteSupport q := by
    refine ⟨x, ?_, ?_⟩
    · rw [hsupportQ]
      exact ⟨hxSupport, fun y hy ↦ hxGreatest y hy⟩
    · rw [coeff_finiteSupportScalarHom_mul]
      exact inv_mul_cancel₀ ha
  refine ⟨q, hqMonic, ?_⟩
  apply Associates.mk_eq_mk_iff_associated.mpr
  let uK : Kˣ := Units.mk0 a⁻¹ (inv_ne_zero ha)
  let uD : (finiteSupportSubring (G := G) (K := K))ˣ :=
    Units.map (finiteSupportScalarHom (G := G)).toMonoidHom uK
  apply Associated.symm
  refine ⟨uD, ?_⟩
  change p * finiteSupportScalarHom (G := G) a⁻¹ = q
  rw [mul_comm]

/-- A normalized representative of an associate class is zero exactly for the zero class and is
otherwise a monic representative of that class. -/
def IsNormalizedAssociateRepresentative
    (a : Associates (finiteSupportSubring (G := G) (K := K)))
    (p : finiteSupportSubring (G := G) (K := K)) : Prop :=
  (a = 0 ∧ p = 0) ∨
    (a ≠ 0 ∧ Associates.mk p = a ∧ IsMonicFiniteSupport p)

/-- Characterization of normalized representatives of finite-support associate classes. -/
theorem isNormalizedAssociateRepresentative_iff
    (a : Associates (finiteSupportSubring (G := G) (K := K)))
    (p : finiteSupportSubring (G := G) (K := K)) :
    IsNormalizedAssociateRepresentative a p ↔
      (a = 0 ∧ p = 0) ∨
        (a ≠ 0 ∧ Associates.mk p = a ∧ IsMonicFiniteSupport p) :=
  Iff.rfl

/-- Every finite-support associate class has a normalized representative. -/
theorem exists_isNormalizedAssociateRepresentative
    (a : Associates (finiteSupportSubring (G := G) (K := K))) :
    ∃ p : finiteSupportSubring (G := G) (K := K),
      IsNormalizedAssociateRepresentative a p := by
  induction a using Quotient.inductionOn with
  | _ p =>
      by_cases hp : p = 0
      · subst p
        exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨q, hqMonic, hqAssociated⟩ :=
          exists_isMonicFiniteSupport_associated p hp
        exact ⟨q, Or.inr ⟨Associates.mk_ne_zero.mpr hp,
          hqAssociated, hqMonic⟩⟩

/-- The choice-defined normalized representative of a finite-support associate class. -/
noncomputable def normalizedAssociateRepresentative
    (a : Associates (finiteSupportSubring (G := G) (K := K))) :
    finiteSupportSubring (G := G) (K := K) :=
  Classical.choose (exists_isNormalizedAssociateRepresentative a)

/-- The chosen representative satisfies the normalization predicate. -/
theorem normalizedAssociateRepresentative_is
    (a : Associates (finiteSupportSubring (G := G) (K := K))) :
    IsNormalizedAssociateRepresentative a (normalizedAssociateRepresentative a) :=
  Classical.choose_spec (exists_isNormalizedAssociateRepresentative a)

/-- The normalized representative of the zero associate class is zero. -/
@[simp]
theorem normalizedAssociateRepresentative_zero :
    normalizedAssociateRepresentative
      (0 : Associates (finiteSupportSubring (G := G) (K := K))) = 0 := by
  rcases normalizedAssociateRepresentative_is
      (0 : Associates (finiteSupportSubring (G := G) (K := K))) with h | h
  · exact h.2
  · exact (h.1 rfl).elim

/-- The associate class of the normalized representative is the original class. -/
theorem normalizedAssociateRepresentative_mk
    (a : Associates (finiteSupportSubring (G := G) (K := K))) :
    Associates.mk (normalizedAssociateRepresentative a) = a := by
  rcases normalizedAssociateRepresentative_is a with h | h
  · calc
      Associates.mk (normalizedAssociateRepresentative a) = Associates.mk 0 :=
        congrArg Associates.mk h.2
      _ = 0 := Associates.mk_zero
      _ = a := h.1.symm
  · exact h.2.1

/-- The normalized representative of a nonzero associate class is monic. -/
theorem normalizedAssociateRepresentative_isMonic_of_ne_zero
    {a : Associates (finiteSupportSubring (G := G) (K := K))}
    (ha : a ≠ 0) :
    IsMonicFiniteSupport (normalizedAssociateRepresentative a) := by
  rcases normalizedAssociateRepresentative_is a with h | h
  · exact (ha h.1).elim
  · exact h.2.2

/-- Normalized representatives are unique when every unit is a nonzero constant series. -/
theorem IsNormalizedAssociateRepresentative.eq
    (hunits : ∀ u : finiteSupportSubring (G := G) (K := K),
      IsUnit u ↔ ∃ k : K, k ≠ 0 ∧ u = finiteSupportScalarHom (G := G) k)
    {a : Associates (finiteSupportSubring (G := G) (K := K))}
    {p q : finiteSupportSubring (G := G) (K := K)}
    (hp : IsNormalizedAssociateRepresentative a p)
    (hq : IsNormalizedAssociateRepresentative a q) : p = q := by
  rcases hp with hpZero | hpNonzero
  · rcases hq with hqZero | hqNonzero
    · exact hpZero.2.trans hqZero.2.symm
    · exact (hqNonzero.1 hpZero.1).elim
  · rcases hq with hqZero | hqNonzero
    · exact (hpNonzero.1 hqZero.1).elim
    · obtain ⟨u, hu⟩ := Associates.mk_eq_mk_iff_associated.mp
        (hpNonzero.2.1.trans hqNonzero.2.1.symm)
      obtain ⟨k, hk, huk⟩ :=
        (hunits (u : finiteSupportSubring (G := G) (K := K))).mp u.isUnit
      have hqp : q = finiteSupportScalarHom (G := G) k * p := by
        calc
          q = p * (u : finiteSupportSubring (G := G) (K := K)) := hu.symm
          _ = p * finiteSupportScalarHom (G := G) k := congrArg (p * ·) huk
          _ = finiteSupportScalarHom (G := G) k * p := mul_comm _ _
      obtain ⟨xp, hxpGreatest, hxpCoeff⟩ := hpNonzero.2.2
      obtain ⟨xq, hxqGreatest, hxqCoeff⟩ := hqNonzero.2.2
      have hsupport :
          ((q : Nonpositive G K) : K⟦G⟧).support =
            ((p : Nonpositive G K) : K⟦G⟧).support := by
        rw [hqp]
        exact support_finiteSupportScalarHom_mul (G := G) (K := K) hk p
      have hxpq : xp = xq := by
        apply le_antisymm
        · exact hxqGreatest.2 (hsupport ▸ hxpGreatest.1)
        · exact hxpGreatest.2 (hsupport.symm ▸ hxqGreatest.1)
      subst xq
      have hcoeff := congrArg
        (fun r : finiteSupportSubring (G := G) (K := K) ↦
          ((r : Nonpositive G K) : K⟦G⟧).coeff xp) hqp
      rw [coeff_finiteSupportScalarHom_mul, hxpCoeff, mul_one, hxqCoeff] at hcoeff
      rw [hqp, hcoeff.symm, map_one, one_mul]

/-- The chosen normalized representative is the unique normalized representative when all units
are nonzero constant series. -/
theorem normalizedAssociateRepresentative_eq_of_is
    (hunits : ∀ u : finiteSupportSubring (G := G) (K := K),
      IsUnit u ↔ ∃ k : K, k ≠ 0 ∧ u = finiteSupportScalarHom (G := G) k)
    {a : Associates (finiteSupportSubring (G := G) (K := K))}
    {p : finiteSupportSubring (G := G) (K := K)}
    (hp : IsNormalizedAssociateRepresentative a p) :
    normalizedAssociateRepresentative a = p := by
  exact (normalizedAssociateRepresentative_is a).eq hunits hp

end

end HahnSeries.Nonpositive

end
