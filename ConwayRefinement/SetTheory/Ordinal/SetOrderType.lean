/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Order.WellFoundedSet

public import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Order type of a partially well-ordered set

A partially well-ordered subset of a linear order is well-ordered by the induced strict order.
This module assigns it that ordinary ordinal order type. The order is always the ambient order,
with no reversal.

The union theorem proves a slightly more general form of LM24, Fact 2.2.3(2): the two sets need not
first be exhibited as subsets of a common well-ordered set. Its right-hand side uses addition in
`NatOrdinal`, hence Hessenberg's natural sum rather than ordinary ordinal addition.

Mathlib supplies `Ordinal.type_sum_lex`, `Ordinal.type_eq`, `OrderIso.sumLexIioIci`, and ordinal
enumeration, but no theorem equivalent to LM24, Fact 2.2.3(1), nor its uniqueness consequence.
The proof reuses the lexicographic-sum and order-isomorphism infrastructure rather than defining
a new ordinal representation.
-/

universe u

public noncomputable section

namespace Set.IsPWO

open Ordinal

variable {α : Type u} [LinearOrder α] {s t : Set α}

@[reducible] private def isWellOrder (hs : s.IsPWO) :
    IsWellOrder s (Subrel (· < ·) (· ∈ s)) where
  wf := hs.isWF
  trichotomous := fun _ _ hab hba ↦
    Subtype.ext (le_antisymm (le_of_not_gt hba) (le_of_not_gt hab))

/-- The ordinary ordinal order type of a partially well-ordered subset of a linear order. -/
def orderType (hs : s.IsPWO) : Ordinal.{u} :=
  @Ordinal.type s (Subrel (· < ·) (· ∈ s)) (isWellOrder hs)

/-- A partially well-ordered set has order type zero exactly when it is empty. -/
@[simp]
theorem orderType_eq_zero (hs : s.IsPWO) : hs.orderType = 0 ↔ s = ∅ := by
  letI := isWellOrder hs
  rw [orderType, Ordinal.type_eq_zero_iff_isEmpty, isEmpty_subtype]
  exact Set.eq_empty_iff_forall_notMem.symm

/-- Compute the order type through an order isomorphism from the set to a well-ordered type. -/
theorem orderType_eq_typeLT_of_orderIso {A : Type u} [LinearOrder A] [WellFoundedLT A]
    (hs : s.IsPWO) (e : s ≃o A) : hs.orderType = typeLT A := by
  letI := isWellOrder hs
  let er : Subrel (· < ·) (· ∈ s) ≃r (· < · : A → A → Prop) :=
    e.toRelIsoLT
  exact er.ordinalType_congr

/-- Inclusion of partially well-ordered subsets cannot decrease their ordinary order type. -/
theorem orderType_mono (hs : s.IsPWO) (ht : t.IsPWO) (h : s ⊆ t) :
    hs.orderType ≤ ht.orderType := by
  letI := isWellOrder hs
  letI := isWellOrder ht
  exact (Subrel.inclusionEmbedding (· < ·) h).ordinal_type_le

/-- A well-ordered set has order type `a + b` exactly when it is the union of a set of order
type `a` followed strictly by a set of order type `b`. This is LM24, Fact 2.2.3(1). -/
theorem orderType_eq_add_iff (hs : s.IsPWO) (a b : Ordinal.{u}) :
    hs.orderType = a + b ↔
      ∃ (s₀ s₁ : Set α) (hs₀ : s₀.IsPWO) (hs₁ : s₁.IsPWO),
        s₀ ⊆ s ∧
          s₁ ⊆ s ∧
          (∀ x ∈ s₀, ∀ y ∈ s₁, x < y) ∧
          hs₀.orderType = a ∧
          hs₁.orderType = b ∧
          s = s₀ ∪ s₁ := by
  constructor
  · intro htype
    letI : WellFoundedLT s := ⟨hs.isWF⟩
    letI : WellFoundedLT (a.ToType ⊕ₗ b.ToType) :=
      ⟨Sum.lex_wf wellFounded_lt wellFounded_lt⟩
    have htypes : typeLT s = typeLT (a.ToType ⊕ₗ b.ToType) := by
      calc
        typeLT s = hs.orderType :=
          (hs.orderType_eq_typeLT_of_orderIso (OrderIso.refl s)).symm
        _ = a + b := htype
        _ = typeLT (a.ToType ⊕ₗ b.ToType) := by
          symm
          calc
            typeLT (a.ToType ⊕ₗ b.ToType) =
                Ordinal.type (Sum.Lex (· < · : a.ToType → a.ToType → Prop)
                  (· < · : b.ToType → b.ToType → Prop)) :=
              (Sum.Lex.toLexRelIsoLT (α := a.ToType)
                (β := b.ToType)).ordinalType_congr.symm
            _ = a + b := by
              rw [Ordinal.type_sum_lex, Ordinal.type_toType, Ordinal.type_toType]
    let e : s ≃o a.ToType ⊕ₗ b.ToType :=
      OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp htypes))
    let left : a.ToType ↪o α :=
      OrderEmbedding.ofStrictMono
        (fun x ↦ (e.symm (Sum.inlₗ x)).1)
        (fun _ _ hxy ↦ e.symm.strictMono (Sum.Lex.inl_strictMono hxy))
    let right : b.ToType ↪o α :=
      OrderEmbedding.ofStrictMono
        (fun x ↦ (e.symm (Sum.inrₗ x)).1)
        (fun _ _ hxy ↦ e.symm.strictMono (Sum.Lex.inr_strictMono hxy))
    let s₀ : Set α := Set.range left
    let s₁ : Set α := Set.range right
    have hs₀s : s₀ ⊆ s := by
      rintro x ⟨y, rfl⟩
      exact (e.symm (Sum.inlₗ y)).2
    have hs₁s : s₁ ⊆ s := by
      rintro x ⟨y, rfl⟩
      exact (e.symm (Sum.inrₗ y)).2
    let hs₀ : s₀.IsPWO := hs.mono hs₀s
    let hs₁ : s₁.IsPWO := hs.mono hs₁s
    have hs₀type : hs₀.orderType = a := by
      rw [hs₀.orderType_eq_typeLT_of_orderIso left.orderIso.symm,
        Ordinal.type_toType]
    have hs₁type : hs₁.orderType = b := by
      rw [hs₁.orderType_eq_typeLT_of_orderIso right.orderIso.symm,
        Ordinal.type_toType]
    have hbefore : ∀ x ∈ s₀, ∀ y ∈ s₁, x < y := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact e.symm.strictMono (Sum.Lex.inl_lt_inr x y)
    have hunion : s = s₀ ∪ s₁ := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases heq : e ⟨x, hx⟩ with y | y
        · left
          refine ⟨y, ?_⟩
          change (e.symm (Sum.inlₗ y)).1 = x
          have h := e.symm_apply_apply ⟨x, hx⟩
          rw [heq] at h
          exact congrArg Subtype.val h
        · right
          refine ⟨y, ?_⟩
          change (e.symm (Sum.inrₗ y)).1 = x
          have h := e.symm_apply_apply ⟨x, hx⟩
          rw [heq] at h
          exact congrArg Subtype.val h
      · exact Set.union_subset hs₀s hs₁s
    exact ⟨s₀, s₁, hs₀, hs₁, hs₀s, hs₁s, hbefore, hs₀type, hs₁type, hunion⟩
  · rintro ⟨s₀, s₁, hs₀, hs₁, hs₀s, hs₁s, hbefore, hs₀type, hs₁type, hunion⟩
    let f : s₀ ⊕ₗ s₁ → s
      | Sum.inlₗ x => ⟨x, hs₀s x.2⟩
      | Sum.inrₗ x => ⟨x, hs₁s x.2⟩
    have hf : StrictMono f := by
      intro x y hxy
      rcases x with x | x <;> rcases y with y | y
      · have hxy' : x < y :=
          (Sum.Lex.inl_lt_inl_iff (α := s₀) (β := s₁)).mp hxy
        exact hxy'
      · exact hbefore x x.2 y y.2
      · exact (Sum.Lex.not_inr_lt_inl hxy).elim
      · have hxy' : x < y :=
          (Sum.Lex.inr_lt_inr_iff (α := s₀) (β := s₁)).mp hxy
        exact hxy'
    have hsurj : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rw [hunion] at hx
      rcases hx with hx | hx
      · exact ⟨Sum.inlₗ ⟨x, hx⟩, rfl⟩
      · exact ⟨Sum.inrₗ ⟨x, hx⟩, rfl⟩
    let e : s₀ ⊕ₗ s₁ ≃o s := hf.orderIsoOfSurjective f hsurj
    letI : WellFoundedLT s₀ := ⟨hs₀.isWF⟩
    letI : WellFoundedLT s₁ := ⟨hs₁.isWF⟩
    letI : WellFoundedLT (s₀ ⊕ₗ s₁) :=
      ⟨Sum.lex_wf wellFounded_lt wellFounded_lt⟩
    calc
      hs.orderType = typeLT (s₀ ⊕ₗ s₁) :=
        hs.orderType_eq_typeLT_of_orderIso e.symm
      _ = typeLT s₀ + typeLT s₁ := Ordinal.type_sum_lex _ _
      _ = hs₀.orderType + hs₁.orderType := by
        rw [hs₀.orderType_eq_typeLT_of_orderIso (OrderIso.refl s₀),
          hs₁.orderType_eq_typeLT_of_orderIso (OrderIso.refl s₁)]
      _ = a + b := by rw [hs₀type, hs₁type]

/-- A partially well-ordered set is finite exactly when its order type is below `ω`. -/
theorem finite_iff_orderType_lt_omega (hs : s.IsPWO) :
    s.Finite ↔ hs.orderType < Ordinal.omega0 := by
  letI := isWellOrder hs
  rw [Set.Finite, ← Cardinal.mk_lt_aleph0_iff]
  rw [orderType, ← Ordinal.card_type (Subrel (· < ·) (· ∈ s)), Ordinal.card_lt_aleph0]

/-- Every infinite partially well-ordered set is an initial block of nonzero limit order type
followed by a finite final block. The split removes the finite remainder after ordinal division of
the order type by `ω`. -/
theorem finite_or_exists_limit_initial_finite_final (hs : s.IsPWO) :
    s.Finite ∨
      ∃ (s₀ s₁ : Set α) (hs₀ : s₀.IsPWO) (_ : s₁.IsPWO),
        s₀ ⊆ s ∧
          s₁ ⊆ s ∧
          (∀ x ∈ s₀, ∀ y ∈ s₁, x < y) ∧
          Order.IsSuccLimit hs₀.orderType ∧
          s₁.Finite ∧
          s = s₀ ∪ s₁ := by
  by_cases hfinite : s.Finite
  · exact Or.inl hfinite
  · right
    have homega : Ordinal.omega0 ≤ hs.orderType := by
      exact le_of_not_gt (hfinite ∘ hs.finite_iff_orderType_lt_omega.mpr)
    have hdivpos : 0 < hs.orderType / Ordinal.omega0 := by
      exact (Ordinal.div_pos Ordinal.omega0_ne_zero).mpr homega
    have hlimit : Order.IsSuccLimit
        (Ordinal.omega0 * (hs.orderType / Ordinal.omega0)) :=
      Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hdivpos
    have hmodlt : hs.orderType % Ordinal.omega0 < Ordinal.omega0 :=
      Ordinal.mod_lt hs.orderType Ordinal.omega0_ne_zero
    have hdecomp :
        hs.orderType = Ordinal.omega0 * (hs.orderType / Ordinal.omega0) +
          hs.orderType % Ordinal.omega0 :=
      (Ordinal.div_add_mod hs.orderType Ordinal.omega0).symm
    obtain ⟨s₀, s₁, hs₀, hs₁, hs₀s, hs₁s, hbefore, hs₀type, hs₁type, hunion⟩ :=
      (hs.orderType_eq_add_iff
        (Ordinal.omega0 * (hs.orderType / Ordinal.omega0))
        (hs.orderType % Ordinal.omega0)).mp hdecomp
    refine ⟨s₀, s₁, hs₀, hs₁, hs₀s, hs₁s, hbefore, ?_, ?_, hunion⟩
    · rwa [hs₀type]
    · rw [hs₁.finite_iff_orderType_lt_omega, hs₁type]
      exact hmodlt

private def belowRelIso {x : α} (hx : x ∈ s) :
    Subrel (· < ·) (· ∈ s ∩ Set.Iio x) ≃r
      Subrel (Subrel (· < ·) (· ∈ s))
        (Subrel (· < ·) (· ∈ s) · ⟨x, hx⟩) where
  toFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  invFun a := ⟨a.1.1, a.1.2, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The part of a partially well-ordered set strictly below one of its elements has strictly smaller
order type. -/
theorem orderType_inter_Iio_lt (hs : s.IsPWO) {x : α} (hx : x ∈ s) :
    (hs.mono (s := s ∩ Set.Iio x) Set.inter_subset_left).orderType < hs.orderType := by
  letI := isWellOrder hs
  let hbelow := hs.mono (s := s ∩ Set.Iio x) Set.inter_subset_left
  letI := isWellOrder hbelow
  calc
    hbelow.orderType = Ordinal.type
        (Subrel (Subrel (· < ·) (· ∈ s))
          (Subrel (· < ·) (· ∈ s) · ⟨x, hx⟩)) :=
      (belowRelIso hx).ordinalType_congr
    _ = Ordinal.typein (Subrel (· < ·) (· ∈ s)) ⟨x, hx⟩ :=
      Ordinal.type_subrel _ _
    _ < hs.orderType := Ordinal.typein_lt_type _ _

/-- If the ordinary order type is a limit ordinal, every member has a strictly larger member. -/
theorem exists_gt_of_isSuccLimit_orderType
    (hs : s.IsPWO) (hlimit : Order.IsSuccLimit hs.orderType)
    {x : α} (hx : x ∈ s) :
    ∃ y ∈ s, x < y := by
  letI : WellFoundedLT s := ⟨hs.isWF⟩
  have hprelimit : Order.IsSuccPrelimit
      (Ordinal.type (fun x y : s ↦ x < y)) := by
    rw [← hs.orderType_eq_typeLT_of_orderIso (OrderIso.refl s)]
    exact hlimit.isSuccPrelimit
  letI : NoMaxOrder s :=
    Ordinal.isSuccPrelimit_type_lt_iff.mp hprelimit
  obtain ⟨y, hxy⟩ : ∃ y : s, (⟨x, hx⟩ : s) < y :=
    exists_gt (⟨x, hx⟩ : s)
  exact ⟨y.1, y.2, hxy⟩

end Set.IsPWO
