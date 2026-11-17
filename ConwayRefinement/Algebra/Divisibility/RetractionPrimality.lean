/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Tactic.LinearCombination
public import Mathlib.Order.Filter.Defs
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

/-!
# Primality from refinement modulo an ideal and a family of retractions

Let `T` be a commutative ring with an ideal `J` and a family of ring endomorphisms `ρ i`, indexed
along a filter, with three properties: each `ρ i` is idempotent; every element of `J` is killed by
`ρ i` for all `i` eventually; and a nonzero element fixed by `ρ i` divides an element as soon as it
divides its image under `ρ i`. If every element of `T ⧸ J` is primal, then every divisibility
relation `f ∣ x * y` refines modulo `J`, and for all `i` eventually the image `ρ i f` refines it
exactly.

In the application `T` is a ring of generalised power series with nonpositive support, `J` is the
ideal of series whose support is bounded away from zero, so that `T ⧸ J` is the ring of germs, and
`ρ i` is restriction to a convex subgroup of the exponent group. When `f = ρ i f * w` with `w`
primal, the exact refinement of `ρ i f` combines with primality of `w`, so `f` is primal.
-/

public section

variable {T ι : Type*} [CommRing T]

/-- A divisibility relation `f ∣ x * y` refines exactly after a retraction `ρ i`, for all `i`
eventually, when it refines modulo an ideal killed eventually by the retractions. -/
theorem eventually_exists_refinement_of_retractions
    (J : Ideal T) (F : Filter ι) (ρ : ι → T →+* T)
    (hidem : ∀ i x, ρ i (ρ i x) = ρ i x)
    (hJ : ∀ j ∈ J, ∀ᶠ i in F, ρ i j = 0)
    (hdvd : ∀ i q x, ρ i q = q → q ≠ 0 → q ∣ ρ i x → q ∣ x)
    {f x y : T}
    (hmod : ∃ p₁ p₂ q₁ q₂ : T,
      f - p₁ * p₂ ∈ J ∧ x - p₁ * q₁ ∈ J ∧ y - p₂ * q₂ ∈ J) :
    ∀ᶠ i in F, ρ i f ≠ 0 → ∃ g₁ g₂ : T, ρ i f = g₁ * g₂ ∧ g₁ ∣ x ∧ g₂ ∣ y := by
  obtain ⟨p₁, p₂, q₁, q₂, hf, hx, hy⟩ := hmod
  filter_upwards [hJ _ hf, hJ _ hx, hJ _ hy] with i hif hix hiy hf0
  rw [map_sub, sub_eq_zero, map_mul] at hif hix hiy
  have hg₁ : ρ i p₁ ≠ 0 := fun h ↦ hf0 (by rw [hif, h, zero_mul])
  have hg₂ : ρ i p₂ ≠ 0 := fun h ↦ hf0 (by rw [hif, h, mul_zero])
  refine ⟨ρ i p₁, ρ i p₂, hif, ?_, ?_⟩
  · exact hdvd i _ x (hidem i p₁) hg₁ ⟨ρ i q₁, hix⟩
  · exact hdvd i _ y (hidem i p₂) hg₂ ⟨ρ i q₂, hiy⟩

/-- If every element of `T ⧸ J` is primal, every divisibility relation in `T` refines modulo
`J`. -/
theorem exists_refinement_mod_of_isPrimal_quotient (J : Ideal T)
    (hQ : ∀ q : T ⧸ J, IsPrimal q) {f x y : T} (hf : f ∣ x * y) :
    ∃ p₁ p₂ q₁ q₂ : T, f - p₁ * p₂ ∈ J ∧ x - p₁ * q₁ ∈ J ∧ y - p₂ * q₂ ∈ J := by
  obtain ⟨a₁, a₂, ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩, ha⟩ :=
    hQ (Ideal.Quotient.mk J f) (by simpa only [map_mul] using map_dvd (Ideal.Quotient.mk J) hf)
  obtain ⟨p₁, rfl⟩ := Ideal.Quotient.mk_surjective a₁
  obtain ⟨p₂, rfl⟩ := Ideal.Quotient.mk_surjective a₂
  obtain ⟨q₁, rfl⟩ := Ideal.Quotient.mk_surjective c₁
  obtain ⟨q₂, rfl⟩ := Ideal.Quotient.mk_surjective c₂
  refine ⟨p₁, p₂, q₁, q₂, ?_, ?_, ?_⟩ <;> rw [← Ideal.Quotient.eq, map_mul]
  exacts [ha, hc₁, hc₂]

/-- **Primality from germs and restrictions.** Suppose that every element of `T ⧸ J` is primal,
that each retraction `ρ i` is idempotent and kills every element of `J` for all `i` eventually,
and that divisibility by a nonzero element fixed by `ρ i` can be tested after `ρ i`. Then `f` is
primal as soon as, for `i` frequently, `ρ i f ≠ 0` and `f = ρ i f * w` with `w` primal. -/
theorem isPrimal_of_frequently_retraction_mul_isPrimal [IsDomain T]
    (J : Ideal T) (F : Filter ι) (ρ : ι → T →+* T)
    (hidem : ∀ i x, ρ i (ρ i x) = ρ i x)
    (hJ : ∀ j ∈ J, ∀ᶠ i in F, ρ i j = 0)
    (hdvd : ∀ i q x, ρ i q = q → q ≠ 0 → q ∣ ρ i x → q ∣ x)
    (hQ : ∀ q : T ⧸ J, IsPrimal q)
    {f : T} (hf : ∃ᶠ i in F, ρ i f ≠ 0 ∧ ∃ w : T, f = ρ i f * w ∧ IsPrimal w) :
    IsPrimal f := by
  intro x y hxy
  obtain ⟨i, hrefine, hi0, w, hfw, hw⟩ :=
    ((eventually_exists_refinement_of_retractions J F ρ hidem hJ hdvd
      (exists_refinement_mod_of_isPrimal_quotient J hQ hxy)).and_frequently hf).exists
  obtain ⟨g₁, g₂, hg, ⟨x', rfl⟩, ⟨y', rfl⟩⟩ := hrefine hi0
  obtain ⟨z, hz⟩ := hxy
  have hg0 : g₁ * g₂ ≠ 0 := hg ▸ hi0
  have hwz : w ∣ x' * y' := ⟨z, mul_left_cancel₀ hg0 (by
    linear_combination hz + z * hfw + w * z * hg)⟩
  obtain ⟨w₁, w₂, ⟨x'', rfl⟩, ⟨y'', rfl⟩, rfl⟩ := hw hwz
  exact ⟨g₁ * w₁, g₂ * w₂, ⟨x'', by ring⟩, ⟨y'', by ring⟩, by rw [hfw, hg]; ring⟩
