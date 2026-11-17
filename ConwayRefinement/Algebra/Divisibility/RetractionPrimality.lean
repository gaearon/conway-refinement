/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Ideal.Basic
import ConwayRefinement.Blueprint

/-!
# Primality from refinement modulo an ideal and a family of retractions

Let `T` be a commutative ring with an ideal `J` and a family of ring endomorphisms `ρ i`, indexed
along a filter, with three properties: each `ρ i` is idempotent; every element of `J` is killed by
`ρ i` for all `i` eventually; and a nonzero element fixed by `ρ i` divides an element as soon as it
divides its image under `ρ i`. If every divisibility relation `f ∣ x * y` refines modulo `J`, then
for all `i` eventually the image `ρ i f` refines it exactly.

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

/-- **Primality from germs and restrictions.** Suppose that every divisibility relation in `T`
refines modulo an ideal `J`, that each retraction `ρ i` is idempotent and kills every element of
`J` for all `i` eventually, and that divisibility by a nonzero element fixed by `ρ i` can be
tested after `ρ i`. Then `f` is primal as soon as, for `i` frequently, `ρ i f ≠ 0` and
`f = ρ i f * w` with `w` primal. -/
@[blueprint "lem:primality-from-germs-and-restrictions"
  (phase := "Refinement over Archimedean classes")
  (title := "Primality from germs and restrictions")
  (statement := /--
    Let $T$ be a domain, $J\subseteq T$ an ideal, and $(\rho_i)_{i\in I}$ a
    family of idempotent ring endomorphisms of $T$ indexed along a filter on
    $I$.  Assume that every element of $J$ is killed by $\rho_i$ for all
    sufficiently late $i$; that whenever $q=\rho_i(q)\ne0$ and
    $q\mid\rho_i(x)$, also $q\mid x$; and that every relation $f\mid xy$ in
    $T$ refines modulo $J$: there are $p_1,p_2,q_1,q_2\in T$ with
    $f\equiv p_1p_2$, $x\equiv p_1q_1$, $y\equiv p_2q_2\pmod J$.  If for
    arbitrarily late $i$ one has $\rho_i(f)\ne0$ and $f=\rho_i(f)\,w$ with
    $w$ primal, then $f$ is primal in $T$.
  -/)
  (proof := /--
    Let $f\mid xy$ and refine modulo $J$ as above.  The three differences lie
    in $J$, so for all sufficiently late $i$ they are killed by $\rho_i$; pick
    such an $i$ with $\rho_i(f)\ne0$ and $f=\rho_i(f)w$, $w$ primal.  Then
    $\rho_i(f)=g_1g_2$, $\rho_i(x)=g_1\rho_i(q_1)$ and
    $\rho_i(y)=g_2\rho_i(q_2)$ with $g_k=\rho_i(p_k)$.  Both $g_k$ are nonzero
    and fixed by $\rho_i$, so $g_1\mid x$ and $g_2\mid y$.  Write $x=g_1x'$,
    $y=g_2y'$.  Cancelling $g_1g_2\ne0$ from $g_1g_2wz=g_1g_2x'y'$ gives
    $w\mid x'y'$, hence $w=w_1w_2$ with $w_1\mid x'$ and $w_2\mid y'$.  Then
    $f=(g_1w_1)(g_2w_2)$ with $g_1w_1\mid x$ and $g_2w_2\mid y$.
  -/)]
theorem isPrimal_of_frequently_retraction_mul_isPrimal [IsDomain T]
    (J : Ideal T) (F : Filter ι) (ρ : ι → T →+* T)
    (hidem : ∀ i x, ρ i (ρ i x) = ρ i x)
    (hJ : ∀ j ∈ J, ∀ᶠ i in F, ρ i j = 0)
    (hdvd : ∀ i q x, ρ i q = q → q ≠ 0 → q ∣ ρ i x → q ∣ x)
    (hmod : ∀ f x y : T, f ∣ x * y → ∃ p₁ p₂ q₁ q₂ : T,
      f - p₁ * p₂ ∈ J ∧ x - p₁ * q₁ ∈ J ∧ y - p₂ * q₂ ∈ J)
    {f : T} (hf : ∃ᶠ i in F, ρ i f ≠ 0 ∧ ∃ w : T, f = ρ i f * w ∧ IsPrimal w) :
    IsPrimal f := by
  intro x y hxy
  obtain ⟨i, hrefine, hi0, w, hfw, hw⟩ :=
    ((eventually_exists_refinement_of_retractions J F ρ hidem hJ hdvd
      (hmod f x y hxy)).and_frequently hf).exists
  obtain ⟨g₁, g₂, hg, ⟨x', rfl⟩, ⟨y', rfl⟩⟩ := hrefine hi0
  obtain ⟨z, hz⟩ := hxy
  have hg0 : g₁ * g₂ ≠ 0 := hg ▸ hi0
  have hwz : w ∣ x' * y' := ⟨z, mul_left_cancel₀ hg0 (by
    linear_combination hz + z * hfw + w * z * hg)⟩
  obtain ⟨w₁, w₂, ⟨x'', rfl⟩, ⟨y'', rfl⟩, rfl⟩ := hw hwz
  exact ⟨g₁ * w₁, g₂ * w₂, ⟨x'', by ring⟩, ⟨y'', by ring⟩, by rw [hfw, hg]; ring⟩
