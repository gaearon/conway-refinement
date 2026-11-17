/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Germ.GermAt

import ConwayRefinement.Blueprint
import ConwayRefinement.Topology.Order.PWOAddition

/-!
# The exponents at which a series has a nonzero germ

Let `G` be a nontrivial ordered abelian group with its order topology and `K` a field.
The germ of a nonpositive series `b` at `γ` is nonzero exactly when
`γ` lies in the closure of the support of `b` (`germAt_ne_zero_iff`). Consequently the set of such
exponents is well-founded, a series is determined by its germs, truncations keep the germs at
exponents up to the cutoff and kill the others, and multiplication by a monomial `t^γ` translates
germs by `γ`. A germ at `γ` is a constant exactly when the germs vanish on a left neighbourhood of
`γ`.
-/

open Set
open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [Field K]

/-- The set of exponents at which a series has a nonzero germ is the closure of its support. -/
theorem setOf_germAt_ne_zero (b : Nonpositive G K) :
    {γ | germAt γ b ≠ 0} = closure (b : HahnSeries G K).support :=
  Set.ext fun γ => germAt_ne_zero_iff b γ

/-- The set of exponents at which a series has a nonzero germ is well-founded. -/
theorem isWF_setOf_germAt_ne_zero (b : Nonpositive G K) : {γ | germAt γ b ≠ 0}.IsWF := by
  rw [setOf_germAt_ne_zero]
  exact (Set.IsPWO.closure (b : HahnSeries G K).isPWO_support).isWF

/-- A series all of whose germs vanish is zero. -/
theorem eq_zero_of_forall_germAt_eq_zero (b : Nonpositive G K) (h : ∀ γ, germAt γ b = 0) :
    b = 0 := by
  refine Subtype.ext (HahnSeries.coeff_injective (funext fun δ => ?_))
  rw [ZeroMemClass.coe_zero, HahnSeries.coeff_zero]
  by_contra hδ
  exact (germAt_ne_zero_iff b δ).mpr (subset_closure hδ) (h δ)

/-- The truncation `b_{|η}` of a nonpositive series, the part of `b` with exponents at most `η`. -/
def truncation (η : G) (b : Nonpositive G K) : Nonpositive G K :=
  ⟨truncLE η (b : HahnSeries G K), by
    rw [mem_nonpositiveSubring]; exact (support_truncLE_subset η _).trans (support_subset b)⟩

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] in
@[simp]
theorem coe_truncation (η : G) (b : Nonpositive G K) :
    (truncation η b : HahnSeries G K) = truncLE η (b : HahnSeries G K) := (rfl)

/-- The truncation of `b` at `η` keeps the germs at exponents `≤ η` and kills the others. -/
theorem germAt_truncation (b : Nonpositive G K) (η ξ : G) :
    germAt ξ (truncation η b) = if ξ ≤ η then germAt ξ b else 0 := by
  split_ifs with hξ
  · rw [germAt_apply, germAt_apply]
    congr 1
    apply Subtype.ext
    rw [coe_translatedTruncation, coe_translatedTruncation]
    ext δ
    simp only [coeff_translate, HahnSeries.coeff_truncLE, truncation]
    split_ifs with h1 h2 <;> first | rfl | exact absurd (h1.trans hξ) h2
  · by_contra hne
    have hmem := (germAt_ne_zero_iff _ ξ).mp hne
    have hsub : (truncation η b : HahnSeries G K).support ⊆ Set.Iic η := by
      intro δ hδ
      rw [HahnSeries.mem_support] at hδ
      change (truncLE η (b : HahnSeries G K)).coeff δ ≠ 0 at hδ
      rw [HahnSeries.coeff_truncLE] at hδ
      by_contra h
      exact hδ (if_neg h)
    exact hξ (closure_minimal hsub isClosed_Iic hmem)

/-- The truncation of `b` at `η` keeps the germs at exponents `≤ η` and kills the others. -/
theorem exists_germAt_truncation (b : Nonpositive G K) (η : G) :
    ∃ b' : Nonpositive G K, ∀ ξ, germAt ξ b' = if ξ ≤ η then germAt ξ b else 0 :=
  ⟨truncation η b, germAt_truncation b η⟩

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] in
/-- Multiplication by the monomial `t^γ`, `γ ≤ 0`, translates germs by `γ`. -/
theorem germAt_single_mul (γ : G) (hγ : γ ≤ 0) (b : Nonpositive G K) (ξ : G) :
    germAt ξ (single γ 1 hγ * b) = germAt (ξ - γ) b := by
  have hcoe : ((single γ 1 hγ * b : Nonpositive G K) : HahnSeries G K) =
      translate γ (b : HahnSeries G K) := by
    rw [Subring.coe_mul, coe_single, single_one_mul_eq_translate]
  rw [germAt_apply, germAt_apply]
  congr 1
  apply Subtype.ext
  rw [coe_translatedTruncation, coe_translatedTruncation, hcoe]
  ext δ
  simp only [coeff_translate, HahnSeries.coeff_truncLE]
  have h1 : δ - -ξ - γ = δ - -(ξ - γ) := by abel
  have h2 : (δ - -ξ ≤ ξ) ↔ (δ - -(ξ - γ) ≤ ξ - γ) := by
    rw [show δ - -(ξ - γ) = δ - -ξ - γ by abel]; exact (sub_le_sub_iff_right γ).symm
  by_cases h : δ - -ξ ≤ ξ
  · rw [if_pos h, if_pos (h2.mp h), h1]
  · rw [if_neg h, if_neg (fun h' => h (h2.mpr h'))]

/-- The germ of `b` at `γ` is a constant exactly when the germs of `b` vanish on a left
neighbourhood of `γ`. -/
@[blueprint "lem:constant-germs"
  (phase := "Germs of translated truncations")
  (title := "Characterisation of constant germs")
  (statement := /--
    For $b\in K((G^{\le0}))$ and $\gamma\in G$, the germ $[b^{|\gamma}]$ lies in
    $K$ if and only if there is $\varepsilon<0$ with $[b^{|\gamma+\zeta}]=0$ for
    all $\zeta\in(\varepsilon,0)$.
  -/)
  (proof := /--
    By \ref{lem:germs-of-translated-truncation} the germs of $b^{|\gamma}$ at $\zeta\le0$ are the
    germs of $b$ at $\gamma+\zeta$, for every $\gamma\in G$, so it suffices to treat $\gamma=0$.
    If $b-k\in J$ for $k\in K$, its support and hence its closed support lie in
    $(-\infty,c]$ for some $c<0$. By \ref{lem:nonzero-germs} its germs vanish on $(c,0)$.
    The constant series $k$ also has zero germ there, so the germs of $b$ vanish on $(c,0)$.
    Conversely, if the germ at $\xi<0$ vanishes, then $b^{|\xi}\in J$. Its coefficient at $0$,
    the coefficient of $t^\xi$ in $b$, is therefore $0$. If this holds throughout
    $(\varepsilon,0)$, subtracting the constant coefficient of $b$ leaves support in
    $(-\infty,\varepsilon]$, so the difference lies in $J$.
  -/)]
theorem germAt_mem_range_algebraMap_iff (b : Nonpositive G K) (γ : G) :
    germAt γ b ∈ Set.range (algebraMap K (Nonpositive G K ⧸
        boundedAwayIdeal G K)) ↔
      ∃ ε < (0 : G), ∀ ζ, ε < ζ → ζ < 0 → germAt (γ + ζ) b = 0 := by
  rw [germAt_apply]
  constructor
  · intro h
    obtain ⟨ε, hε, hvan⟩ := exists_germAt_eq_zero_of_mk_mem_range _ h
    exact ⟨ε, hε, fun ζ hεζ hζ => by
      rw [← germAt_translatedTruncation b γ hζ.le]; exact hvan ζ hεζ hζ⟩
  · rintro ⟨ε, hε, hvan⟩
    exact mk_mem_range_of_germAt_eq_zero _ ⟨ε, hε, fun ζ hεζ hζ => by
      rw [germAt_translatedTruncation b γ hζ.le]; exact hvan ζ hεζ hζ⟩

/-- A series with finite support has a constant germ at every exponent. -/
theorem germAt_mem_range_algebraMap_of_finite (b : Nonpositive G K)
    (hb : (b : HahnSeries G K).support.Finite) (γ : G) :
    germAt γ b ∈ Set.range (algebraMap K (Nonpositive G K ⧸
        boundedAwayIdeal G K)) := by
  rw [germAt_mem_range_algebraMap_iff]
  obtain ⟨ε₀, hε₀⟩ := exists_lt (0 : G)
  set s := (hb.toFinset.filter (· < γ)).image (· - γ)
  have hs : ∀ x ∈ s, x < 0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact sub_neg.mpr (Finset.mem_filter.mp hy).2
  refine ⟨(insert ε₀ s).max' (Finset.insert_nonempty _ _), ?_, fun ζ hεζ hζ => ?_⟩
  · exact (Finset.max'_lt_iff _ _).mpr fun x hx => by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hε₀
      · exact hs x hx
  · by_contra hne
    have hne := (germAt_ne_zero_iff b (γ + ζ)).mp hne
    rw [hb.isClosed.closure_eq] at hne
    have hmem : γ + ζ - γ ∈ insert ε₀ s := Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨γ + ζ, Finset.mem_filter.mpr ⟨hb.mem_toFinset.mpr hne, by simpa using hζ⟩, rfl⟩)
    have := Finset.le_max' _ _ hmem
    exact absurd hεζ (not_lt.mpr (by simpa using this))

end HahnSeries.Nonpositive
