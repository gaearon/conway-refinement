/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Germs of translated truncations: the axioms

Let `A` be a ring of generalised power series over a field `K` of characteristic zero with exponents
in an ordered abelian group `Γ`, for instance `K((G^{≤0}))`, and let `Q` be its ring of germs, for
instance `K((G^{≤0}))/J`. For an exponent `γ`, the germ of `b ∈ A` at `γ` is the germ of the
translated truncation `b^{|γ} = t^{-γ} b_{|γ}`, where `b_{|γ}` is the truncation of `b` at `γ`
(Berarducci 2000, Def. 6.1).

A `TruncationGerms K Γ A Q` records the germ `germ : A →ₐ[K] Q` to a nontrivial ring of germs and
the `K`-linear maps `germAt γ : A →ₗ[K] Q`, together with the properties of Berarducci's germs used
below: the germ at `0` is the germ of the series, germs at positive exponents vanish, the germs of
a product satisfy Berarducci's convolution formula (Berarducci 2000, Lemma 7.5), translated
truncations exist, a germ is a constant exactly when the germs vanish on a left neighbourhood of
`0`, a well-founded `rank` on germs drops along the germs of a non-constant germ, and series can be
cut off below a negative exponent without changing the germ. The ring of germs is not assumed to be
an integral domain; that it is one is a consequence (`TruncationGerms.isDomain`).

This file states the axioms, defines `HasRepresentativesWithGermsIn`, and proves the elementary
consequences of the convolution formula. `ConwayRefinement.RingTheory.TruncationGerms.Transcendence`
proves the transcendence lemma and shows that `Q` is a polynomial ring over `K`;
`ConwayRefinement.RingTheory.TruncationGerms.Series` shows, under further axioms, that `A` is a
polynomial ring over the series all of whose germs are constants.
-/

universe w

public section

/-- Berarducci's germs of generalised power series at exponents. `A` is a ring of generalised
power series with exponents in `Γ`, `Q` its nontrivial ring of germs at `0`, `germ` the germ at `0`,
and `germAt γ b` the germ at `0` of the translated truncation of `b` at `γ`. -/
structure TruncationGerms (K Γ A Q : Type*) [Field K] [CharZero K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q] where
  /-- The germ of a series at an exponent, a `K`-linear map to the ring of germs. -/
  germAt : Γ → A →ₗ[K] Q
  /-- The germ at `0`, a `K`-algebra homomorphism. -/
  germ : A →ₐ[K] Q
  /-- The germ at `0` is surjective onto the ring of germs. -/
  germ_surjective : Function.Surjective germ
  /-- The germ at exponent `0` is the germ at `0`. -/
  germAt_zero : ∀ b, germAt 0 b = germ b
  /-- The germ of a series at a positive exponent vanishes. -/
  germAt_of_pos : ∀ (b : A) (ξ : Γ), 0 < ξ → germAt ξ b = 0
  /-- The convolution fibre of two series at an exponent is finite. -/
  convolution_finite : ∀ (b c : A) (γ : Γ), {β : Γ | germAt β b ≠ 0 ∧ germAt (γ - β) c ≠ 0}.Finite
  /-- Berarducci's convolution formula for the germ of a product. -/
  convolution : ∀ (b c : A) (γ : Γ), germAt γ (b * c) = ∑ᶠ β, germAt β b * germAt (γ - β) c
  /-- For a nonpositive exponent `ξ`, there is a series whose germs at nonpositive exponents are the
  germs of `b` shifted by `ξ`: the translated truncation. -/
  exists_translatedTruncation :
    ∀ (b : A) (ξ : Γ), ξ ≤ 0 → ∃ b' : A, ∀ ζ ≤ 0, germAt ζ b' = germAt (ξ + ζ) b
  /-- A complexity of germs with values in the ordinals, hence well-founded; for Hahn series, the
  Cantor--Bendixson value of a representative. -/
  rank : Q → Ordinal.{w}
  /-- The germ of `b` at `0` is a scalar exactly when the germs of `b` vanish on a left
  neighbourhood of `0`; this direction gives the vanishing. -/
  germAt_eventually_eq_zero : ∀ b : A, germ b ∈ Set.range (algebraMap K Q) →
    ∃ ε < 0, ∀ ξ, ε < ξ → ξ < 0 → germAt ξ b = 0
  /-- The converse: eventual vanishing of the germs forces the germ at `0` to be a scalar. -/
  germ_mem_range_of_eventually : ∀ b : A, (∃ ε < 0, ∀ ξ, ε < ξ → ξ < 0 → germAt ξ b = 0) →
    germ b ∈ Set.range (algebraMap K Q)
  /-- For a non-scalar germ, the rank strictly drops along the germ maps on a left neighbourhood of
  `0`. -/
  rank_germAt_lt : ∀ b : A, germ b ∉ Set.range (algebraMap K Q) →
    ∃ ε < 0, ∀ ξ, ε < ξ → ξ < 0 → rank (germAt ξ b) < rank (germ b)
  /-- The germ of a scalar series at a nonzero exponent vanishes. -/
  germAt_algebraMap : ∀ (k : K) (ξ : Γ), ξ ≠ 0 → germAt ξ (algebraMap K A k) = 0
  /-- Every series has a representative with the same germ at `0`, the same germs strictly above a
  negative cutoff `ε`, and vanishing germs at and below `ε`. -/
  exists_cutoff : ∀ (b : A) (ε : Γ), ε < 0 → ∃ b' : A, germ b' = germ b ∧
    (∀ ξ, ε < ξ → germAt ξ b' = germAt ξ b) ∧ (∀ ξ, ξ ≤ ε → germAt ξ b' = 0)

namespace TruncationGerms

variable {K Γ A Q : Type*} [Field K] [CharZero K]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
  (sys : TruncationGerms K Γ A Q)

/-- A subalgebra of germs has representatives with germs in it when each of its elements is the germ
of a series all of whose germs again lie in the subalgebra. -/
@[expose] def HasRepresentativesWithGermsIn (S : Subalgebra K Q) : Prop :=
  ∀ a ∈ S, ∃ b : A, sys.germ b = a ∧ ∀ ξ, sys.germAt ξ b ∈ S

/-- Isolate the diagonal term of the convolution: the remaining terms range over a finite set. -/
theorem germAt_mul_diag (b c : A) (ξ : Γ) :
    sys.germAt ξ (b * c) = sys.germAt ξ b * sys.germAt 0 c +
      ∑ β ∈ (insert ξ (sys.convolution_finite b c ξ).toFinset).erase ξ,
        sys.germAt β b * sys.germAt (ξ - β) c := by
  classical
  set g : Γ → Q := fun β => sys.germAt β b * sys.germAt (ξ - β) c with hg
  have hsupp : Function.support g ⊆
      (↑(insert ξ (sys.convolution_finite b c ξ).toFinset) : Set Γ) := by
    intro β hβ
    have hβ' : g β ≠ 0 := hβ
    rw [Finset.coe_insert]
    refine Set.mem_insert_iff.mpr (Or.inr ?_)
    rw [Set.Finite.coe_toFinset]
    exact ⟨left_ne_zero_of_mul hβ', right_ne_zero_of_mul hβ'⟩
  have h1 : sys.germAt ξ (b * c) = ∑ β ∈ insert ξ (sys.convolution_finite b c ξ).toFinset, g β := by
    rw [sys.convolution b c ξ]; exact finsum_eq_finsetSum_of_support_subset g hsupp
  rw [h1, ← Finset.add_sum_erase _ g (Finset.mem_insert_self ξ _)]
  congr 1
  simp [hg, sub_self]

/-- The convolution diagonal split over an arbitrary finite index set containing the support. -/
theorem germAt_mul_sum (b c : A) (ξ : Γ) (s : Finset Γ)
    (hs : ∀ β, sys.germAt β b * sys.germAt (ξ - β) c ≠ 0 → β ∈ s) :
    sys.germAt ξ (b * c) = sys.germAt ξ b * sys.germAt 0 c +
      ∑ β ∈ (insert ξ s).erase ξ, sys.germAt β b * sys.germAt (ξ - β) c := by
  classical
  set g : Γ → Q := fun β => sys.germAt β b * sys.germAt (ξ - β) c with hg
  have hsupp : Function.support g ⊆ (↑(insert ξ s) : Set Γ) :=
    fun β hβ => Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hs β hβ))
  have h1 : sys.germAt ξ (b * c) = ∑ β ∈ insert ξ s, g β := by
    rw [sys.convolution b c ξ]; exact finsum_eq_finsetSum_of_support_subset g hsupp
  rw [h1, ← Finset.add_sum_erase _ g (Finset.mem_insert_self ξ s)]
  congr 1
  simp [hg, sub_self]

/-- A finite-support convolution sum whose factors lie in a subalgebra lies in it. -/
theorem finsum_convolution_mem (T : Subalgebra K Q) (b b' : A) (ξ : Γ)
    (hb : ∀ β, sys.germAt β b ∈ T) (hb' : ∀ β, sys.germAt β b' ∈ T) :
    ∑ᶠ β, sys.germAt β b * sys.germAt (ξ - β) b' ∈ T := by
  classical
  have hsupp : Function.support (fun β => sys.germAt β b * sys.germAt (ξ - β) b') ⊆
      (↑(sys.convolution_finite b b' ξ).toFinset : Set Γ) := by
    intro β hβ
    have hβ' : sys.germAt β b * sys.germAt (ξ - β) b' ≠ 0 := hβ
    rw [Set.Finite.coe_toFinset]
    exact ⟨left_ne_zero_of_mul hβ', right_ne_zero_of_mul hβ'⟩
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  exact Subalgebra.sum_mem _ fun β _ => T.mul_mem (hb β) (hb' _)

/-- Each off-diagonal convolution correction of `b * X` lies in `S`, when all germs of `b` and the
negative germs of `X` lie in `S`. -/
theorem offDiagonal_mem (S : Subalgebra K Q) {X : A} (hX : ∀ ξ < 0, sys.germAt ξ X ∈ S)
    (b : A) (h0 : ∀ ξ, sys.germAt ξ b ∈ S) {ξ : Γ} :
    sys.germAt ξ (b * X) - sys.germAt ξ b * sys.germ X ∈ S := by
  classical
  rw [sys.germAt_mul_diag b X ξ, sys.germAt_zero X, add_sub_cancel_left]
  apply Subalgebra.sum_mem
  intro β hβ
  have hβne : β ≠ ξ := Finset.ne_of_mem_erase hβ
  rcases le_or_gt β 0 with hβ0 | hβ0
  · rcases lt_or_gt_of_ne hβne with hlt | hgt
    · have : sys.germAt (ξ - β) X = 0 :=
        sys.germAt_of_pos X (ξ - β) (by simpa using sub_pos.mpr hlt)
      rw [this, mul_zero]; exact zero_mem S
    · have hlt0 : ξ - β < 0 := by simpa using sub_neg.mpr hgt
      exact S.mul_mem (h0 β) (hX _ hlt0)
  · rw [sys.germAt_of_pos b β hβ0, zero_mul]; exact zero_mem S

/-- The bottom subalgebra (the scalars) has representatives with germs in it: a scalar is
represented by the constant series, whose only nonzero germ sits at exponent `0`. -/
theorem hasRepresentativesWithGermsIn_bot :
    sys.HasRepresentativesWithGermsIn (⊥ : Subalgebra K Q) := by
  intro a ha
  rw [Algebra.mem_bot] at ha
  obtain ⟨k, hk⟩ := ha
  refine ⟨algebraMap K A k, ?_, fun ξ => ?_⟩
  · rw [AlgHom.commutes]; exact hk
  · rcases eq_or_ne ξ 0 with rfl | hξ
    · rw [sys.germAt_zero, AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ k
    · rw [sys.germAt_algebraMap k ξ hξ]; exact zero_mem _

end TruncationGerms

end
