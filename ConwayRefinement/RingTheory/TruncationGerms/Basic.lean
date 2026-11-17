/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Order.WellFoundedSet

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Subalgebra.Directed

/-!
# Germs of translated truncations: the axioms

Let `A` be a ring of generalised power series over a field `K` with exponents
in an ordered abelian group `Γ`, for instance `K((G^{≤0}))`, and let `Q` be its ring of germs, for
instance `K((G^{≤0}))/J`. For an exponent `γ`, the germ of `b ∈ A` at `γ` is the germ of the
translated truncation `b^{|γ} = t^{-γ} b_{|γ}`, where `b_{|γ}` is the truncation of `b` at `γ`
(Berarducci 2000, Def. 6.1).

The axioms are split by the facts they record, so that each consequence depends only on the facts
it uses. `GermMaps` records the germ `germ : A →ₐ[K] Q` onto a nontrivial ring of germs and the
`K`-linear maps `germAt γ : A →ₗ[K] Q`: the germ at `0` is the germ of the series, germs at positive
exponents vanish, and constants have no other germs. `ConvolutionGerms` adds Berarducci's
convolution formula (Berarducci 2000, Lemma 7.5). `ConstantGerms` adds translated truncations and
the characterisation of constant germs: a germ is a constant exactly when the germs vanish on a left
neighbourhood of `0`. In `TruncationGerms` the exponents with nonzero germ form a well-ordered
set. This will allow the first nonzero germ above a given bound to serve as a nonzero scalar.

This file states the axioms, defines `HasRepresentativesWithGermsIn`, and proves the elementary
consequences of the convolution formula. It also shows that a proper subalgebra of germs misses the
germ of a series whose germs at negative exponents lie in it (`exists_germAt_mem_germ_mem_notMem`).
`ConwayRefinement.RingTheory.TruncationGerms.Transcendence` proves the transcendence lemma and
shows that `Q` is a polynomial ring over `K`; `ConwayRefinement.RingTheory.TruncationGerms.Series`
shows, under further axioms and given the transcendence lemma, that `A` is a polynomial ring over
the series all of whose germs are constants.
-/

public section

/-- Germ maps on a ring `A` of generalised power series with exponents in `Γ`: a surjective germ
`germ : A →ₐ[K] Q` onto a nontrivial ring of germs and `K`-linear maps `germAt γ : A →ₗ[K] Q`, such
that the germ at `0` is the germ, germs at positive exponents vanish, and constants have no germs at
nonzero exponents. -/
structure GermMaps (K Γ A Q : Type*) [Field K]
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
  /-- The germ of a scalar series at a nonzero exponent vanishes. -/
  germAt_algebraMap : ∀ (k : K) (ξ : Γ), ξ ≠ 0 → germAt ξ (algebraMap K A k) = 0

/-- Germ maps satisfying Berarducci's convolution formula for the germs of a product
(Berarducci 2000, Lemma 7.5). -/
structure ConvolutionGerms (K Γ A Q : Type*) [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
    extends GermMaps K Γ A Q where
  /-- The convolution fibre of two series at an exponent is finite. -/
  convolution_finite : ∀ (b c : A) (γ : Γ), {β : Γ | germAt β b ≠ 0 ∧ germAt (γ - β) c ≠ 0}.Finite
  /-- Berarducci's convolution formula for the germ of a product. -/
  convolution : ∀ (b c : A) (γ : Γ), germAt γ (b * c) = ∑ᶠ β, germAt β b * germAt (γ - β) c

/-- Germ maps with translated truncations and the characterisation of constant germs: the germ of a
series is a scalar exactly when its germs vanish on a left neighbourhood of `0`. -/
structure ConstantGerms (K Γ A Q : Type*) [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
    extends GermMaps K Γ A Q where
  /-- For a nonpositive exponent `ξ`, there is a series whose germs at nonpositive exponents are the
  germs of `b` shifted by `ξ`: the translated truncation. -/
  exists_translatedTruncation :
    ∀ (b : A) (ξ : Γ), ξ ≤ 0 → ∃ b' : A, ∀ ζ ≤ 0, germAt ζ b' = germAt (ξ + ζ) b
  /-- The germ of `b` at `0` is a scalar exactly when the germs of `b` vanish on a left
  neighbourhood of `0`; this direction gives the vanishing. -/
  germAt_eventually_eq_zero : ∀ b : A, germ b ∈ Set.range (algebraMap K Q) →
    ∃ ε < 0, ∀ ξ, ε < ξ → ξ < 0 → germAt ξ b = 0
  /-- The converse: eventual vanishing of the germs forces the germ at `0` to be a scalar. -/
  germ_mem_range_of_eventually : ∀ b : A, (∃ ε < 0, ∀ ξ, ε < ξ → ξ < 0 → germAt ξ b = 0) →
    germ b ∈ Set.range (algebraMap K Q)

/-- Germ maps satisfying the convolution formula and the characterisation of constant germs,
with a well-ordered set of exponents at which each series has nonzero germ. -/
structure TruncationGerms (K Γ A Q : Type*) [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
    extends ConvolutionGerms K Γ A Q, ConstantGerms K Γ A Q where
  /-- The exponents at which a series has nonzero germ are well ordered. -/
  germSupport_isWF : ∀ b : A, {ξ | germAt ξ b ≠ 0}.IsWF

namespace GermMaps

variable {K Γ A Q : Type*} [Field K]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
  (sys : GermMaps K Γ A Q)

/-- A subalgebra of germs has representatives with germs in it when each of its elements is the germ
of a series all of whose germs again lie in the subalgebra. -/
@[expose] def HasRepresentativesWithGermsIn (S : Subalgebra K Q) : Prop :=
  ∀ a ∈ S, ∃ b : A, sys.germ b = a ∧ ∀ ξ, sys.germAt ξ b ∈ S

/-- Every germ admits a representative with germs in the full ring. -/
theorem hasRepresentativesWithGermsIn_top :
    sys.HasRepresentativesWithGermsIn (⊤ : Subalgebra K Q) := by
  intro a _
  obtain ⟨b, hb⟩ := sys.germ_surjective a
  exact ⟨b, hb, fun _ ↦ trivial⟩

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

/-- The union of a chain of sets generating subalgebras with representatives whose germs lie in
them generates a subalgebra with the same property. -/
theorem hasRepresentativesWithGermsIn_adjoin_sUnion {c : Set (Set Q)} (hcn : c.Nonempty)
    (hchain : IsChain (· ⊆ ·) c)
    (hc : ∀ T ∈ c, sys.HasRepresentativesWithGermsIn (Algebra.adjoin K T)) :
    sys.HasRepresentativesWithGermsIn (Algebra.adjoin K (⋃₀ c)) := by
  intro a ha
  haveI : Nonempty ↥c := hcn.to_subtype
  have hdir : Directed (· ≤ ·) fun s : c => Algebra.adjoin K (s : Set Q) := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    rcases hchain.total hs ht with hst | hts
    · exact ⟨⟨t, ht⟩, Algebra.adjoin_mono hst, le_rfl⟩
    · exact ⟨⟨s, hs⟩, le_rfl, Algebra.adjoin_mono hts⟩
  have hcoe : (↑(Algebra.adjoin K (⋃₀ c)) : Set Q) =
      ⋃ s : c, (Algebra.adjoin K (s : Set Q) : Set Q) := by
    rw [Set.sUnion_eq_iUnion, Algebra.adjoin_iUnion]
    exact Subalgebra.coe_iSup_of_directed hdir
  have ha' : a ∈ (↑(Algebra.adjoin K (⋃₀ c)) : Set Q) := ha
  rw [hcoe, Set.mem_iUnion] at ha'
  obtain ⟨s, has⟩ := ha'
  obtain ⟨b, hbg, hbs⟩ := hc s s.2 a has
  exact ⟨b, hbg, fun ξ => Algebra.adjoin_mono (Set.subset_sUnion_of_mem s.2) (hbs ξ)⟩

/-- Between two subalgebras, translating to the first germ outside the smaller one gives a germ
in the larger one whose representative has all negative-exponent germs in the smaller one. -/
theorem exists_germAt_mem_germ_mem_notMem (hwf : ∀ b : A, {ξ | sys.germAt ξ b ≠ 0}.IsWF)
    (htrans : ∀ (b : A) (ξ : Γ), ξ ≤ 0 →
      ∃ b' : A, ∀ ζ ≤ 0, sys.germAt ζ b' = sys.germAt (ξ + ζ) b)
    {P S : Subalgebra K Q} (hP : sys.HasRepresentativesWithGermsIn P) (hSP : S < P) :
    ∃ X : A, (∀ ξ < 0, sys.germAt ξ X ∈ S) ∧ sys.germ X ∈ P ∧ sys.germ X ∉ S := by
  obtain ⟨g, hgP, hgS⟩ := SetLike.exists_of_lt hSP
  obtain ⟨b, hb, hall⟩ := hP g hgP
  let D : Set Γ := {ξ | sys.germAt ξ b ∉ S}
  have hD : D.IsWF := (hwf b).subset fun _ hi hzero ↦ hi (hzero ▸ S.zero_mem)
  have h0 : (0 : Γ) ∈ D := by simpa [D, sys.germAt_zero, hb] using hgS
  let ξ := hD.min ⟨0, h0⟩
  obtain ⟨X, hX⟩ := htrans b ξ (hD.min_le _ h0)
  have hx : sys.germ X = sys.germAt ξ b := by simpa [sys.germAt_zero] using hX 0 le_rfl
  refine ⟨X, fun ζ hζ ↦ ?_, hx ▸ hall ξ, hx ▸ hD.min_mem _⟩
  rw [hX ζ hζ.le]
  by_contra h
  exact (not_lt_of_ge (hD.min_le _ h)) (show ξ + ζ < ξ by simpa using hζ)

end GermMaps

namespace ConvolutionGerms

variable {K Γ A Q : Type*} [Field K]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
  (sys : ConvolutionGerms K Γ A Q)

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

end ConvolutionGerms

namespace ConstantGerms

variable {K Γ A Q : Type*} [Field K]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
  (sys : ConstantGerms K Γ A Q)
  (hwf : ∀ b : A, {ξ | sys.germAt ξ b ≠ 0}.IsWF)

/-- If the germs vanish on an interval immediately below a nonpositive exponent, the germ at
that exponent is a scalar. -/
theorem germAt_mem_range_of_gap (b : A) {ε ξ : Γ} (hlo : ε < ξ) (hhi : ξ ≤ 0)
    (hgap : ∀ t, ε < t → t < ξ → sys.germAt t b = 0) :
    sys.germAt ξ b ∈ Set.range (algebraMap K Q) := by
  obtain ⟨B, hB⟩ := sys.exists_translatedTruncation b ξ hhi
  have hBg : sys.germ B = sys.germAt ξ b := by simpa [sys.germAt_zero] using hB 0 le_rfl
  rw [← hBg]
  refine sys.germ_mem_range_of_eventually B ⟨ε - ξ, sub_neg.mpr hlo, fun ζ hζ hneg ↦ ?_⟩
  rw [hB ζ hneg.le]
  exact hgap _ (by simpa [add_comm] using sub_lt_iff_lt_add.mp hζ) (by simpa using hneg)

include hwf in
/-- Every nonzero germ has a nonzero scalar germ above each negative cutoff, possibly at zero. -/
theorem exists_germAt_eq_scalar (b : A) (hb : sys.germ b ≠ 0) {ε : Γ} (hε : ε < 0) :
    ∃ ξ, ε < ξ ∧ ξ ≤ 0 ∧ ∃ k : K, k ≠ 0 ∧ sys.germAt ξ b = algebraMap K Q k := by
  let D : Set Γ := {ξ | ε < ξ ∧ sys.germAt ξ b ≠ 0}
  have hD : D.IsWF := (hwf b).subset fun _ h ↦ h.2
  have h0 : (0 : Γ) ∈ D := ⟨hε, by rwa [sys.germAt_zero]⟩
  let ξ := hD.min ⟨0, h0⟩
  obtain ⟨hεξ, hξb⟩ := hD.min_mem ⟨0, h0⟩
  have hξ : ξ ≤ 0 := hD.min_le _ h0
  obtain ⟨k, hk⟩ := sys.germAt_mem_range_of_gap b hεξ hξ fun t hεt ht ↦ by
    by_contra hn
    exact (not_lt_of_ge (hD.min_le _ ⟨hεt, hn⟩)) ht
  refine ⟨ξ, hεξ, hξ, k, ?_, hk.symm⟩
  rintro rfl
  exact hξb (hk.symm.trans (map_zero _))

include hwf in
/-- Two germs proportional to their germs at all nearby negative exponents differ by a scalar
factor if the second germ is nonzero. -/
theorem exists_germ_eq_smul_of_proportional (U V : A) (hV : sys.germ V ≠ 0)
    (h : ∃ ε < 0, ∀ ξ, ε < ξ → ξ < 0 →
      sys.germ V * sys.germAt ξ U = sys.germ U * sys.germAt ξ V) :
    ∃ c : K, sys.germ U = c • sys.germ V := by
  obtain ⟨ε, hε, hrel⟩ := h
  let D : Set Γ := {ξ | ε < ξ ∧ (sys.germAt ξ U ≠ 0 ∨ sys.germAt ξ V ≠ 0)}
  have hD : D.IsWF := ((hwf U).union (hwf V)).subset fun _ h ↦ h.2
  have h0 : (0 : Γ) ∈ D := ⟨hε, Or.inr (by rwa [sys.germAt_zero])⟩
  let ξ := hD.min ⟨0, h0⟩
  obtain ⟨hlo, hne⟩ := hD.min_mem ⟨0, h0⟩
  have hhi : ξ ≤ 0 := hD.min_le _ h0
  have hgap (B : A) (hB : ∀ t, sys.germAt t B ≠ 0 → sys.germAt t U ≠ 0 ∨ sys.germAt t V ≠ 0) :
      sys.germAt ξ B ∈ Set.range (algebraMap K Q) := by
    apply sys.germAt_mem_range_of_gap B hlo hhi
    intro t hεt ht
    by_contra hn
    exact (not_lt_of_ge (hD.min_le _ ⟨hεt, hB _ hn⟩)) ht
  obtain ⟨u, hu⟩ := hgap U (fun _ ↦ Or.inl)
  obtain ⟨v, hv⟩ := hgap V (fun _ ↦ Or.inr)
  have hξ : sys.germ V * sys.germAt ξ U = sys.germ U * sys.germAt ξ V := by
    rcases hhi.lt_or_eq with hlt | heq
    · exact hrel ξ hlo hlt
    · simp [heq, sys.germAt_zero, mul_comm]
  have he : u • sys.germ V = v • sys.germ U := by
    simpa only [Algebra.smul_def, hu, hv, mul_comm] using hξ
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_smul] at he
    have hu0 : u = 0 := by
      by_contra h
      exact hV (by simpa [inv_smul_smul₀ h] using congrArg (u⁻¹ • ·) he)
    subst u
    simp only [map_zero] at hu hv
    exact hne.elim (· hu.symm) (· hv.symm)
  exact ⟨v⁻¹ * u, by rw [mul_smul, he, inv_smul_smul₀ hv0]⟩

end ConstantGerms

end
