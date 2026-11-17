/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.SetTheory.Ordinal.Basic

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Subalgebra.Directed

/-!
# Germs of translated truncations: the axioms

Let `A` be a ring of generalised power series over a field `K` of characteristic zero with exponents
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
neighbourhood of `0`. `RankedGerms` adds a well-founded `rank` on germs that drops along the germs
of a non-constant germ, and cutoffs below a negative exponent that keep the germ.
`TruncationGerms` combines them. The ring of germs is not assumed to be an integral domain; that it
is one is a consequence (`TruncationGerms.isDomain`).

This file states the axioms, defines `HasRepresentativesWithGermsIn`, and proves the elementary
consequences of the convolution formula. It also shows that a proper subalgebra of germs misses the
germ of a series whose germs at negative exponents lie in it (`exists_germAt_mem_germ_notMem`).
`ConwayRefinement.RingTheory.TruncationGerms.Transcendence` proves the transcendence lemma and
shows that `Q` is a polynomial ring over `K`; `ConwayRefinement.RingTheory.TruncationGerms.Series`
shows, under further axioms and given the transcendence lemma, that `A` is a polynomial ring over
the series all of whose germs are constants.
-/

universe w

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

/-- Germ maps with cutoffs and a well-founded rank that drops along the germs of a non-constant
germ. -/
structure RankedGerms (K Γ A Q : Type*) [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
    extends GermMaps K Γ A Q where
  /-- A complexity of germs with values in the ordinals, hence well-founded; for Hahn series, the
  Cantor--Bendixson value of a representative. -/
  rank : Q → Ordinal.{w}
  /-- For a non-scalar germ, the rank strictly drops along the germ maps on a left neighbourhood of
  `0`. -/
  rank_germAt_lt : ∀ b : A, germ b ∉ Set.range (algebraMap K Q) →
    ∃ ε < 0, ∀ ξ, ε < ξ → ξ < 0 → rank (germAt ξ b) < rank (germ b)
  /-- Every series has a representative with the same germ at `0`, the same germs strictly above a
  negative cutoff `ε`, and vanishing germs at and below `ε`. -/
  exists_cutoff : ∀ (b : A) (ε : Γ), ε < 0 → ∃ b' : A, germ b' = germ b ∧
    (∀ ξ, ε < ξ → germAt ξ b' = germAt ξ b) ∧ (∀ ξ, ξ ≤ ε → germAt ξ b' = 0)

/-- Berarducci's germs of generalised power series at exponents: germ maps satisfying the
convolution formula, with translated truncations, cutoffs, and a rank. The ring of germs is not
assumed to be an integral domain; that it is one is a consequence (`TruncationGerms.isDomain`). -/
structure TruncationGerms (K Γ A Q : Type*) [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
    extends ConvolutionGerms K Γ A Q, ConstantGerms K Γ A Q, RankedGerms.{w} K Γ A Q

namespace GermMaps

variable {K Γ A Q : Type*} [Field K]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
  (sys : GermMaps K Γ A Q)

/-- A subalgebra of germs has representatives with germs in it when each of its elements is the germ
of a series all of whose germs again lie in the subalgebra. -/
@[expose] def HasRepresentativesWithGermsIn (S : Subalgebra K Q) : Prop :=
  ∀ a ∈ S, ∃ b : A, sys.germ b = a ∧ ∀ ξ, sys.germAt ξ b ∈ S

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

namespace RankedGerms

variable {K Γ A Q : Type*} [Field K]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
  (sys : RankedGerms.{w} K Γ A Q)

/-- A proper subalgebra `S` of the ring of germs misses the germ of a series whose germs at
negative exponents lie in `S`: represent a germ outside `S` of minimal rank, and cut the
representative off below the exponents at which the rank drops. -/
theorem exists_germAt_mem_germ_notMem (S : Subalgebra K Q) (hS : S ≠ ⊤) :
    ∃ X : A, (∀ ξ < 0, sys.germAt ξ X ∈ S) ∧ sys.germ X ∉ S := by
  obtain ⟨g₀, hg₀⟩ : ∃ g : Q, g ∉ S := by
    by_contra h
    exact hS (Algebra.eq_top_iff.mpr fun x => not_not.mp fun hx => h ⟨x, hx⟩)
  have hwf : WellFounded fun a b : Q => sys.rank a < sys.rank b :=
    InvImage.wf sys.rank Ordinal.lt_wf
  obtain ⟨x, hxnotS, hxmin⟩ := hwf.has_min {g : Q | g ∉ S} ⟨g₀, hg₀⟩
  have hmin : ∀ y : Q, sys.rank y < sys.rank x → y ∈ S := fun y hy => by
    by_contra hyS; exact hxmin y hyS hy
  have hxnc : x ∉ Set.range (algebraMap K Q) := by
    rintro ⟨k, rfl⟩; exact hxnotS (Subalgebra.algebraMap_mem S k)
  obtain ⟨X₀, hX₀⟩ := sys.germ_surjective x
  obtain ⟨ε, hε, hdrop⟩ := sys.rank_germAt_lt X₀ (by rw [hX₀]; exact hxnc)
  obtain ⟨X, hXg, hXeq, hXvan⟩ := sys.exists_cutoff X₀ ε hε
  refine ⟨X, fun ξ hξ => ?_, by rw [hXg, hX₀]; exact hxnotS⟩
  rcases le_or_gt ξ ε with hξε | hεξ
  · rw [hXvan ξ hξε]; exact zero_mem S
  · rw [hXeq ξ hεξ]
    exact hmin _ (by simpa [hX₀] using hdrop ξ hεξ hξ)

end RankedGerms

namespace TruncationGerms

variable {K Γ A Q : Type*} [Field K]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [CommRing A] [Algebra K A] [CommRing Q] [Nontrivial Q] [Algebra K Q]
  (sys : TruncationGerms.{w} K Γ A Q)

section Comap

variable {A' Q' : Type*} [CommRing A'] [Algebra K A'] [CommRing Q'] [Nontrivial Q'] [Algebra K Q']

/-- **Pulling back germ maps.** Let `φ : A' → A` be a `K`-algebra homomorphism and let
`ι : Q' → Q` be an injective `K`-algebra homomorphism of germ rings. If a surjective germ map and
germ maps on `A'` lift the germs of `A` along `φ` and `ι`, and translated truncations and cutoffs
of elements of `A'` can be chosen in `A'`, then the germ maps on `A'` satisfy the axioms of
`TruncationGerms`. -/
def comap (φ : A' →ₐ[K] A) (ι : Q' →ₐ[K] Q) (hι : Function.Injective ι)
    (germ' : A' →ₐ[K] Q') (hgerm' : Function.Surjective germ')
    (hgerm : ∀ b, ι (germ' b) = sys.germ (φ b))
    (germAt' : Γ → A' →ₗ[K] Q') (hgermAt : ∀ γ b, ι (germAt' γ b) = sys.germAt γ (φ b))
    (htrans : ∀ (b : A') (ξ : Γ), ξ ≤ 0 →
      ∃ b' : A', ∀ ζ ≤ 0, sys.germAt ζ (φ b') = sys.germAt (ξ + ζ) (φ b))
    (hcut : ∀ (b : A') (ε : Γ), ε < 0 → ∃ b' : A', sys.germ (φ b') = sys.germ (φ b) ∧
      (∀ ξ, ε < ξ → sys.germAt ξ (φ b') = sys.germAt ξ (φ b)) ∧
        (∀ ξ, ξ ≤ ε → sys.germAt ξ (φ b') = 0)) :
    TruncationGerms K Γ A' Q' where
  germAt := germAt'
  germ := germ'
  germ_surjective := hgerm'
  germAt_zero b := hι (by rw [hgermAt, hgerm, sys.germAt_zero])
  germAt_of_pos b ξ hξ := hι (by rw [hgermAt, map_zero, sys.germAt_of_pos _ _ hξ])
  convolution_finite b c γ := by
    refine (sys.convolution_finite (φ b) (φ c) γ).subset fun β hβ ↦ ?_
    simp only [Set.mem_setOf_eq, ← hgermAt] at hβ ⊢
    exact ⟨(map_ne_zero_iff ι hι).mpr hβ.1, (map_ne_zero_iff ι hι).mpr hβ.2⟩
  convolution b c γ := by
    classical
    apply hι
    have hS := sys.convolution_finite (φ b) (φ c) γ
    have hsub : Function.support (fun β ↦ germAt' β b * germAt' (γ - β) c) ⊆
        (hS.toFinset : Set Γ) := fun β hβ ↦ by
      rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq, ← hgermAt, ← hgermAt]
      exact ⟨(map_ne_zero_iff ι hι).mpr (left_ne_zero_of_mul hβ),
        (map_ne_zero_iff ι hι).mpr (right_ne_zero_of_mul hβ)⟩
    have hsub' : Function.support (fun β ↦ sys.germAt β (φ b) * sys.germAt (γ - β) (φ c)) ⊆
        (hS.toFinset : Set Γ) := fun β hβ ↦ by
      rw [Set.Finite.coe_toFinset]
      exact ⟨left_ne_zero_of_mul hβ, right_ne_zero_of_mul hβ⟩
    rw [hgermAt, map_mul, sys.convolution, finsum_eq_finsetSum_of_support_subset _ hsub,
      finsum_eq_finsetSum_of_support_subset _ hsub', map_sum]
    simp only [map_mul, hgermAt]
  exists_translatedTruncation b ξ hξ := by
    obtain ⟨b', hb'⟩ := htrans b ξ hξ
    exact ⟨b', fun ζ hζ ↦ hι (by rw [hgermAt, hgermAt, hb' ζ hζ])⟩
  rank q := sys.rank (ι q)
  germAt_eventually_eq_zero b hb := by
    obtain ⟨k, hk⟩ := hb
    obtain ⟨ε, hε, h⟩ := sys.germAt_eventually_eq_zero (φ b)
      ⟨k, by rw [← hgerm, ← hk, AlgHom.commutes]⟩
    exact ⟨ε, hε, fun ξ h₁ h₂ ↦ hι (by rw [hgermAt, h ξ h₁ h₂, map_zero])⟩
  germ_mem_range_of_eventually b hb := by
    obtain ⟨ε, hε, h⟩ := hb
    obtain ⟨k, hk⟩ := sys.germ_mem_range_of_eventually (φ b)
      ⟨ε, hε, fun ξ h₁ h₂ ↦ by rw [← hgermAt, h ξ h₁ h₂, map_zero]⟩
    exact ⟨k, hι (by rw [AlgHom.commutes, hk, hgerm])⟩
  rank_germAt_lt b hb := by
    have hb' : sys.germ (φ b) ∉ Set.range (algebraMap K Q) := by
      rintro ⟨k, hk⟩
      exact hb ⟨k, hι (by rw [AlgHom.commutes, hk, hgerm])⟩
    obtain ⟨ε, hε, h⟩ := sys.rank_germAt_lt (φ b) hb'
    exact ⟨ε, hε, fun ξ h₁ h₂ ↦ by
      rw [hgermAt, hgerm]
      exact h ξ h₁ h₂⟩
  germAt_algebraMap k ξ hξ :=
    hι (by rw [hgermAt, AlgHom.commutes, sys.germAt_algebraMap k ξ hξ, map_zero])
  exists_cutoff b ε hε := by
    obtain ⟨b', h₀, h₁, h₂⟩ := hcut b ε hε
    exact ⟨b', hι (by rw [hgerm, hgerm, h₀]), fun ξ hξ ↦ hι (by rw [hgermAt, hgermAt, h₁ ξ hξ]),
      fun ξ hξ ↦ hι (by rw [hgermAt, h₂ ξ hξ, map_zero])⟩

end Comap

end TruncationGerms

end
