/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.SetTheory.Ordinal.Basic

import ConwayRefinement.Blueprint
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

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
@[blueprint "def:germ-axioms"
  (phase := "Polynomial presentations")
  (title := "Properties of germs used in the transcendence argument")
  (statement := /--
    Let $K$ be a field of characteristic $0$, $\Gamma$ an ordered abelian
    group, $A$ a commutative $K$-algebra and $Q$ a nontrivial commutative
    $K$-algebra.  Consider a surjective $K$-algebra homomorphism $A\to Q$,
    $b\mapsto[b]$ (the germ at $0$), $K$-linear maps $g_\gamma:A\to Q$ for
    $\gamma\in\Gamma$ (the germ at $\gamma$), and a map
    $\operatorname{rk}:Q\to\mathbf{On}$.  The following properties are used,
    for all $b,c\in A$:
    \begin{itemize}
      \item (1) $g_0(b)=[b]$, and $g_\xi(b)=0$ for $\xi>0$;
      \item (2) for every $\gamma$, only finitely many $\beta$ have
        $g_\beta(b)\ne0$ and $g_{\gamma-\beta}(c)\ne0$, and
        $g_\gamma(bc)=\sum_\beta g_\beta(b)\,g_{\gamma-\beta}(c)$;
      \item (3) for every $\xi\le0$ there is $b'\in A$ with
        $g_\zeta(b')=g_{\xi+\zeta}(b)$ for all $\zeta\le0$;
      \item (4) $[b]$ lies in the image of $K$ if and only if there is
        $\varepsilon<0$ with $g_\xi(b)=0$ for all $\xi\in(\varepsilon,0)$;
      \item (5) if $[b]$ is not in the image of $K$, there is $\varepsilon<0$ with
        $\operatorname{rk}(g_\xi(b))<\operatorname{rk}([b])$ for all
        $\xi\in(\varepsilon,0)$;
      \item (6) $g_\xi(k)=0$ for $k\in K$ and $\xi\ne0$;
      \item (7) for every $\varepsilon<0$ there is $b'\in A$ with $[b']=[b]$,
        $g_\xi(b')=g_\xi(b)$ for $\xi>\varepsilon$ and $g_\xi(b')=0$ for
        $\xi\le\varepsilon$.
    \end{itemize}
    The ring $Q$ is not assumed to be an integral domain.
  -/)
  (proof := /--
    The axioms abstract the germs of generalised power series: for
    $A=K((G^{\le0}))$ and $Q=K((G^{\le0}))/J$, $g_\gamma(b)$ is the class of
    the translated truncation $b^{|\gamma}$, property (2) is the convolution
    formula, property (3) is witnessed by $b^{|\xi}$, and $\operatorname{rk}$ is
    the Cantor--Bendixson value of a representative.
  -/)]
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
