/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Order.Module.HahnEmbedding

import ConwayRefinement.HahnSeries.Nonpositive.ArchimedeanClasses
import ConwayRefinement.Blueprint
public import ConwayRefinement.HahnSeries.ConvexSubgroup.Restriction
public import Mathlib.Data.Real.Basic
import ConwayRefinement.HahnSeries.CharZero
import ConwayRefinement.HahnSeries.IntegerPart.Regrouping
import Mathlib.Data.Set.Card

/-!
# Primality for finitely many Archimedean support classes

Let `σ` be the leading Archimedean class met by the support of `x ∈ Z + R((G^{<0}))_κ`, that is,
the class of its order. Regroup along the strict inner ball `C = G_{≺σ}`. The support of the
regrouped series lies in the image of the closed ball `G_{⪯σ}` in `G ⧸ C`, which the chosen stratum
`H_σ ≃ ℝ` identifies with `ℝ`. Every series over `ℝ` is primal, and primality in a convex exponent
subgroup passes to the ambient ring, so the regrouped series is primal. Its constant coefficient is
the restriction of `x` to `C`, which meets strictly fewer classes. Assumption `(A2)_σ` supplies the
fraction-field condition, and primality through regrouping completes the induction.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open scoped HahnSeries

universe u v w

namespace FiniteArchimedeanClass

variable (K : Type w) {G : Type u}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]

theorem lt_mk_of_mem_ball {c : FiniteArchimedeanClass G} {g : G} (hg : g ∈ ball K c) :
    c.1 < ArchimedeanClass.mk g := by
  by_cases hg0 : g = 0
  · subst hg0
    rw [ArchimedeanClass.mk_zero]
    exact lt_top_iff_ne_top.mpr c.2
  · exact (FiniteArchimedeanClass.mem_ball_iff K).mp hg hg0

theorem mem_ball_of_lt_mk {c : FiniteArchimedeanClass G} {g : G}
    (hg : c.1 < ArchimedeanClass.mk g) : g ∈ ball K c :=
  (FiniteArchimedeanClass.mem_ball_iff K).mpr fun _ ↦ hg

/-- The open Archimedean ball is a convex subgroup. -/
instance ball_isConvex (c : FiniteArchimedeanClass G) : (ball K c).toAddSubgroup.IsConvex where
  ordConnected := ⟨fun _ hg _ hh _ hk ↦ mem_ball_of_lt_mk K <|
    (lt_min (lt_mk_of_mem_ball K hg) (lt_mk_of_mem_ball K hh)).trans_le
      (ArchimedeanClass.min_le_mk_of_le_of_le hk.1 hk.2)⟩

end FiniteArchimedeanClass

namespace HahnEmbedding.ArchimedeanStrata

variable {K : Type w} {G : Type u}
variable [Field K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)

/-- The stratum at `c`, mapped to the quotient by the strict inner ball. -/
def stratumToQuotient : u.stratum c →+ G ⧸ ball K c :=
  (ball K c).mkQ.toAddMonoidHom.comp (u.stratum c).subtype.toAddMonoidHom

theorem stratumToQuotient_apply (s : u.stratum c) :
    u.stratumToQuotient c s = (ball K c).mkQ s :=
  (rfl)

/-- The projection of a stratum to the quotient by the inner ball is an order embedding. -/
theorem stratumToQuotient_le_iff (s t : u.stratum c) :
    u.stratumToQuotient c s ≤ u.stratumToQuotient c t ↔ s ≤ t := by
  change ((s : G) : G ⧸ (ball K c).toAddSubgroup) ≤ ((t : G) : G ⧸ (ball K c).toAddSubgroup) ↔ _
  rw [ConvexQuotient.mk_le_mk_iff]
  refine ⟨fun h ↦ h.elim id fun hmem ↦ ?_, Or.inl⟩
  have h0 := (Submodule.disjoint_def.mp (u.disjoint_ball_stratum c)) _ hmem
    ((u.stratum c).sub_mem t.2 s.2)
  exact (sub_eq_zero.mp h0).ge

theorem stratumToQuotient_injective : Function.Injective (u.stratumToQuotient c) :=
  fun s t h ↦ le_antisymm ((u.stratumToQuotient_le_iff c s t).mp h.le)
    ((u.stratumToQuotient_le_iff c t s).mp h.ge)

/-- The closed ball at `c` maps into the image of the stratum. -/
theorem mkQ_mem_range_stratumToQuotient {g : G} (hg : g ∈ closedBall K c) :
    (ball K c).mkQ g ∈ Set.range (u.stratumToQuotient c) := by
  rw [← u.ball_sup_stratum_eq c] at hg
  obtain ⟨b, hb, s, hs, rfl⟩ := Submodule.mem_sup.mp hg
  refine ⟨⟨s, hs⟩, ?_⟩
  rw [stratumToQuotient_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq]
  simpa using (ball K c).neg_mem hb

/-- The image of the stratum in the quotient by the inner ball is order-connected. -/
theorem ordConnected_range_stratumToQuotient :
    (Set.range (u.stratumToQuotient c)).OrdConnected := by
  have hcb : ∀ s : u.stratum c, (s : G) ∈ closedBall K c := fun s ↦ by
    rw [← u.ball_sup_stratum_eq c]
    exact Submodule.mem_sup_right s.2
  refine ⟨?_⟩
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ γ ⟨hsγ, hγt⟩
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective (ball K c) γ
  change ((s : G) : G ⧸ (ball K c).toAddSubgroup) ≤ ((g : G) : G ⧸ (ball K c).toAddSubgroup)
    at hsγ
  change ((g : G) : G ⧸ (ball K c).toAddSubgroup) ≤ ((t : G) : G ⧸ (ball K c).toAddSubgroup)
    at hγt
  rw [ConvexQuotient.mk_le_mk_iff] at hsγ hγt
  apply u.mkQ_mem_range_stratumToQuotient c
  have hball : (ball K c : Set G) ⊆ closedBall K c := fun _ h ↦ (ball_lt_closedBall (K := K)).le h
  rcases hsγ with hsg | hsg
  · rcases hγt with hgt | hgt
    · exact (closedBall_ordConnected c).out (hcb s) (hcb t) ⟨hsg, hgt⟩
    · simpa using (closedBall K c).sub_mem (hcb t) (hball hgt)
  · simpa using (closedBall K c).add_mem (hball hsg) (hcb s)

end HahnEmbedding.ArchimedeanStrata

namespace HahnSeries.CardSuppLTTruncationIntegerPart

variable {K : Type w} {G : Type u} {R : Type v} {κ : Cardinal.{u}}
variable [Field K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R] [Fact (ℵ₀ < κ)]

/-- **Primality at the leading Archimedean class.** If the restriction of a series to the strict
inner ball of the class of its order is primal, then so is the series. -/
theorem isPrimal_of_isPrimal_restrict_leadingClass [CharZero R] [Fact κ.IsRegular]
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (horder : (x : R⟦G⟧).order ≠ 0)
    (hA1 : Nonempty (u.stratum (FiniteArchimedeanClass.mk _ horder) ≃+o ℝ))
    (hA2 : κ ≤ Order.cof (ball K (FiniteArchimedeanClass.mk _ horder)) ∨
      (Subsingleton (ball K (FiniteArchimedeanClass.mk _ horder)) ∧
        Subring.fracSubring Z = ⊤))
    (hres : IsPrimal (restrictToAddSubgroup Z
      (ball K (FiniteArchimedeanClass.mk _ horder)).toAddSubgroup x)) :
    IsPrimal x := by
  classical
  set c := FiniteArchimedeanClass.mk _ horder with hc
  have hxmem := (mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2
  have hsupp : ∀ g ∈ (x : R⟦G⟧).support, g ∈ closedBall K c := fun g hg ↦
    (FiniteArchimedeanClass.mem_closedBall_iff K).mpr fun _ ↦
      ArchimedeanClass.mk_le_mk_of_le_of_nonpos
        (HahnSeries.order_le_of_coeff_ne_zero ((HahnSeries.mem_support _ _).mp hg)) (hxmem.1 hg)
  refine isPrimal_of_isPrimal_regroupAmbient (ball K c) Z x ?_
    (isPrimal_restrictDomain_of_isPrimal_restrictToAddSubgroup Z _
      AddSubgroup.IsConvex.ordConnected x hres)
    (fun _ ↦ fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_le_cof_or_subsingleton Z hA2)
  let φ := u.stratumToQuotient c
  have hw : ((regroupAmbient (κ := κ) (ball K c) Z x :
      CardSuppLTNonpositive (G := G ⧸ ball K c)
        (L := CardSuppLTField (G := ball K c) (R := R) (κ := κ)) (κ := κ)) :
        (CardSuppLTField (G := ball K c) (R := R) (κ := κ))⟦G ⧸ ball K c⟧).support ⊆
      Set.range φ := by
    rw [regroupAmbient_apply, CardSuppLTNonpositive.coe_truncationIntegerPartEquivResidueSubring,
      support_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv,
      support_convexQuotientSplitRingEquiv]
    rintro _ ⟨g, hg, rfl⟩
    exact u.mkQ_mem_range_stratumToQuotient c (hsupp g hg)
  rw [← mapDomain_restrictDomain φ (u.stratumToQuotient_injective c)
    (u.stratumToQuotient_le_iff c) ⊤ _ hw]
  exact isPrimal_mapDomain_of_isPrimal ⊤ φ (u.stratumToQuotient_injective c)
    (u.stratumToQuotient_le_iff c) (u.ordConnected_range_stratumToQuotient c)
    (CardSuppLTNonpositive.isPrimal_of_orderIso_real hA1.some _)

/-- Under assumptions `(A1)`--`(A3)` of L'Innocente and Mantova (LM24, Theorem 9.0.1), every
series meeting only finitely many Archimedean classes is primal: every Archimedean stratum is
order-isomorphic to `ℝ`, every strict ball has cofinality at least `κ` or is zero with `R` the
fraction field of `Z`, and `Z` is pre-Schreier. -/
@[blueprint "thm:finite-support-classes-primality"
  (phase := "Finitely many Archimedean classes")
  (title := "Primality for finitely many Archimedean support classes")
  (statement := /--
    Let $K$ be an Archimedean ordered field, $G$ an ordered $K$-vector
    space, $R$ a field of characteristic zero, $\kappa>\aleph_0$ a regular
    cardinal, and $Z\subseteq R$ a pre-Schreier subring.  At every nonzero
    Archimedean class $\sigma$, choose an additive complement $H_\sigma$ to
    $G_{\prec\sigma}$ in $G_{\preceq\sigma}$ that is order additively
    isomorphic to $\mathbb R$.  Assume that $G_{\prec\sigma}$ either has
    cofinality at least $\kappa$, or is zero and every element of $R$ is a
    fraction of elements of $Z$.  Every element of
    $Z+R((G^{<0}))_\kappa$ whose support meets only finitely many Archimedean
    classes is primal.
  -/)
  (proof := /--
    Induct on the number of Archimedean classes met by the support of $x$.  If
    the order of $x$ is $0$, then $x$ is a constant of $Z$ and is primal
    because $Z$ is pre-Schreier.  Otherwise let $\sigma$ be the class of the
    order of $x$ and regroup along $C=G_{\prec\sigma}$.  The support of $x$
    lies in $G_{\preceq\sigma}$, whose image in $G/C$ is the image of
    $H_\sigma\simeq\mathbb R$; this image is convex.  Every element of
    $L((\mathbb R^{\le0}))$ is primal by \ref{thm:hahn-series-primality}, and
    primality in a convex exponent subgroup passes to the ambient ring, so
    the regrouped series is primal.  The restriction $x_{\vert C}$ meets only
    classes of $x$ other than $\sigma$, so it is primal by induction, and
    $(A2)_\sigma$ makes $R((C))_\kappa$ the fraction field of
    $Z+R((C^{<0}))_\kappa$.  Conclude by
    \ref{lem:primality-through-regrouping}.
  -/)]
theorem isPrimal_of_supportArchimedeanClasses_finite [CharZero R]
    [Fact κ.IsRegular] (Z : Subring R) [DecompositionMonoid Z]
    (u : HahnEmbedding.ArchimedeanStrata K G)
    (hA1 : ∀ c : FiniteArchimedeanClass G, Nonempty (u.stratum c ≃+o ℝ))
    (hA2 : ∀ c : FiniteArchimedeanClass G, κ ≤ Order.cof (ball K c) ∨
      (Subsingleton (ball K c) ∧ Subring.fracSubring Z = ⊤))
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hfinite : (ArchimedeanClass.mk '' (x : R⟦G⟧).support).Finite) : IsPrimal x := by
  classical
  let classes := fun y : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z ↦
    ArchimedeanClass.mk '' (y : R⟦G⟧).support
  suffices h : ∀ n : ℕ, ∀ y, (classes y).ncard = n → (classes y).Finite → IsPrimal y from
    h _ x rfl hfinite
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hn hyfinite
    by_cases horder : (y : R⟦G⟧).order = 0
    · exact isPrimal_of_order_eq_zero Z y (by simpa only [coe_toNonpositiveRingHom] using horder)
    set c := FiniteArchimedeanClass.mk _ horder
    have hy0 : (y : R⟦G⟧) ≠ 0 := fun h ↦ horder (by rw [h, HahnSeries.order_zero])
    have hcy : c.1 ∈ classes y :=
      ⟨_, (HahnSeries.mem_support _ _).mpr (HahnSeries.coeff_order_eq_zero.not.mpr hy0), rfl⟩
    let r := restrictToAddSubgroup Z (ball K c).toAddSubgroup y
    have hsub : classes r ⊆ classes y := by
      rintro _ ⟨g, hg, rfl⟩
      rw [coe_restrictToAddSubgroup, HahnSeries.support_filter] at hg
      exact ⟨g, hg.1, rfl⟩
    have hcr : c.1 ∉ classes r := by
      rintro ⟨g, hg, hgc⟩
      rw [coe_restrictToAddSubgroup, HahnSeries.support_filter] at hg
      exact (FiniteArchimedeanClass.lt_mk_of_mem_ball K hg.2).ne hgc.symm
    have hlt : (classes r).ncard < n :=
      hn ▸ Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr
        ⟨hsub, fun h ↦ hcr (h ▸ hcy)⟩) hyfinite
    exact isPrimal_of_isPrimal_restrict_leadingClass u Z y horder (hA1 c) (hA2 c)
      (ih _ hlt r rfl (hyfinite.subset hsub))

end HahnSeries.CardSuppLTTruncationIntegerPart
