/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Nonpositive.ArchimedeanClasses
public import ConwayRefinement.HahnSeries.BoundedSupport.EmbDomain

import ConwayRefinement.Blueprint
public import ConwayRefinement.HahnSeries.ConvexSubgroup.CommonTail
public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.Algebra.Order.Module.HahnEmbedding
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
import ConwayRefinement.HahnSeries.CharZero
import ConwayRefinement.HahnSeries.IntegerPart.CommonTailGerms
import ConwayRefinement.HahnSeries.IntegerPart.FiniteClasses
public import ConwayRefinement.HahnSeries.IntegerPart.Regrouping
import ConwayRefinement.HahnSeries.IntegerPart.SupportClassFactorization

/-!
# Primality in bounded Hahn integer parts

The main theorem `HahnSeries.CardSuppLTTruncationIntegerPart.isPrimal` proves that every element of
`Z + R((G^{<0}))_κ` is primal under the stratum, cofinality, and completeness hypotheses described
there. It is proved by induction on the support classes. The induction rank is the order type of the
Archimedean classes met by the non-zero support. A supplied theorem handles the case in which this
set is finite. At every infinite rank, the classes split into a non-zero limit initial segment `T₀`
and a finite final segment. Let `C` be the common tail below `T₀`, `Γ = G ⧸ C`, `L = R((C))_κ` and
`D = Z + R((C^{<0}))_κ`. Regrouping exponents along `C` identifies `Z + R((G^{<0}))_κ` with the `D +
M` construction `D + L((Γ^{<0}))_κ` inside `L((Γ^{≤0}))_κ`. The constant term meets only finitely
many classes, so it is primal in `D`, and the fraction-field hypothesis on `D` handles a zero
constant term. Primality in `L((Γ^{≤0}))_κ` follows from primality in its ring of germs, which is a
polynomial ring when `Γ` is Cauchy complete: restriction to the closed ball of a small quotient
class met by the support refines every divisibility relation exactly, and the complementary factor
has strictly smaller rank, hence is primal by induction.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open HahnSeries.CardSuppLTTruncationIntegerPart
open scoped HahnSeries

universe u v w

namespace HahnSeries.CardSuppLTTruncationIntegerPart

section FiniteTail

variable {G : Type u} {R : Type v} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field R] [Fact (ℵ₀ < κ)]

/-- Finite-class primality in an ambient exponent group descends to every convex exponent
subgroup. -/
private theorem isPrimal_addSubgroup_of_ambient_finiteClasses
    (Z : Subring R)
    (hfinite : ∀ x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      (ArchimedeanClass.mk '' (x : HahnSeries G R).support).Finite → IsPrimal x)
    (P : AddSubgroup G) (hP : (P : Set G).OrdConnected)
    (a : cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z)
    (ha : (ArchimedeanClass.mk '' (a : HahnSeries P R).support).Finite) : IsPrimal a := by
  let inc : P →+ G := P.subtype
  have hinci : Function.Injective inc := Subtype.val_injective
  have hinco : ∀ x y : P, inc x ≤ inc y ↔ x ≤ y := fun _ _ ↦ Iff.rfl
  let A := mapDomain inc hinci hinco Z a
  have hAfinite : (ArchimedeanClass.mk '' (A : HahnSeries G R).support).Finite := by
    have hsupport : (A : HahnSeries G R).support = inc '' (a : HahnSeries P R).support := by
      rw [coe_mapDomain]
      exact HahnSeries.support_embDomain _ _
    rw [hsupport]
    let e : P →+o G :=
      { toFun := inc
        map_zero' := map_zero inc
        map_add' := map_add inc
        monotone' := fun _ _ h ↦ h }
    let ac : ArchimedeanClass P → ArchimedeanClass G := ArchimedeanClass.orderHom e
    have heq : ArchimedeanClass.mk '' (inc '' (a : HahnSeries P R).support) =
        ac '' (ArchimedeanClass.mk '' (a : HahnSeries P R).support) := by
      ext c
      constructor
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨ArchimedeanClass.mk p, ⟨p, hp, rfl⟩,
          ArchimedeanClass.orderHom_mk e p⟩
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨inc p, ⟨p, hp, rfl⟩, (ArchimedeanClass.orderHom_mk e p).symm⟩
    rw [heq]
    exact ha.image ac
  apply isPrimal_of_isPrimal_mapDomain inc hinci hinco Z
  · have hrange : Set.range inc = (P : Set G) := by
      ext x
      constructor
      · rintro ⟨p, rfl⟩
        exact p.2
      · exact fun hx ↦ ⟨⟨x, hx⟩, rfl⟩
    rw [hrange]
    exact hP
  exact hfinite A hAfinite

/-- The common-tail coefficient of a series is primal when its remaining support classes form
a finite block and finite-class primality is known in the ambient exponent group. -/
theorem isPrimal_restrictDomain_tailSubmodule_of_ambient_finiteClasses
    [Module ℚ G] [PosSMulMono ℚ G]
    (Z : Subring R)
    (hfinite : ∀ y : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      (ArchimedeanClass.mk '' (y : HahnSeries G R).support).Finite → IsPrimal y)
    (T₀ T₁ : Set (ArchimedeanClass G))
    (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b) (hT₁ : T₁.Finite)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hxclasses : ArchimedeanClass.mk '' (x : HahnSeries G R).support ⊆ T₀ ∪ T₁) :
    let P := FiniteArchimedeanClass.tailSubmodule ℚ
      {c : FiniteArchimedeanClass G | c.1 ∈ T₀}
    IsPrimal (restrictDomain P.toAddSubgroup.subtype Subtype.val_injective
      (fun _ _ ↦ Iff.rfl) Z x) := by
  let P := FiniteArchimedeanClass.tailSubmodule ℚ
    {c : FiniteArchimedeanClass G | c.1 ∈ T₀}
  apply isPrimal_addSubgroup_of_ambient_finiteClasses Z hfinite P.toAddSubgroup
    (inferInstance : P.toAddSubgroup.IsConvex).ordConnected
  have hfinite' :=
    HahnSeries.supportArchimedeanClasses_coeff_zero_convexQuotientSplitRingEquiv_finite
      (K := ℚ) T₀ T₁ hT₀gt hT₁ (x : HahnSeries G R) hxclasses
  rw [HahnSeries.coeff_zero_convexQuotientSplitRingEquiv] at hfinite'
  have hre : ((restrictDomain P.toAddSubgroup.subtype Subtype.val_injective
      (fun _ _ ↦ Iff.rfl) Z x :
      cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) : HahnSeries P R) =
      HahnSeries.restrictDomain (HahnSeries.submoduleOrderEmbedding P)
        (x : HahnSeries G R) := by
    ext p
    rw [coe_restrictDomain, HahnSeries.restrictDomain_coeff,
      HahnSeries.restrictDomain_coeff]
    congr 1
    exact HahnSeries.submoduleOrderEmbedding_apply P p |>.symm
  rw [hre]
  exact hfinite'

end FiniteTail

open Classical in
/-- At a quotient class met by the support, the regrouped series is its closed-ball restriction
times a primal factor, when every series of smaller support-class order type is primal. -/
private theorem restriction_mul_isPrimal_at_support_class
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R] {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R) (T : Set (FiniteArchimedeanClass G))
    (q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T))
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hqocc : q.1 ∈ ArchimedeanClass.mk ''
      (Submodule.Quotient.mk (p := FiniteArchimedeanClass.tailSubmodule ℚ T) ''
        (x : HahnSeries G R).support))
    (ih : ∀ w : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z w)).orderType <
        (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z x)).orderType → IsPrimal w) :
    ∃ t w : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      restrictToAddSubgroup Z ((FiniteArchimedeanClass.closedBallAddSubgroup q).comap
        (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ.toAddMonoidHom) x = t ∧
      x = t * w ∧ IsPrimal w ∧ (w : R⟦G⟧).coeff 0 ≠ 0 := by
  let C : AddSubgroup G := (FiniteArchimedeanClass.closedBallAddSubgroup q).comap
    (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ.toAddMonoidHom
  have hfilter0 : HahnSeries.filter (· ∈ C) (x : HahnSeries G R) ≠ 0 := by
    obtain ⟨z, ⟨r, hr, hqr⟩, hzq⟩ := hqocc
    intro hzero
    have hcoeff := congrArg (fun y : HahnSeries G R ↦ y.coeff r) hzero
    rw [HahnSeries.coeff_filter, if_pos] at hcoeff
    · exact (HahnSeries.mem_support _ _).mp hr hcoeff
    · change (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ r ∈
        FiniteArchimedeanClass.closedBallAddSubgroup q
      apply FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff.mpr
      intro _hr0
      change q.1 ≤ ArchimedeanClass.mk ((FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ r)
      change (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ r = z at hqr
      rw [hqr, hzq]
  have hfactor := exists_factor_with_smaller_support_class_orderType Z T q x hqocc hfilter0
  obtain ⟨t, w, ht, hfac, hw1, hrank⟩ := hfactor
  refine ⟨t, w, ?_, hfac, ih w hrank, by rw [hw1]; exact one_ne_zero⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (coe_restrictToAddSubgroup Z C x).trans ht.symm

private theorem limit_family_exists_gt {G : Type u}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (T₀ : Set (ArchimedeanClass G)) (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b) :
    ∀ c ∈ {c : FiniteArchimedeanClass G | c.1 ∈ T₀},
      ∃ d ∈ {c : FiniteArchimedeanClass G | c.1 ∈ T₀}, c < d := by
  intro c hc
  obtain ⟨d, hd, hcd⟩ := hT₀gt c.1 hc
  obtain ⟨e, _he, hde⟩ := hT₀gt d hd
  exact ⟨⟨d, ne_top_of_lt hde⟩, hd, hcd⟩

private theorem limit_family_card_lt {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Field R] {κ : Cardinal} [Fact (ℵ₀ < κ)] {Z : Subring R}
    (T₀ T₁ : Set (ArchimedeanClass G))
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hxclasses : ArchimedeanClass.mk '' (x : HahnSeries G R).support = T₀ ∪ T₁) :
    #{c : FiniteArchimedeanClass G | c.1 ∈ T₀} < κ := by
  calc
    #{c : FiniteArchimedeanClass G | c.1 ∈ T₀} =
        #(Subtype.val '' {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) :=
      (Cardinal.mk_image_eq Subtype.val_injective).symm
    _ ≤ #T₀ := Cardinal.mk_le_mk_of_subset fun _ h ↦ by
      obtain ⟨c, hc, rfl⟩ := h
      exact hc
    _ ≤ #(ArchimedeanClass.mk '' (x : HahnSeries G R).support) :=
      Cardinal.mk_le_mk_of_subset fun c hc ↦ by
        rw [hxclasses]
        exact Or.inl hc
    _ ≤ #(x : HahnSeries G R).support := Cardinal.mk_image_le
    _ < κ := x.1.2

/-- Let the Archimedean classes met by the support of `x ≠ 0` be `T₀ ∪ T₁`, with `T₁` finite and
`T₀` without least member in magnitude, and let the quotient `Γ` of `G` by the common tail below
`T₀` be Cauchy complete. If every series of smaller support-class order type is primal, then the
regrouping of `x` along the common tail is primal in `L((Γ^{≤0}))_κ`. -/
@[blueprint "lem:regrouped-primality-at-limit"
  (phase := "Reduction along Archimedean classes")
  (title := "Primality of the regrouping at a limit of Archimedean classes")
  (statement := /--
    Let $G$ be an ordered $\mathbb Q$-vector space, $R$ of characteristic $0$,
    and $\kappa$ regular.  Let $0\ne x\in Z+R((G^{<0}))_\kappa$ meet exactly the
    classes $T_0\cup T_1$, where $T_0$ contains a nonzero class and has no least
    element in magnitude, and assume (B2)$_{T_0}$.  Suppose every element whose
    set of nonzero classes has smaller order type than that of $x$ is primal.
    Then the regrouping $\hat x$ of $x$ along $H_{T_0}$ is primal in
    $L((\Gamma^{\le0}))_\kappa$.
  -/)
  (proof := /--
    Here $\Gamma=G/H_{T_0}$ and $L=R((H_{T_0}))_\kappa$.  We apply
    \ref{lem:primality-from-germs} to $f=\hat x$; it remains to find
    arbitrarily small nonzero classes $q$ of $\Gamma$ with
    $\hat x_{|q}\ne0$ and $\hat x=\hat x_{|q}\,w$, $w$ primal.

    Since $T_0$ has no least element in magnitude, the nonzero classes of
    $\Gamma$ met by the support of $\hat x$ are arbitrarily small.  Let $q$ be
    one of them.  By \ref{lem:support-class-factorisation} there is
    $w\in Z+R((G^{<0}))_\kappa$ with constant coefficient $1$ such that $x=tw$,
    where $t$ is the restriction of $x$ to the inverse image of
    $\Gamma_{\preceq q}$, and the nonzero classes of $w$ have smaller order type
    than those of $x$.  So $w$ is primal by hypothesis.  Regrouping is a ring
    isomorphism onto $D+L((\Gamma^{<0}))_\kappa$ which takes $t$ to
    $\hat x_{|q}\ne0$.  The regrouping $\hat w$ is primal there, with constant
    coefficient $1$.  So it is primal in $L((\Gamma^{\le0}))_\kappa$: every
    element of that ring is a nonzero constant times one with constant
    coefficient $0$ or $1$, and this reduces a divisibility relation in
    $L((\Gamma^{\le0}))_\kappa$ to one in $D+L((\Gamma^{<0}))_\kappa$.  Thus
    $\hat x=\hat x_{|q}\,\hat w$ as required.
  -/)]
theorem isPrimal_regroupAmbient_of_limit_tail
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R] [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R)
    (T₀ T₁ : Set (ArchimedeanClass G)) (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b)
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hxclasses : ArchimedeanClass.mk '' (x : HahnSeries G R).support = T₀ ∪ T₁)
    [Nonempty {c : FiniteArchimedeanClass G | c.1 ∈ T₀}]
    [CompleteSpace (FiniteArchimedeanClass.TailQuotient
      {c : FiniteArchimedeanClass G | c.1 ∈ T₀})]
    (hx0 : x ≠ 0)
    (ih : ∀ w : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z w)).orderType <
        (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z x)).orderType → IsPrimal w) :
    IsPrimal (regroupAmbient
      (FiniteArchimedeanClass.tailSubmodule ℚ {c : FiniteArchimedeanClass G | c.1 ∈ T₀}) Z x) := by
  let T : Set (FiniteArchimedeanClass G) := {c | c.1 ∈ T₀}
  let P := FiniteArchimedeanClass.tailSubmodule ℚ T
  have hT := limit_family_exists_gt T₀ hT₀gt
  haveI : Nonempty (FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T)) := by
    letI := FiniteArchimedeanClass.nontrivial_tailQuotient T hT
    obtain ⟨y, hy⟩ := exists_ne (0 : FiniteArchimedeanClass.TailQuotient T)
    exact ⟨FiniteArchimedeanClass.mk y hy⟩
  refine CardSuppLTNonpositive.isPrimal_of_frequently_restriction_mul_isPrimal T
    hT ?_
  rw [Filter.frequently_atTop]
  intro q₀
  have hU : IsCofinal {q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T) |
      q.1 ∈ ArchimedeanClass.mk ''
        (HahnSeries.convexQuotientSplitRingEquiv P (x : HahnSeries G R)).support} :=
    HahnSeries.isCofinal_supportArchimedeanClasses_convexQuotientSplit
      T₀ T₁ hT₀gt (x : HahnSeries G R) hxclasses
  have hq₀ : ∃ q ∈ {q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T) |
      q.1 ∈ ArchimedeanClass.mk ''
        (HahnSeries.convexQuotientSplitRingEquiv P (x : HahnSeries G R)).support}, q₀ ≤ q :=
    hU q₀
  obtain ⟨q, hqU, hq₀q⟩ := hq₀
  have hqocc : q.1 ∈ ArchimedeanClass.mk ''
      (Submodule.Quotient.mk (p := P) '' (x : HahnSeries G R).support) := by
    obtain ⟨z, hz, hzq⟩ := hqU
    have hsupp := HahnSeries.support_convexQuotientSplitRingEquiv P (x : HahnSeries G R)
    rw [hsupp] at hz
    obtain ⟨r, hr, hzr⟩ := hz
    exact ⟨z, ⟨r, hr, hzr⟩, hzq⟩
  have hfactor := restriction_mul_isPrimal_at_support_class Z T q x hqocc ih
  obtain ⟨t, w, ht, hfac, hw, hw0⟩ := hfactor
  exact ⟨q, hq₀q, restriction_mul_isPrimal_of_factorization P Z _ x t w hx0 ht hfac hw hw0⟩

/-- **Primality in bounded Hahn integer parts.** Let `K` be an Archimedean ordered field, `G` an
ordered `K`-vector space, `R` a field of characteristic zero, `κ > ℵ₀` a regular cardinal, and
`Z ⊆ R` a pre-Schreier subring. Suppose that every Archimedean stratum of `G` is order-isomorphic
to `ℝ`; that every strict ball `G_{≺σ}`, and every common tail of a limit family of fewer than `κ`
classes, has cofinality at least `κ` or is zero with `R` the fraction field of `Z`; and that the
quotient of `G` by every such common tail is Cauchy complete. Then every element of
`Z + R((G^{<0}))_κ` is primal.

At strict balls, the first two conditions are assumptions `(A1)` and `(A2)` of L'Innocente and
Mantova (LM24, Theorem 9.0.1); primality of `Z` is their `(A3)`. -/
@[blueprint "thm:hahn-integer-part-primality"
  (phase := "Reduction along Archimedean classes")
  (title := "Primality in $Z+R((G^{<0}))_\\kappa$")
  (statement := /--
    Let $K$ be an Archimedean ordered field and $G$ an ordered $K$-vector space
    that is also an ordered $\mathbb Q$-vector space, with $K$-linear complements
    $H_\sigma$; let $R$ have characteristic $0$ and $\kappa$ be regular.  Assume
    (A1)$_\sigma$ and (A2)$_\sigma$ for every nonzero class $\sigma$, (A3), and
    (B1)$_T$ and (B2)$_T$ for every nonempty set $T$ of fewer than $\kappa$
    nonzero classes without least element in magnitude.  Then every element of
    $Z+R((G^{<0}))_\kappa$ is primal.  Conditions (A1)--(A3) are shown to be
    necessary in [LM24, Thm. 9.0.1].
  -/)
  (proof := /--
    Induct on the order type of the well-ordered set of nonzero classes met by
    $x$.  If it is finite, $x$ is primal by
    \ref{thm:finite-support-classes-primality}, from (A1), (A2) and (A3).

    Otherwise the classes met by $x$ split as $T_0\cup T_1$, with $T_1$ a finite
    final segment and $T_0$ an initial segment whose order type is a limit
    ordinal.  So $T_0$ has no least element in magnitude and contains a nonzero
    class, and it has fewer than $\kappa$ elements because
    $\operatorname{supp}(x)$ does.  We may assume $x\ne0$.  Put $C=H_{T_0}$ and
    apply the primality through regrouping along $C$.  Its hypotheses hold:

    $\hat x$ is primal, by \ref{lem:regrouped-primality-at-limit}; that lemma
    needs (B2)$_{T_0}$ and the induction hypothesis.

    $x_{|C}$ is primal in $D$.  It meets only classes in $T_1$, so it is primal
    in $Z+R((G^{<0}))_\kappa$ by \ref{thm:finite-support-classes-primality}.  It
    is then primal in the subring $D$ of elements supported in $C$, as in the
    proof of primality at the leading class.

    $L=\operatorname{Frac}(D)$, by (B1)$_{T_0}$ and the fraction field lemma
    [LM24, Prop. 2.4.5].
  -/)
  (highlight)]
theorem isPrimal
    {K : Type*} {G : Type u} {R : Type v}
    [Field K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module K G] [IsOrderedModule K G] [Module ℚ G] [PosSMulMono ℚ G]
    [Field R] [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R) [DecompositionMonoid Z]
    (s : HahnEmbedding.ArchimedeanStrata K G)
    (hstratum : ∀ c : FiniteArchimedeanClass G, Nonempty (s.stratum c ≃+o ℝ))
    (hball : ∀ c : FiniteArchimedeanClass G, κ ≤ Order.cof (FiniteArchimedeanClass.ball K c) ∨
      (Subsingleton (FiniteArchimedeanClass.ball K c) ∧ Subring.fracSubring Z = ⊤))
    (htail : ∀ T : Set (FiniteArchimedeanClass G), T.Nonempty → (∀ c ∈ T, ∃ d ∈ T, c < d) →
      #T < κ → κ ≤ Order.cof (FiniteArchimedeanClass.tailSubmodule ℚ T) ∨
        (Subsingleton (FiniteArchimedeanClass.tailSubmodule ℚ T) ∧ Subring.fracSubring Z = ⊤))
    (hcomplete : ∀ T : Set (FiniteArchimedeanClass G), T.Nonempty →
      (∀ c ∈ T, ∃ d ∈ T, c < d) → #T < κ →
        CompleteSpace (FiniteArchimedeanClass.TailQuotient T))
    (a : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z) : IsPrimal a := by
  let S := HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z
  let rank : S → Ordinal := fun x ↦
    (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
      (toNonpositiveRingHom Z x)).orderType
  have hfinite := isPrimal_of_supportArchimedeanClasses_finite Z s hstratum hball
  suffices hind : ∀ o : Ordinal, ∀ x : S, rank x = o → IsPrimal x from hind (rank a) a rfl
  intro o
  induction o using WellFoundedLT.induction with
  | ind o ih =>
      intro x hxrank
      rcases (toNonpositiveRingHom Z x).isPWO_supportArchimedeanClasses
          |>.finite_or_exists_limit_initial_finite_final
          with hfiniteClasses | ⟨T₀, T₁, hT₀pwo, _hT₁pwo, _hT₀sub, _hT₁sub, _hbefore,
            hT₀limit, hT₁finite, hclasses⟩
      · apply hfinite x
        simpa only [coe_toNonpositiveRingHom] using hfiniteClasses
      have hT₀gt : ∀ c ∈ T₀, ∃ d ∈ T₀, c < d := fun c hc ↦
        hT₀pwo.exists_gt_of_isSuccLimit_orderType hT₀limit hc
      have hxclasses : ArchimedeanClass.mk '' (x : HahnSeries G R).support = T₀ ∪ T₁ := by
        simpa only [coe_toNonpositiveRingHom] using hclasses
      let T : Set (FiniteArchimedeanClass G) := {c | c.1 ∈ T₀}
      have hTne : T.Nonempty := by
        have hT₀ne : T₀.Nonempty := by
          by_contra hne
          rw [Set.not_nonempty_iff_eq_empty] at hne
          exact hT₀limit.ne_bot (hT₀pwo.orderType_eq_zero.mpr hne)
        obtain ⟨c, hc⟩ := hT₀ne
        obtain ⟨d, _hd, hcd⟩ := hT₀gt c hc
        exact ⟨⟨c, ne_top_of_lt hcd⟩, hc⟩
      letI : Nonempty T := hTne.to_subtype
      have hTgt := limit_family_exists_gt T₀ hT₀gt
      have hTcard := limit_family_card_lt T₀ T₁ x hxclasses
      letI : CompleteSpace (FiniteArchimedeanClass.TailQuotient T) :=
        hcomplete T hTne hTgt hTcard
      by_cases hx0 : x = 0
      · rw [hx0]
        exact isPrimal_zero
      exact isPrimal_of_isPrimal_regroupAmbient _ Z x
        (isPrimal_regroupAmbient_of_limit_tail Z T₀ T₁ hT₀gt x hxclasses hx0
          (fun w hw ↦ ih (rank w) (hxrank ▸ hw) w rfl))
        (isPrimal_restrictDomain_tailSubmodule_of_ambient_finiteClasses
          Z hfinite T₀ T₁ hT₀gt hT₁finite x hxclasses.le)
        (fun _ ↦ fracSubring_eq_top_of_le_cof_or_subsingleton Z (htail T hTne hTgt hTcard))

end HahnSeries.CardSuppLTTruncationIntegerPart
