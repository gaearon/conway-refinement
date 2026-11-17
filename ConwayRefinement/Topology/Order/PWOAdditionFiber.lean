/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
import ConwayRefinement.Topology.CantorBendixson.Rank
import ConwayRefinement.Topology.Order.PWOAddition
import ConwayRefinement.Blueprint

/-!
# Local domination by a finite addition fiber

Near a fixed sum, each pair from two closed well-ordered supports is coordinatewise bounded
by exactly one pair in the fiber at that sum. Closedness of addition propagates the local
right gaps of the supports to a whole nearby fiber; finite fibers supply uniqueness.
The ambient ordered uniform group is Cauchy complete. No countability or density is assumed.
-/

public noncomputable section

open Set Filter Topology

universe u

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]

/-- Every nearby addition pair lies below a pair in the fixed fiber. -/
theorem Set.IsPWO.eventually_exists_add_dominator {B C : Set G}
    (hB : B.IsPWO) (hC : C.IsPWO) (hBc : IsClosed B) (hCc : IsClosed C) (γ : G) :
    ∀ᶠ δ in 𝓝 γ, ∀ q : B ×ˢ C, q.1.1 + q.1.2 = δ →
      ∃ p : B ×ˢ C, p.1.1 + p.1.2 = γ ∧ q.1 ≤ p.1 := by
  apply (hB.isClosedMap_add hC hBc hCc).eventually_nhds_fiber γ
  intro p hp
  have hfst : Continuous (fun q : B ×ˢ C ↦ q.1.1) := by fun_prop
  have hsnd : Continuous (fun q : B ×ˢ C ↦ q.1.2) := by fun_prop
  filter_upwards [hfst.continuousAt.tendsto.eventually (hB.eventually_le p.1.1),
    hsnd.continuousAt.tendsto.eventually (hC.eventually_le p.1.2)] with q hq1 hq2
  exact ⟨p, hp, hq1 q.2.1, hq2 q.2.2⟩

/-- Every nearby addition pair lies below exactly one pair in the fixed fiber. -/
@[blueprint "lem:addition-fibre"
  (phase := "Germs of translated truncations")
  (title := "Addition near a fibre on closed well-ordered sets")
  (statement := /--
    Let $G$ be Cauchy complete, let $B,C\subseteq G$ be closed and well ordered, and let
    $\gamma\in G$. Then there is a neighbourhood $U$ of $\gamma$ such that every
    $(\beta,\eta)\in B\times C$ with $\beta+\eta\in U$ satisfies $\beta\le\xi$ and $\eta\le\zeta$
    for exactly one $(\xi,\zeta)\in B\times C$ with $\xi+\zeta=\gamma$.
  -/)
  (proof := /--
    Let $F$ be the set of $(\xi,\zeta)\in B\times C$ with $\xi+\zeta=\gamma$. Two distinct pairs of
    $F$ are incomparable coordinatewise, and $B\times C$ is partially well ordered, so $F$ is
    finite.

    Addition $B\times C\to G$ is a closed map. Let $\mathcal U$ be an ultrafilter on $B\times C$
    whose image under addition converges. For each $\varepsilon>0$, take $V\in\mathcal U$ such
    that the sums of any two pairs in $V$ differ by less than $\varepsilon$ in absolute value.
    Every pair in $V$ lies above one of its finitely many minimal pairs. Thus for some $a\in V$
    the pairs $p\in V$ above $a$ form a member of $\mathcal U$. For each such $p$, both coordinate
    differences $p_i-a_i$ lie between $0$ and $(p_1+p_2)-(a_1+a_2)<\varepsilon$. Any two of
    these pairs therefore differ by less than $\varepsilon$ in each coordinate. So $\mathcal U$
    is Cauchy and converges in the closed subset $B\times C$ of the complete space $G\times G$.
    Thus addition is proper, hence closed.

    Existence. For $(\xi,\zeta)\in F$, the points of $B$ above $\xi$, if any, have a least element,
    so the points of $B$ near $\xi$ are at most $\xi$; likewise for $C$ near $\zeta$. So the set of
    pairs lying below some pair of $F$ contains an open neighbourhood $W$ of $F$ in $B\times C$. The
    image of $(B\times C)\setminus W$ under addition is closed and does not contain $\gamma$. Take
    $U$ disjoint from it.

    Uniqueness. If $(\beta,\eta)$ lies below two distinct pairs $(\xi,\zeta)$ and $(\xi',\zeta')$ of
    $F$, say with $\xi<\xi'$, then $\zeta>\zeta'$ and $\beta+\eta\le\xi+\zeta'<\gamma$. There are
    finitely many such sums $\xi+\zeta'$; shrinking $U$ to lie above all of them gives uniqueness.
  -/)]
theorem Set.IsPWO.eventually_existsUnique_add_dominator {B C : Set G}
    (hB : B.IsPWO) (hC : C.IsPWO) (hBc : IsClosed B) (hCc : IsClosed C) (γ : G) :
    ∀ᶠ δ in 𝓝 γ, ∀ q : B ×ˢ C, q.1.1 + q.1.2 = δ →
      ∃! p : B ×ˢ C, p.1.1 + p.1.2 = γ ∧ q.1 ≤ p.1 := by
  let f : B ×ˢ C → G := fun p ↦ p.1.1 + p.1.2
  let F := f ⁻¹' {γ}
  have hF : F.Finite := hB.finite_subtype_add_fiber hC γ
  have hu : ∀ᶠ δ in 𝓝 γ, ∀ p ∈ F, ∀ r ∈ F, ∀ q : B ×ˢ C,
      f q = δ → q.1 ≤ p.1 → q.1 ≤ r.1 → p = r := by
    apply hF.eventually_all.mpr
    intro p hp
    apply hF.eventually_all.mpr
    intro r hr
    by_cases he : p = r
    · exact Filter.Eventually.of_forall fun _ _ _ _ _ ↦ he
    have hne : p.1.1 ≠ r.1.1 := by
      intro he1
      apply he
      apply Subtype.ext
      apply Prod.ext he1
      have hh : p.1.1 + p.1.2 = r.1.1 + r.1.2 := hp.trans hr.symm
      rw [he1] at hh
      exact add_left_cancel hh
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hgap : p.1.1 + r.1.2 < γ :=
        (add_lt_add_left hlt r.1.2).trans_eq hr
      filter_upwards [eventually_gt_nhds hgap] with δ hδ q hq hqp hqr
      exact False.elim ((not_le_of_gt hδ) (hq ▸ add_le_add hqp.1 hqr.2))
    · have hgap : r.1.1 + p.1.2 < γ :=
        (add_lt_add_left hlt p.1.2).trans_eq hp
      filter_upwards [eventually_gt_nhds hgap] with δ hδ q hq hqp hqr
      exact False.elim ((not_le_of_gt hδ) (hq ▸ add_le_add hqr.1 hqp.2))
  filter_upwards [hB.eventually_exists_add_dominator hC hBc hCc γ, hu]
    with δ hex huniq q hq
  obtain ⟨p, hp, hqp⟩ := hex q hq
  exact ⟨p, ⟨hp, hqp⟩, fun r hr ↦ huniq r hr.1 p hp q hq hr.2 hqp⟩
