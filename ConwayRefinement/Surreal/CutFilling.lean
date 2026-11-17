/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Basic
public import ConwayRefinement.Topology.Order.CoinitialComplete

import ConwayRefinement.Blueprint

/-!
# The surreals fill cuts between small families

Between any two small families of surreals separated by the order there is a surreal, namely the
one born from those families as its option sets. This is the simplicity theorem in the form the
completeness criterion of `ConwayRefinement.Topology.Order.CoinitialComplete`
consumes, and it is restricted to *small* families for the reason that makes the restriction
essential rather than
technical: a surreal has a set of options, so no construction reaches across a family the size of
the ordinals.

That restriction is exactly why the surreals themselves are not Cauchy complete — the positive
surreals have no small coinitial family, so a Cauchy filter can outrun every small cut — and why
the route to a complete group runs through a quotient. `FillsCuts.of_surjective` carries the
conclusion below to such a quotient; supplying the small coinitial family there is separate work.
-/

universe u

public section

namespace Surreal

/-- **The simplicity theorem for small cuts.** Two small sets of surreals with every member of the
first below every member of the second are strictly separated by a surreal. -/
@[blueprint "thm:surreal-simplicity-small-cuts"
  (phase := "Surreal numbers and omnific integers")
  (title := "Filling small cuts in the surreal numbers")
  (statement := /--
    Let $L,R\subseteq\mathbf{No}$ be sets of the universe $u$ with $l<r$ for all
    $l\in L$ and $r\in R$.  Then there is $x\in\mathbf{No}$ with $l<x<r$ for all
    $l\in L$ and $r\in R$.
  -/)
  (proof := /--
    Form the surreal number $\{L\mid R\}$ [Con76].  The separation hypothesis
    makes it a valid cut, and every left option is less than it and every
    right option greater.
  -/)]
theorem exists_between_small_sets (L R : Set Surreal.{u})
    [Small.{u} L] [Small.{u} R] (hLR : ∀ l ∈ L, ∀ r ∈ R, l < r) :
    ∃ x : Surreal.{u}, (∀ l ∈ L, l < x) ∧ ∀ r ∈ R, x < r :=
  ⟨!{L | R}, fun _ hl ↦ lt_ofSets_of_mem_left (H := hLR) hl,
    fun _ hr ↦ ofSets_lt_of_mem_right (H := hLR) hr⟩

/-- Small families separated by the surreal order satisfy the weak cut-filling property. -/
theorem fillsCuts {ι : Type u} [Small.{u} ι] : FillsCuts ι Surreal.{u} := by
  rw [fillsCuts_iff]
  intro L R hLR
  have hsep : ∀ x ∈ Set.range L, ∀ y ∈ Set.range R, x < y := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hLR i j
  obtain ⟨x, hxL, hxR⟩ := exists_between_small_sets (Set.range L) (Set.range R) hsep
  exact ⟨x, fun i ↦ (hxL _ ⟨i, rfl⟩).le, fun j ↦ (hxR _ ⟨j, rfl⟩).le⟩

end Surreal
