/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.CardinalTruncation
public import ConwayRefinement.Surreal.HahnSeries.CardinalIntegerPart
public import Mathlib.Data.List.Chain
public import Mathlib.RingTheory.HahnSeries.Addition
public import ConwayRefinement.HahnSeries.Truncation
public import CombinatorialGames.NatOrdinal.Pow
public import Mathlib.SetTheory.Ordinal.Exponential
public import ConwayRefinement.SetTheory.Ordinal.SetOrderType
public import ConwayRefinement.Order.Archimedean
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import ConwayRefinement.Surreal.HahnSeries.Full
public import CombinatorialGames.Surreal.HahnSeries.Basic

/-!
# Ordinary omnific integers

An omnific integer is ordinary when it is an integer. A non-ordinary omnific integer has nonzero
lowest exponent in the signed Hahn orientation, and conversely; these are the hypotheses under
which the LM24 leading-class transfer applies.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open scoped HahnSeries NatOrdinal

namespace Surreal.OmnificInteger

universe u

/-- An omnific integer is ordinary when its underlying surreal is an integer. -/
def IsOrdinaryInteger (x : Surreal.OmnificInteger.{u}) : Prop :=
  ∃ z : ℤ, x.1 = (z : Surreal)

/-- Characterization of ordinary omnific integers by an integer witness. -/
theorem isOrdinaryInteger_iff (x : Surreal.OmnificInteger.{u}) :
    IsOrdinaryInteger x ↔ ∃ z : ℤ, x.1 = (z : Surreal) :=
  (Iff.rfl)

end Surreal.OmnificInteger
