/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import ConwayRefinement.HahnSeries.Germ.PolynomialRing
public import ConwayRefinement.HahnSeries.BoundedSupport.Residue

import ConwayRefinement.Blueprint
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import ConwayRefinement.RingTheory.TruncationGerms.Transcendence

/-!
# Germs of series with fewer than `κ` support exponents

Let `κ > ℵ₀` and let `K((G^{≤0}))_κ` be the ring of nonpositive series with fewer than `κ` support
exponents. Translated truncation and cutoff below a negative exponent do not enlarge supports, so
they preserve this ring, and the ideal `J_κ` of series whose support is bounded away from zero is
the trace of `J`. The germs of translated truncations therefore pull back to germ maps on
`K((G^{≤0}))_κ` with values in `K((G^{≤0}))_κ / J_κ`, which embeds in `K((G^{≤0}))/J`, and these
germ maps satisfy the axioms of `TruncationGerms`. When `G` is
Cauchy complete, `K((G^{≤0}))_κ / J_κ` is a polynomial ring over `K`, so every germ is primal.
-/

open Cardinal Set
open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.CardSuppLTNonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field K]
variable {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]

/-- Package a nonpositive Hahn series with an explicit support-cardinality bound. -/
def ofNonpositive (x : Nonpositive G K) (hx : (x : K⟦G⟧).cardSupp < κ) :
    CardSuppLTNonpositive (G := G) (L := K) (κ := κ) :=
  ⟨⟨x, (mem_cardSuppLTSubfield (Γ := G) (R := K) (κ := κ)).mpr hx⟩, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    exact ⟨x.2, Subring.mem_top _⟩⟩

/-- Forgetting the cardinal-bound package recovers the original nonpositive series. -/
@[simp]
theorem coe_ofNonpositive (x : Nonpositive G K) (hx : (x : K⟦G⟧).cardSupp < κ) :
    ((ofNonpositive x hx : CardSuppLTNonpositive (G := G) (L := K) (κ := κ)) :
      K⟦G⟧) = (x : K⟦G⟧) :=
  (rfl)

/-- Forgetting the support bound from a packaged nonpositive series recovers that series. -/
@[simp]
theorem toNonpositiveRingHom_ofNonpositive
    (x : Nonpositive G K) (hx : (x : K⟦G⟧).cardSupp < κ) :
    CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring K)
      (ofNonpositive x hx) = x := by
  apply Subtype.ext
  rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
  exact coe_ofNonpositive x hx

variable (G K κ) in
/-- Forgetting the support bound, as a `K`-algebra homomorphism. -/
def toNonpositiveAlgHom :
    CardSuppLTNonpositive (G := G) (L := K) (κ := κ) →ₐ[K] Nonpositive G K where
  __ := CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring K)
  commutes' r := by
    apply Subtype.ext
    rw [RingHom.toFun_eq_coe, CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom,
      coe_algebraMap, Nonpositive.algebraMap_apply, Nonpositive.coe_C]

@[simp]
theorem toNonpositiveAlgHom_apply (x : CardSuppLTNonpositive (G := G) (L := K) (κ := κ)) :
    toNonpositiveAlgHom G K κ x =
      CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring K) x :=
  (rfl)

theorem toNonpositiveAlgHom_injective :
    Function.Injective (toNonpositiveAlgHom G K κ) :=
  CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_injective _

/-- The translated truncation of a `κ`-bounded series is `κ`-bounded. -/
def translatedTruncation (γ : G) (b : CardSuppLTNonpositive (G := G) (L := K) (κ := κ)) :
    CardSuppLTNonpositive (G := G) (L := K) (κ := κ) :=
  ofNonpositive (Nonpositive.translatedTruncation γ (toNonpositiveAlgHom G K κ b)) <| by
    classical
    rw [Nonpositive.coe_translatedTruncation, ← single_one_mul_eq_translate]
    refine ((cardSupp_single_mul_le _ _ _).trans
      (cardSupp_mono (support_truncLE_subset _ _))).trans_lt ?_
    exact CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt _ b

theorem toNonpositiveAlgHom_translatedTruncation (γ : G)
    (b : CardSuppLTNonpositive (G := G) (L := K) (κ := κ)) :
    toNonpositiveAlgHom G K κ (translatedTruncation γ b) =
      Nonpositive.translatedTruncation γ (toNonpositiveAlgHom G K κ b) :=
  toNonpositiveRingHom_ofNonpositive _ _

variable [Nontrivial G]

variable (G K κ) in
/-- The ideal `J_κ` of `κ`-bounded nonpositive series whose support is bounded away from zero. -/
def boundedAwayIdeal : Ideal (CardSuppLTNonpositive (G := G) (L := K) (κ := κ)) :=
  (Nonpositive.boundedAwayIdeal G K).comap
    (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom (⊤ : Subring K))

theorem mem_boundedAwayIdeal (x : CardSuppLTNonpositive (G := G) (L := K) (κ := κ)) :
    x ∈ boundedAwayIdeal G K κ ↔ ∃ c < (0 : G), (x : K⟦G⟧).support ⊆ Iic c := by
  rw [boundedAwayIdeal, Ideal.mem_comap, Nonpositive.mem_boundedAwayIdeal,
    CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]

/-- The germ map at the exponent `γ` on `K((G^{≤0}))_κ`. -/
def germAt (γ : G) :
    CardSuppLTNonpositive (G := G) (L := K) (κ := κ) →ₗ[K]
      CardSuppLTNonpositive (G := G) (L := K) (κ := κ) ⧸ boundedAwayIdeal G K κ where
  toFun b := Ideal.Quotient.mk _ (translatedTruncation γ b)
  map_add' b b' := by
    rw [← map_add]
    congr 1
    apply toNonpositiveAlgHom_injective
    simp only [toNonpositiveAlgHom_translatedTruncation, map_add,
      Nonpositive.translatedTruncation_add]
  map_smul' k b := by
    rw [RingHom.id_apply, ← Ideal.Quotient.mkₐ_eq_mk K, ← map_smul]
    congr 1
    apply toNonpositiveAlgHom_injective
    simp only [toNonpositiveAlgHom_translatedTruncation, map_smul,
      Nonpositive.translatedTruncation_smul]

variable (G K κ) in
/-- The ring of `κ`-bounded germs embeds in the ring of all germs. -/
def germEmbedding :
    (CardSuppLTNonpositive (G := G) (L := K) (κ := κ) ⧸ boundedAwayIdeal G K κ) →ₐ[K]
      Nonpositive G K ⧸ Nonpositive.boundedAwayIdeal G K :=
  Ideal.quotientMapₐ _ (toNonpositiveAlgHom G K κ) le_rfl

theorem germEmbedding_injective : Function.Injective (germEmbedding G K κ) :=
  Ideal.quotientMap_injective

theorem germEmbedding_mk (b : CardSuppLTNonpositive (G := G) (L := K) (κ := κ)) :
    germEmbedding G K κ (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (toNonpositiveAlgHom G K κ b) :=
  (rfl)

instance : Nontrivial (CardSuppLTNonpositive (G := G) (L := K) (κ := κ) ⧸
    boundedAwayIdeal G K κ) :=
  Ideal.Quotient.nontrivial_iff.mpr ((Ideal.ne_top_iff_one _).mpr fun h ↦
    Nonpositive.one_notMem_boundedAwayIdeal (G := G) (R := K) (by
      simpa [boundedAwayIdeal] using h))

variable [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [CompleteSpace G]
  [CharZero K]

variable (G K κ) in
/-- The germs of translated truncations on `K((G^{≤0}))_κ` satisfy the axioms of
`TruncationGerms`. -/
def truncationGerms : TruncationGerms K G (CardSuppLTNonpositive (G := G) (L := K) (κ := κ))
    (CardSuppLTNonpositive (G := G) (L := K) (κ := κ) ⧸ boundedAwayIdeal G K κ) :=
  (Nonpositive.truncationGerms G K).comap (toNonpositiveAlgHom G K κ) (germEmbedding G K κ)
    germEmbedding_injective (Ideal.Quotient.mkₐ K _) (Ideal.Quotient.mkₐ_surjective K _)
    (fun _ ↦ by rw [Ideal.Quotient.mkₐ_eq_mk, germEmbedding_mk, Nonpositive.truncationGerms_germ])
    germAt (fun _ _ ↦ by
      change germEmbedding G K κ (Ideal.Quotient.mk _ _) = _
      rw [germEmbedding_mk, toNonpositiveAlgHom_translatedTruncation,
        Nonpositive.truncationGerms_germAt, Nonpositive.germAt_apply])
    (fun b ξ _ ↦ ⟨translatedTruncation ξ b, fun ζ hζ ↦ by
      simp only [toNonpositiveAlgHom_translatedTruncation, Nonpositive.truncationGerms_germAt]
      exact Nonpositive.germAt_translatedTruncation (toNonpositiveAlgHom G K κ b) ξ hζ⟩)
    (fun b ε hε ↦ by
      obtain ⟨b', h₀, h₁, h₂, hsupp⟩ :=
        Nonpositive.exists_germAt_cutoff (toNonpositiveAlgHom G K κ b) hε
      refine ⟨ofNonpositive b' ((cardSupp_mono hsupp).trans_lt
        (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt _ b)), ?_⟩
      simp only [toNonpositiveAlgHom_apply, toNonpositiveRingHom_ofNonpositive,
        Nonpositive.truncationGerms_germ, Nonpositive.truncationGerms_germAt]
      exact ⟨h₀, h₁, h₂⟩)

/-- For a nontrivial Cauchy-complete exponent group `G`, the ring of germs of `κ`-bounded
nonpositive series is a polynomial algebra over `K`. -/
@[blueprint "thm:bounded-hahn-germ-polynomial-algebra"
  (phase := "Polynomial presentations")
  (title := "Polynomial presentation of the ring of germs of series with small support")
  (statement := /--
    Let $K$ be a field of characteristic zero, $\kappa>\aleph_0$ a cardinal,
    and $G$ a nontrivial ordered abelian group which, with its order topology
    and the associated group uniformity, is Cauchy complete.  Let
    $K((G^{\le0}))_\kappa$ be the ring of series in $K((G^{\le0}))$ whose
    support has cardinality less than $\kappa$, and
    $J_\kappa=J\cap K((G^{\le0}))_\kappa$.  Then for some set $I$ there is a
    $K$-algebra isomorphism
    \[
      K[X_i:i\in I]\simeq K((G^{\le 0}))_\kappa/J_\kappa.
    \]
  -/)
  (proof := /--
    Translated truncations, and cutoffs below a negative exponent, do not
    enlarge supports, so they preserve $K((G^{\le0}))_\kappa$; and
    $K((G^{\le0}))_\kappa/J_\kappa$ embeds in $K((G^{\le0}))/J$ compatibly with
    the germ maps.  Each of the properties (1)--(7) is an identity or a
    vanishing statement in the ring of germs whose witnesses are translated
    truncations or cutoffs.  So the germ maps $b\mapsto[b^{|\gamma}]$ on
    $K((G^{\le0}))_\kappa$ with values in $K((G^{\le0}))_\kappa/J_\kappa$
    satisfy (1)--(7), by restriction from \ref{prop:hahn-germs-axioms}.  Apply
    \ref{thm:germ-ring-generators}.
  -/)]
theorem exists_mvPolynomial_algEquiv_germ :
    ∃ ι : Type (max (u + 1) v), Nonempty (MvPolynomial ι K ≃ₐ[K]
      CardSuppLTNonpositive (G := G) (L := K) (κ := κ) ⧸ boundedAwayIdeal G K κ) :=
  (truncationGerms G K κ).exists_mvPolynomial_algEquiv.{_, u + 1}

/-- Every germ of a `κ`-bounded nonpositive series over a Cauchy-complete exponent group is
primal. -/
theorem isPrimal_germ
    (q : CardSuppLTNonpositive (G := G) (L := K) (κ := κ) ⧸ boundedAwayIdeal G K κ) :
    IsPrimal q := by
  obtain ⟨ι, ⟨e⟩⟩ := exists_mvPolynomial_algEquiv_germ (G := G) (K := K) (κ := κ)
  letI := MulEquiv.decompositionMonoid e.symm.toMulEquiv
  exact DecompositionMonoid.primal q

end HahnSeries.CardSuppLTNonpositive
