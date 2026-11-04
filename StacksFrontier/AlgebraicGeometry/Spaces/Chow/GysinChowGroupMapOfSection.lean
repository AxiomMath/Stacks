module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinMemberRuleComparison

/-!
# Stacks 0ERA: the Gysin homomorphism factors through rational equivalence

In Situation 0EDT let `X/B` be good and let `(ℒ, s, i : D → X)` be as in Definition 0ER1: `ℒ` an
invertible `𝒪_X`-module, `s ∈ Γ(X, ℒ)` and `i : D = Z(s) → X` the closed immersion of the
vanishing locus.  **Stacks 0ERA**: the Gysin homomorphism `i^* : Z_{k+1}(X) → CH_k(D)` of
Definition 0ER1 factors through rational equivalence, giving

`i^* : CH_{k+1}(X) ⟶ CH_k(D)`.

The letter `D` is the dimension situation of Stacks 0EDT, so the vanishing locus is called `E`
below.

## The objects

* The Gysin homomorphism on cycles is `AlgebraicGeometry.Space.gysinCycleMap` at the component
  rule `AlgebraicGeometry.Space.sectionGysinRule` of Stacks 0ER1(1), which is the rule of the
  refined Gysin homomorphism `AlgebraicGeometry.Space.sectionRefinedGysin` registered as
  Stacks 0ER1:
  clause (1)(a) the cycle `[E ∩ W]_k` of Stacks 0EE9, clause (1)(b) `c₁(ℒ|_W) ∩ [W]` read as the
  Weil divisor of the regular meromorphic section of `ℒ|_W` of Stacks 0EPQ.
* `CH_{k+1}(X)` and `CH_k(E)` are `AlgebraicGeometry.Space.chowGroupCanonical`, the quotients of
  Stacks 0EQ6 by the cycles `∑ (i_j)_* div(f_j)` with `div(f_j)` read at the canonical embeddings
  `R(W_j) → Q(𝒪^h_{W_j,ξ})` of Stacks 0ENK — the source's Chow groups, `div(f_j)` being a
  function of `f_j` alone.  The refined Gysin homomorphism `sectionRefinedGysin`, valued in the
  coarser quotient `AlgebraicGeometry.Space.chowGroup`, is the image of this one under
  `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup`
  (`AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup_sectionGysinChowGroupMap`).

## The proof

The source writes a cycle rationally equivalent to zero as `∑ i_{j,*} div_{W_j}(f_j)`, moves
`i^*` across the pushforward from `∐ W_j` by Lemma 0ER5, discards the pushforward by Lemma 0EQC,
and treats an integral `W = W_j`: if `W ⊆ D` then `i^*div(f) = c₁(ℒ) ∩ div(f)`, which vanishes by
Lemma 0EQY; if `W ⊄ D` then `i^*div(f) = c₁(𝒪_D) ∩ [D] = 0` by Lemma 0ER9.

Here the reassembly over the presenting family and the transport of the member's rational
equivalence to `E` are
`gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_firstChernCapWithinOnMember`,
which runs them on presentations of rational equivalences *with their carriers*, so that neither
Lemma 0ER5 nor Lemma 0EQC is needed.  It leaves one statement about each member `V` of
δ-dimension `k + 2` and each principal divisor `d` on `V`: the cap product of Stacks 0EQJ of `d`,
at the Gysin rule transported to `V`, is rationally equivalent to zero within `V ∩ E`.  That is
proved below in the source's two cases.

* `V ⊆ E`: the transported rule differs from the canonical rule of `ℒ|_V` by principal divisors
  (`isPrincipalDivisorCycleOfGood_closedSubspaceChernRule_sub_canonicalFirstChernRule`),
  and the canonical cap product kills `d` (the summand case of Stacks 0EQY,
  `isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_of_isPrincipalDivisorCycleOfGood`).
* `V ⊄ E`: off `E` the transported rule *is* the generator rule of the source's choice
  `s_i = σ|_V` (`closedSubspaceChernRule_restrictedSectionChernRule_eq_memberGeneratorChernRule`),
  on `E` they differ by principal divisors carried by `E`, and the generator cap product of `d` is
  rationally equivalent to zero within `Z(σ|_V) = V ∩ E` by the key formula of Stacks 0EQV
  (`isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_generatorChernRule`)
  — the content of Lemma 0ER9 at `𝒩 = 𝒪_V`, `t = f`.

## Main results

* `gysinCycleMapFactorsThroughRationalEquivalenceCanonical_sectionGysinRule`:
  the Gysin cycle map carries cycles rationally equivalent to zero to cycles rationally equivalent
  to zero.
* `AlgebraicGeometry.Space.sectionGysinChowGroupMap`: the descended map
  `i^* : CH_{k+1}(X) ⟶ CH_k(E)`.
* `AlgebraicGeometry.Space.exists_sectionGysinChowGroupMap`: **Stacks 0ERA.**

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
* [Stacks Project, Tag 0ERA](https://stacks.math.columbia.edu/tag/0ERA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (σ : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)

include hL in
/-- The inverse image in `V` of the vanishing locus of `σ` is the point set of the vanishing
locus of `σ|_V`. -/
theorem subspacePointSet_vanishingLocus_member
    (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    subspacePointSet D.site D.base D.base_mem V.subspace.toFunctor
        (vanishingLocus D (V.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp V)
          (integralClosedSubspaceRestrict D p hp L V)
          (integralClosedSubspaceRestrictSection D p hp L σ V)).1 =
      pointsMap D.site D.base D.base_mem V.subspace.toFunctor V.subspace.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L σ).1 := by
  rw [vanishingLocus_integralClosedSubspaceRestrictSection D p hp L σ hL V]
  exact subspacePointSet_preimage D.site D.base D.base_mem V.subspace.ι _

include hL in
/-- **The member statement of Stacks 0ERA.**  For an integral closed subspace `V ⊆ X` of
δ-dimension `k + 2` and a principal divisor `d` on `V` at the canonical embeddings of Stacks 0ENK,
the cap product of Stacks 0EQJ of `d` at the Gysin rule of Stacks 0ER1 transported to `V` is
rationally equivalent to zero at the canonical embeddings within the part of `V` lying on
`E = Z(σ)`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_member
    (V : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hVdim : deltaDimension D p V = k + 1 + 1)
    (d : CycleGroup D (V.subspace.ι ≫ p) (k + 1))
    (hd : IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ p)
      (isGood_integralClosedSubspace D p hp V) V.isIntegralSpace (k + 1) d) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D (V.subspace.ι ≫ p)
      (isGood_integralClosedSubspace D p hp V) k
      (firstChernCapCycleMap D (V.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp V) k
        (closedSubspaceChernRule D p hp V.subspace V.isClosedSubspace k
          (restrictedSectionChernRule D p hp L σ hL k (restrictedDivisorCycle D p hp L k hL))) d)
      (pointsMap D.site D.base D.base_mem V.subspace.toFunctor V.subspace.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L σ).1) := by
  have hVg := isGood_integralClosedSubspace D p hp V
  set c := firstChernCapCycleMap D (V.subspace.ι ≫ p) hVg k
    (closedSubspaceChernRule D p hp V.subspace V.isClosedSubspace k
      (restrictedSectionChernRule D p hp L σ hL k (restrictedDivisorCycle D p hp L k hL))) d
  by_cases hVE : V.subspace ≤ (vanishingLocus D p hp L σ).1
  · have hpre : pointsMap D.site D.base D.base_mem V.subspace.toFunctor V.subspace.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L σ).1 = Set.univ :=
      Set.eq_univ_of_forall fun x => subspacePointSet_mono_of_le D hVE ⟨x, rfl⟩
    rw [hpre, ← sub_add_cancel c
      (firstChernCapCycleMap D (V.subspace.ι ≫ p) hVg k
        (canonicalFirstChernRule D (V.subspace.ι ≫ p) hVg
          (integralClosedSubspaceRestrict D p hp L V)
          (isInvertibleModule_memberRestrict D p hp L hL V) k) d)]
    refine IsRationallyEquivalentToZeroWithinCanonical.add ?_ ?_
    · refine isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_sub D _ hVg k _ _ d
        Set.univ fun T₀ hT₀ _ _ => ⟨?_, Set.subset_univ _⟩
      refine isPrincipalDivisorCycleOfGood_closedSubspaceChernRule_sub_canonicalFirstChernRule D p
        hp L σ hL k V T₀ hT₀ ?_
      refine le_of_subspacePointSet_subset_of_integral D hp.1 _ (vanishingLocus D p hp L σ).2 _ ?_
      exact (subspacePointSet_integralClosedSubspaceImage_subset D p hp V T₀).trans
        (subspacePointSet_mono_of_le D hVE)
    · exact (isRationallyEquivalentToZeroWithinCanonical_univ_iff D _ hVg k _).2 <|
        isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_of_isPrincipalDivisorCycleOfGood
          D (V.subspace.ι ≫ p) hVg V.isIntegralSpace (integralClosedSubspaceRestrict D p hp L V)
          (isInvertibleModule_memberRestrict D p hp L hL V) k
          (deltaDimensionClosed_member D p hp k V hVdim) d hd
  · have hσV : integralClosedSubspaceRestrictSection D p hp L σ V ≠ 0 :=
      closedSubspaceRestrictSection_ne_zero D p hp L σ hL ⟨V.subspace, V.isClosedSubspace⟩ hVE
    rw [← subspacePointSet_vanishingLocus_member D p hp L σ hL V,
      ← sub_add_cancel c
      (firstChernCapCycleMap D (V.subspace.ι ≫ p) hVg k
        (memberGeneratorChernRule D p hp L σ hL k V hVdim) d)]
    refine IsRationallyEquivalentToZeroWithinCanonical.add ?_ ?_
    · refine isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_sub D _ hVg k _ _ d
        _ fun T₀ hT₀ _ hne => ?_
      by_cases hT₀E : T₀.subspace ≤ (vanishingLocus D (V.subspace.ι ≫ p) hVg
          (integralClosedSubspaceRestrict D p hp L V)
          (integralClosedSubspaceRestrictSection D p hp L σ V)).1
      · refine ⟨?_, subspacePointSet_mono_of_le D hT₀E⟩
        simpa only [sub_add_sub_cancel] using
          (isPrincipalDivisorCycleOfGood_closedSubspaceChernRule_sub_canonicalFirstChernRule D p hp
            L σ hL k V T₀ hT₀ ((le_vanishingLocus_member_iff D p hp L σ hL V T₀).1 hT₀E)).add
          (isPrincipalDivisorCycleOfGood_canonicalFirstChernRule_sub_memberGeneratorChernRule D p hp
            L σ hL k V hVdim T₀ hT₀)
      · exact absurd
          (closedSubspaceChernRule_restrictedSectionChernRule_eq_memberGeneratorChernRule D p hp L
            σ hL k V _ hVdim T₀ hT₀ hT₀E) hne
    · exact isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_generatorChernRule D
        (V.subspace.ι ≫ p) hVg V.isIntegralSpace (integralClosedSubspaceRestrict D p hp L V)
        (isInvertibleModule_memberRestrict D p hp L hL V)
        (deltaDimensionClosed_member D p hp k V hVdim)
        (integralClosedSubspaceRestrictSection D p hp L σ V) hσV d hd

include hL in
/-- **The Gysin homomorphism of Stacks 0ER1 carries rational equivalences to rational
equivalences.**  In Situation 0EDT let `X/B` be good, `ℒ` invertible with a global section `σ` and
`i : E = Z(σ) → X` the vanishing locus.  The Gysin cycle map `i^* : Z_{k+1}(X) ⟶ Z_k(E)` of
Stacks 0ER1 at its own component rule `AlgebraicGeometry.Space.sectionGysinRule` carries every
`(k+1)`-cycle rationally equivalent to zero on `X` to a `k`-cycle rationally equivalent to zero on
`E`, rational equivalence being read at the canonical embeddings of Stacks 0ENK on both sides. -/
theorem gysinCycleMapFactorsThroughRationalEquivalenceCanonical_sectionGysinRule :
    GysinCycleMapFactorsThroughRationalEquivalenceCanonical.{u + 1} D p hp
      (vanishingLocus D p hp L σ) (isGood_vanishingLocus D p hp L σ) k
      (sectionGysinRule D p hp L σ k hL) :=
  gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_firstChernCapWithinOnMember.{u + 1}
    D p hp L σ hL k (restrictedDivisorCycle D p hp L k hL) fun V hV d hd =>
      isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_member D p hp L σ hL k V hV
        d hd

/-- **Stacks 0ERA, the map.**  The Gysin homomorphism `i^* : CH_{k+1}(X) ⟶ CH_k(E)` of the triple
`(ℒ, σ, i : E → X)` of Definition 0ER1, descended from the Gysin cycle map of Stacks 0ER1 through
the Chow groups of Stacks 0EQ6. -/
def sectionGysinChowGroupMap :
    chowGroupCanonical.{u + 1} D p hp (k + 1) →+
      chowGroupCanonical.{u + 1} D ((vanishingLocus D p hp L σ).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L σ) k :=
  gysinChowGroupMapCanonical.{u + 1} D p hp (vanishingLocus D p hp L σ)
    (isGood_vanishingLocus D p hp L σ) k (sectionGysinRule D p hp L σ k hL)
    (gysinCycleMapFactorsThroughRationalEquivalenceCanonical_sectionGysinRule D p hp L σ hL k)

/-- The descended Gysin map sends the class of `α` to the class of `i^*α`. -/
@[simp]
theorem sectionGysinChowGroupMap_chowClassCanonical (α : CycleGroup D p (k + 1)) :
    sectionGysinChowGroupMap D p hp L σ hL k (chowClassCanonical.{u + 1} D p hp (k + 1) α) =
      chowClassCanonical.{u + 1} D ((vanishingLocus D p hp L σ).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L σ) k
        (gysinCycleMap D p (vanishingLocus D p hp L σ) (isGood_vanishingLocus D p hp L σ) k
          (sectionGysinRule D p hp L σ k hL) α) :=
  rfl

/-- The descended Gysin map, read in the coarser quotient `AlgebraicGeometry.Space.chowGroup`, is
the refined Gysin homomorphism `AlgebraicGeometry.Space.sectionRefinedGysin` registered as Stacks
0ER1. -/
theorem chowGroupCanonicalToChowGroup_sectionGysinChowGroupMap (α : CycleGroup D p (k + 1)) :
    chowGroupCanonicalToChowGroup.{u + 1} D ((vanishingLocus D p hp L σ).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L σ) k
        (sectionGysinChowGroupMap D p hp L σ hL k (chowClassCanonical.{u + 1} D p hp (k + 1) α)) =
      sectionRefinedGysin.{u + 1} D p hp L σ k hL α :=
  rfl

/-- **Stacks 0ERA.**  In Situation 0EDT let `X/B` be good and let `(ℒ, σ, i : E → X)` be as in
Definition 0ER1: `ℒ` an invertible `𝒪_X`-module, `σ ∈ Γ(X, ℒ)` and `i : E = Z(σ) → X` the closed
immersion of its vanishing locus.  The Gysin homomorphism `i^* : Z_{k+1}(X) → CH_k(E)` of
Definition 0ER1 factors through rational equivalence: there is a homomorphism

`i^* : CH_{k+1}(X) ⟶ CH_k(E)`

sending the class of every `(k+1)`-cycle `α` to `i^*α`, i.e. to the class of the cycle
`∑ n_W i^*[W]` of Stacks 0ER1(2).

The Gysin map on cycles is `AlgebraicGeometry.Space.gysinCycleMap` at
`AlgebraicGeometry.Space.sectionGysinRule`, the component rule of Stacks 0ER1(1) with every
ingredient constructed, which is the rule of `AlgebraicGeometry.Space.sectionRefinedGysin`; the
Chow groups are `AlgebraicGeometry.Space.chowGroupCanonical`, Stacks 0EQ6 with `div(f_j)` read at
the canonical embeddings of Stacks 0ENK.  The map is
`AlgebraicGeometry.Space.sectionGysinChowGroupMap`; nothing is assumed. -/
@[stacks 0ERA "i^* : CH_{k+1}(X) → CH_k(D) for X/B good and (L, s, i : D → X) as in 0ER1 (L \
invertible, s a global section, D = Z(s)): the Gysin cycle map of 0ER1 at its own constructed \
rule sectionGysinRule descends through the Chow groups chowGroupCanonical of 0EQ6 (div(f_j) at \
the canonical 0ENK embeddings). Unconditional: the member cases are 0EQY on V ⊆ D and the key \
formula 0EQV (the content of 0ER9 at N = O_V) on V ⊄ D, both carried inside D; 0ER5 and 0EQC are \
replaced by the carrier-respecting reassembly"]
theorem exists_sectionGysinChowGroupMap :
    ∃ F : chowGroupCanonical.{u + 1} D p hp (k + 1) →+
        chowGroupCanonical.{u + 1} D ((vanishingLocus D p hp L σ).1.ι ≫ p)
          (isGood_vanishingLocus D p hp L σ) k,
      ∀ α : CycleGroup D p (k + 1),
        F (chowClassCanonical.{u + 1} D p hp (k + 1) α) =
          chowClassCanonical.{u + 1} D ((vanishingLocus D p hp L σ).1.ι ≫ p)
            (isGood_vanishingLocus D p hp L σ) k
            (gysinCycleMap D p (vanishingLocus D p hp L σ) (isGood_vanishingLocus D p hp L σ) k
              (sectionGysinRule D p hp L σ k hL) α) :=
  ⟨sectionGysinChowGroupMap D p hp L σ hL k,
    sectionGysinChowGroupMap_chowClassCanonical D p hp L σ hL k⟩

end AlgebraicGeometry.Space

end
