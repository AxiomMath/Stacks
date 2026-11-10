module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinKeyFormula

/-!
# The two refined Gysin maps of a pair of sections commute

In Situation 0EDT let `X/B` be good and let `(ℒ, s, i : E → X)` and `(ℒ', s', i' : E' → X)` be
two triples as in Stacks 0ER1: `ℒ`, `ℒ'` invertible `𝒪_X`-modules, `s`, `s'` global sections,
`E = Z(s)`, `E' = Z(s')`. On `E` the pair `(ℒ'|_E, s'|_E)` has vanishing locus
`Z(s'|_E) = E ×_X E'`, and on `E'` the pair `(ℒ|_{E'}, s|_{E'})` has vanishing locus
`Z(s|_{E'}) = E' ×_X E` (Stacks 0846, part (2)); both are `E ∩ E'`, identified by
`AlgebraicGeometry.Space.vanishingLocusIntersectionComparison`, which is the identity on points
of `X`. **Stacks 0ERC** asserts that the square of Gysin maps

`CH_k(X) → CH_{k-1}(E) → CH_{k-2}(E ∩ E')`,  `CH_k(X) → CH_{k-1}(E') → CH_{k-2}(E ∩ E')`

commutes, that is `(j')^* i^* α = j^* (i')^* α` for `j : E ∩ E' → E` and `j' : E ∩ E' → E'` the
Gysin maps of `(ℒ'|_E, s'|_E)` and `(ℒ|_{E'}, s|_{E'})`.

The proof is the source's. For an integral closed subspace `W ⊆ X` of δ-dimension `k`,
`i^*[W] = (W → E)_* div_{ℒ|_W}(σ)` for a regular meromorphic section `σ` of `ℒ|_W` which is
`s|_W` unless `W ⊆ E`. The Gysin map of `(ℒ', s')` commutes with the restrictions to `E` and to
`W` up to rational equivalence on `E ∩ E'`, so both composites are read on `W`, where they are
compared by the key formula (Stacks 0EQV) with the generators `s_i = s`, `s'_i = s'` off `E`,
resp. `E'`. All the rational equivalences produced are sums of principal divisors on integral
closed subspaces of `|W| ∩ |E| ∩ |E'|`, so they are read on `E ∩ E'`; and since they lie over
`|W|`, the case of a general cycle follows (Stacks 0EQ8).

## Main definitions

* `AlgebraicGeometry.Space.vanishingLocusIntersectionComparison`: the identification
  `Z(s'|_E) → Z(s|_{E'})` over `X`.

## Main results

* `exists_closedSubspaceCyclePushforward_gysinComponentCycle_eq_canonicalDivisorCycleAt`:
  the Gysin component of an integral closed subspace as a Weil divisor on it.
* `isRationallyEquivalentToZeroWithin_comparisonPushforward_gysinCycleMap_sub_integralCycle`:
  the case `α = [W]`.
* `AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_gysinCycleMap_comm`: **Stacks 0ERC**,
  in the Chow group of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK.
* `AlgebraicGeometry.Space.sectionRefinedGysin_gysinCycleMap_comm`: its image in the coarser
  quotient `AlgebraicGeometry.Space.chowGroup`.

## Implementation notes

The statement is given on representatives, as for the other results of this chapter whose
source statement is on Chow groups. A class of `CH_{k+2}(X)` is the class of a cycle `α`. The
inner Gysin maps are the cycle-level maps `Z_{k+2}(X) → Z_{k+1}(E)` of Stacks 0ER1, parts (1)
and (2), at the canonical component cycles (`AlgebraicGeometry.Space.sectionGysinRule`). The
outer Gysin map on the side of `E'` is `AlgebraicGeometry.Space.sectionRefinedGysin`, the class in
`CH_k(E ∩ E')` of the cycle-level map. On the side of `E` the outer Gysin map lands in
`CH_k(Z(s'|_E))`, and is read in `CH_k(Z(s|_{E'}))` through the identification of the two
vanishing loci: the class of the pushforward of the representing cycle. This form does not use
that the Gysin maps descend to the Chow groups (Stacks 0ERA). With that descent it is the source's
statement on classes.

Every rational equivalence constructed is a sum of principal divisors `div(f)` taken with the
canonical embeddings `R(V) → Q(𝒪^h_{V, ξ})` of Stacks 0ENK, as in Stacks 0EQ6.

## References

* [Stacks Project, Tag 0ERC](https://stacks.math.columbia.edu/tag/0ERC)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (L' : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s' : L'.sections)

/-! ### The intersection of the two vanishing loci -/

section Intersection

/-- **The identification of `Z(s'|_E)` with `Z(s|_{E'})`**, for `E = Z(s)` and `E' = Z(s')`: both
are the inverse image of one vanishing locus in the other (Stacks 0846, part (2)), and the map is
the identity on the underlying points of `X`. -/
def vanishingLocusIntersectionComparison {L L'} (s : L.sections) (s' : L'.sections)
    (hL : IsInvertibleSheaf D p hp L) (hL' : IsInvertibleSheaf D p hp L') :
    (closedSubspaceVanishingLocus D p hp L' s' (vanishingLocus D p hp L s)).1.toFunctor ⟶
      (closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s')).1.toFunctor :=
  Subfunctor.homOfLe
      (closedSubspaceVanishingLocus_eq_preimage D p hp s' (vanishingLocus D p hp L s) hL').le ≫
    (Subfunctor.preimageιIso (vanishingLocus D p hp L s).1 (vanishingLocus D p hp L' s').1).hom ≫
      Subfunctor.homOfLe
        (closedSubspaceVanishingLocus_eq_preimage D p hp s (vanishingLocus D p hp L' s') hL).ge

variable {L L'} (hL : IsInvertibleSheaf D p hp L) (hL' : IsInvertibleSheaf D p hp L')

/-- The identification `Z(s'|_E) → Z(s|_{E'})` lies over `X`. -/
theorem vanishingLocusIntersectionComparison_comp_ι :
    vanishingLocusIntersectionComparison D p hp s s' hL hL' ≫
        (closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s')).1.ι ≫
          (vanishingLocus D p hp L' s').1.ι =
      (closedSubspaceVanishingLocus D p hp L' s' (vanishingLocus D p hp L s)).1.ι ≫
        (vanishingLocus D p hp L s).1.ι := by
  ext T x
  rfl

/-- The identification `Z(s'|_E) → Z(s|_{E'})` is an isomorphism, its inverse being the
identification in the other direction. -/
theorem vanishingLocusIntersectionComparison_comp :
    vanishingLocusIntersectionComparison D p hp s s' hL hL' ≫
        vanishingLocusIntersectionComparison D p hp s' s hL' hL = 𝟙 _ := by
  ext T x
  rfl

/-- The identification `Z(s'|_E) → Z(s|_{E'})` is an isomorphism, with inverse the identification
`Z(s|_{E'}) → Z(s'|_E)`. -/
instance isIso_vanishingLocusIntersectionComparison :
    IsIso (vanishingLocusIntersectionComparison D p hp s s' hL hL') :=
  ⟨vanishingLocusIntersectionComparison D p hp s' s hL' hL,
    vanishingLocusIntersectionComparison_comp D p hp s s' hL hL',
    vanishingLocusIntersectionComparison_comp D p hp s' s hL' hL⟩

/-- The identification `Z(s'|_E) → Z(s|_{E'})` is a closed immersion. -/
theorem isClosedImmersion_vanishingLocusIntersectionComparison :
    IsClosedImmersion D.site D.base D.base_mem
      (vanishingLocusIntersectionComparison D p hp s s' hL hL') :=
  isClosedImmersion_of_isIso D.site D.base D.base_mem _

include hL' in
/-- The image in `|X|` of `Z(s'|_Y) ⊆ Y` lies in `|Y| ∩ |Z(s')|`. -/
theorem range_pointsMap_closedSubspaceVanishingLocus_subset
    (Y : ClosedSubspaces D.site D.base D.base_mem X) :
    Set.range (pointsMap D.site D.base D.base_mem _
        ((closedSubspaceVanishingLocus D p hp L' s' Y).1.ι ≫ Y.1.ι)) ⊆
      subspacePointSet D.site D.base D.base_mem X Y.1 ∩
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L' s').1 := by
  rintro _ ⟨g, rfl⟩
  rw [pointsMap_comp_apply]
  refine ⟨⟨_, rfl⟩, ?_⟩
  have h : pointsMap D.site D.base D.base_mem _
      (closedSubspaceVanishingLocus D p hp L' s' Y).1.ι g ∈
      subspacePointSet D.site D.base D.base_mem Y.1.toFunctor
        (closedSubspaceVanishingLocus D p hp L' s' Y).1 := ⟨g, rfl⟩
  generalize pointsMap D.site D.base D.base_mem _
    (closedSubspaceVanishingLocus D p hp L' s' Y).1.ι g = y at h ⊢
  rw [closedSubspaceVanishingLocus_eq_preimage D p hp s' Y hL', subspacePointSet_preimage] at h
  exact h

include hL' in
/-- Every point of `|Y| ∩ |Z(s')|` is the image of a point of `Z(s'|_Y) ⊆ Y`. -/
theorem subset_range_pointsMap_closedSubspaceVanishingLocus
    (Y : ClosedSubspaces D.site D.base D.base_mem X) :
    subspacePointSet D.site D.base D.base_mem X Y.1 ∩
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L' s').1 ⊆
      Set.range (pointsMap D.site D.base D.base_mem _
        ((closedSubspaceVanishingLocus D p hp L' s' Y).1.ι ≫ Y.1.ι)) := by
  rintro _ ⟨⟨y, rfl⟩, hy⟩
  have h : y ∈ subspacePointSet D.site D.base D.base_mem Y.1.toFunctor
      (closedSubspaceVanishingLocus D p hp L' s' Y).1 := by
    rw [closedSubspaceVanishingLocus_eq_preimage D p hp s' Y hL', subspacePointSet_preimage]
    exact hy
  obtain ⟨g, rfl⟩ := h
  exact ⟨g, pointsMap_comp_apply _ _ _ _ _ _⟩

end Intersection

/-! ### The Gysin component of an integral closed subspace, read on the subspace -/

section Component

variable {L} (hL : IsInvertibleSheaf D p hp L)

/-- **The Gysin component of `W` as a Weil divisor on `W`.** For an integral closed subspace
`W ⊆ X` of δ-dimension `k + 1`, the pushforward to `X` of the Gysin component `i^*[W]` of
`(ℒ, s)` is the pushforward from `W` of the Weil divisor of a regular meromorphic section `σ` of
`ℒ|_W` which is `s|_W` unless `Z(s|_W) = W`: if `W ⊆ Z(s)` this is the definition, and otherwise
`i^*[W] = [Z(s) ∩ W]_k = [Z(s|_W)]_k = div(s|_W)` by Stacks 0846, part (2), and Stacks 0EQF. -/
theorem exists_closedSubspaceCyclePushforward_gysinComponentCycle_eq_canonicalDivisorCycleAt
    {k : ℤ} (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) :
    ∃ (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
        (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩).1
        (closedSubspaceModuleRestrict D p hp L ⟨W.subspace, W.isClosedSubspace⟩))
      (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
        (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩).1 _ σ),
      (¬ (⊤ : Subfunctor W.subspace.toFunctor) ≤
          (closedSubspaceVanishingLocus D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).1 →
        σ = globalSectionMeromorphic D.site D.base D.base_mem
          (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩).1 _
          (closedSubspaceModuleRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩)) ∧
      closedSubspaceCyclePushforward D p hp (vanishingLocus D p hp L s) k
          (gysinComponentCycle D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s)
            k (sectionGysinRule D p hp L s k hL) W) =
        closedSubspaceCyclePushforward D p hp ⟨W.subspace, W.isClosedSubspace⟩ k
          (canonicalDivisorCycleAt D (W.subspace.ι ≫ p)
            (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩) W.isIntegralSpace _
            (isInvertibleModule_closedSubspaceModuleRestrict D p hp ⟨W.subspace, W.isClosedSubspace⟩
              L (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL)) σ hσ
            (by rw [deltaDimensionClosed_univ_integralClosedSubspace D p hp W, hW])) := by
  set E := vanishingLocus D p hp L s with hEdef
  have hE := isGood_vanishingLocus D p hp L s
  have hWg := isGood_integralClosedSubspace D p hp W
  have hk : deltaDimensionClosed D (W.subspace.ι ≫ p) hWg Set.univ isClosed_univ =
      ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D p hp W, hW]
  have hZ : (closedSubspaceVanishingLocus D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).1 =
      E.1.preimage W.subspace.ι :=
    closedSubspaceVanishingLocus_eq_preimage D p hp s ⟨W.subspace, W.isClosedSubspace⟩ hL
  by_cases hWE : W.subspace ≤ E.1
  · refine ⟨restrictedSectionOfIntegralClosedSubspace D p hp L hL W,
      isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem hWg.1
        W.isIntegralSpace (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hWg) _
        (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W),
      fun h => absurd ?_ h, ?_⟩
    · rw [hZ]
      intro U x _
      exact hWE U x.2
    · rw [gysinComponentCycle_of_le D p E hE k _ hW hWE,
        closedSubspaceCyclePushforward_containedPushforward D p hp E k hE hWE]
      rfl
  · have hs0 := modulePullbackSections_ne_zero_of_not_le D p hp L hL s W hWE
    refine ⟨globalSectionMeromorphic D.site D.base D.base_mem hWg.1 _
        (closedSubspaceModuleRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩),
      (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hWg.1 W.isIntegralSpace
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _ hWg) _
        (isInvertibleModule_integralClosedSubspaceRestrict D p hp L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) _).2
        (globalSectionMeromorphic_ne_zero D.site D.base D.base_mem hWg.1 _
          (isInvertibleModule_integralClosedSubspaceRestrict D p hp L
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) hs0),
      fun _ => rfl, ?_⟩
    have h0EQF := cycleCoeffOfClosedSubspace_vanishingLocus_eq_canonicalDivisorCycleAt D
      (W.subspace.ι ≫ p) hWg W.isIntegralSpace (integralClosedSubspaceRestrict D p hp L W)
      (isInvertibleModule_integralClosedSubspaceRestrict D p hp L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) W) hs0 hk
    have hd := deltaDimensionSubspace_preimage_integralClosedSubspace_le_of_not_le D p hp E W hWg
      k hW hWE
    have hd' : deltaDimensionSubspace D (W.subspace.ι ≫ p) hWg
        (closedSubspaceVanishingLocus D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).1
        (closedSubspaceVanishingLocus D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).2 ≤
          (k : EInt) := by
      have hZ' : closedSubspaceVanishingLocus D p hp L s ⟨W.subspace, W.isClosedSubspace⟩ =
          ⟨E.1.preimage W.subspace.ι, isClosedSubspace_preimage D.site D.base D.base_mem
            W.subspace.ι E.1 hp.1 W.isClosedSubspace.1 E.2⟩ := Subtype.ext hZ
      rw [hZ']
      exact hd
    have hcongr := closedSubspaceCycle_congr D (W.subspace.ι ≫ p) hWg hZ _ _ k hd' hd
    rw [gysinComponentCycle_of_not_le D p E hE k _ hW hWE]
    change closedSubspaceCyclePushforward D p hp E k
      (gysinIntersectionCycle D p hp E hE k W hW hWE) = _
    rw [← integralClosedSubspacePushforward_closedSubspaceCycle_preimage_eq_gysinIntersectionCycle
      D p hp E hE W hWg k hW hWE, ← hcongr]
    exact congrArg _ (Subtype.ext h0EQF)

end Component

/-! ### Pushforwards along the two readings of the intersection -/

section PushforwardComparison

variable {E E' : ClosedSubspaces D.site D.base D.base_mem X} (hE : D.IsGood (E.1.ι ≫ p))
    (hE' : D.IsGood (E'.1.ι ≫ p)) {F : ClosedSubspaces D.site D.base D.base_mem E.1.toFunctor}
    {F' : ClosedSubspaces D.site D.base D.base_mem E'.1.toFunctor}
    (hF : D.IsGood (F.1.ι ≫ E.1.ι ≫ p)) (hF' : D.IsGood (F'.1.ι ≫ E'.1.ι ≫ p))
    {e : F.1.toFunctor ⟶ F'.1.toFunctor} (he : IsClosedImmersion D.site D.base D.base_mem e)
    (hecomp : e ≫ F'.1.ι ≫ E'.1.ι = F.1.ι ≫ E.1.ι) (k : ℤ)

/-- Pushing a cycle forward along `F' → E' → X` is pushing it forward to `E'` and then to `X`. -/
theorem cycleGroupClosedPushforward_comp_ι_eq (y : CycleGroup D (F'.1.ι ≫ E'.1.ι ≫ p) k) :
    cycleGroupClosedPushforward D hp.1 hF'.1 (D.isDecentSpace_of_isGood p hp)
        (isClosedImmersion_comp D.site D.base D.base_mem _ _ F'.2.2 E'.2.2) p hp.2.2
        (F'.1.ι ≫ E'.1.ι ≫ p) (Category.assoc _ _ _) k y =
      closedSubspaceCyclePushforward D p hp E' k
        (closedSubspaceCyclePushforward D (E'.1.ι ≫ p) hE' F' k y) :=
  (cycleGroupClosedPushforward_cycleGroupClosedPushforward D hp.1 E'.2.1 F'.2.1
    (D.isDecentSpace_of_isGood p hp) (D.isDecentSpace_of_isGood _ hE') rfl F'.2.2 E'.2.2
    (isClosedImmersion_comp D.site D.base D.base_mem _ _ F'.2.2 E'.2.2) p hp.2.2 (E'.1.ι ≫ p)
    hE'.2.2 (F'.1.ι ≫ E'.1.ι ≫ p) rfl rfl (Category.assoc _ _ _) k y).symm

/-- Pushing forward along `F' → E' → X` after the comparison `e : F → F'` is pushing forward
along `F → E → X`. -/
theorem cycleGroupClosedPushforward_comparisonPushforward_eq
    (x : CycleGroup D (F.1.ι ≫ E.1.ι ≫ p) k) :
    cycleGroupClosedPushforward D hp.1 hF'.1 (D.isDecentSpace_of_isGood p hp)
        (isClosedImmersion_comp D.site D.base D.base_mem _ _ F'.2.2 E'.2.2) p hp.2.2
        (F'.1.ι ≫ E'.1.ι ≫ p) (Category.assoc _ _ _) k
        (comparisonPushforward D p E E' k F F' hF hF' he hecomp x) =
      closedSubspaceCyclePushforward D p hp E k
        (closedSubspaceCyclePushforward D (E.1.ι ≫ p) hE F k x) := by
  have hl := isClosedImmersion_comp D.site D.base D.base_mem _ _ F.2.2 E.2.2
  refine (cycleGroupClosedPushforward_cycleGroupClosedPushforward D hp.1 hF'.1 hF.1
    (D.isDecentSpace_of_isGood p hp) (D.isDecentSpace_of_isGood _ hF') hecomp he
    (isClosedImmersion_comp D.site D.base D.base_mem _ _ F'.2.2 E'.2.2) hl p hp.2.2
    (F'.1.ι ≫ E'.1.ι ≫ p) hF'.2.2 (F.1.ι ≫ E.1.ι ≫ p) (Category.assoc _ _ _)
    (comp_structure_of_comp_eq D p E E' F F' hecomp) (Category.assoc _ _ _) k x).trans ?_
  exact cycleGroupClosedPushforward_comp_ι_eq D p hp hE hF k x

end PushforwardComparison

/-! ### Stacks 0ERC -/

section Commutativity

variable {L L'} (hL : IsInvertibleSheaf D p hp L) (hL' : IsInvertibleSheaf D p hp L')

/-- **The case `α = [W]` of Stacks 0ERC.** For an integral closed subspace `W ⊆ X` of δ-dimension
`k + 2`, the two images of `[W]` in `Z_k(Z(s|_{E'}))` differ by a cycle rationally equivalent to
zero within the inverse image of `|W|`.

Read on `X`, the difference is a sum of canonical principal divisors on integral closed
subspaces of `|W| ∩ |E| ∩ |E'|`: with `i^*[W] = (W → E)_* div(σ)`, the compatibility of the Gysin
map of `(ℒ', s')` with the restrictions to `E` and to `W`
(`isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_closedSubspaceCyclePushforward_sub`)
moves both composites to `W`, where they are compared by the key formula
(`isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_canonicalDivisorCycleAt_sub`).
As the subspaces lie in the image of `Z(s|_{E'}) → X`, the sum is read on `Z(s|_{E'})`
(`AlgebraicGeometry.Space.IsCanonicallyRationallyEquivalentToZeroWithin.of_closedPushforward`). -/
theorem isRationallyEquivalentToZeroWithin_comparisonPushforward_gysinCycleMap_sub_integralCycle
    (k : ℤ) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1 + 1) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D
      ((closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s')).1.ι ≫
        (vanishingLocus D p hp L' s').1.ι ≫ p)
      (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s')) _ _)
      k
      (comparisonPushforward D p (vanishingLocus D p hp L s) (vanishingLocus D p hp L' s') k
          (closedSubspaceVanishingLocus D p hp L' s' (vanishingLocus D p hp L s))
          (closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s'))
          (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L s)) _ _)
          (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s'))
            _ _)
          (isClosedImmersion_vanishingLocusIntersectionComparison D p hp s s' hL hL')
          (vanishingLocusIntersectionComparison_comp_ι D p hp s s' hL hL')
          (gysinCycleMap D _ (closedSubspaceVanishingLocus D p hp L' s' (vanishingLocus D p hp L s))
            (isGood_vanishingLocus D _
              (isGood_closedSubspace D p hp (vanishingLocus D p hp L s)) _ _)
            k (sectionGysinRule D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L s)) _
              (closedSubspaceModuleRestrictSection D p hp L' s' (vanishingLocus D p hp L s)) k
              (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp (vanishingLocus D p hp L s)
                hL'))
            (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s)
              (k + 1) (sectionGysinRule D p hp L s (k + 1) hL)
              (integralCycle D p (k + 1 + 1) W hW))) -
        gysinCycleMap D _ (closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s'))
          (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s'))
            _ _)
          k (sectionGysinRule D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s')) _
            (closedSubspaceModuleRestrictSection D p hp L s (vanishingLocus D p hp L' s')) k
            (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp (vanishingLocus D p hp L' s')
              hL))
          (gysinCycleMap D p (vanishingLocus D p hp L' s') (isGood_vanishingLocus D p hp L' s')
            (k + 1) (sectionGysinRule D p hp L' s' (k + 1) hL')
            (integralCycle D p (k + 1 + 1) W hW)))
      ((pointsMap D.site D.base D.base_mem _ (vanishingLocus D p hp L' s').1.ι ∘
        pointsMap D.site D.base D.base_mem _
          (closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s')).1.ι) ⁻¹'
            subspacePointSet D.site D.base D.base_mem X W.subspace) := by
  classical
  have hdec := D.isDecentSpace_of_isGood p hp
  have hE : D.IsGood ((vanishingLocus D p hp L s).1.ι ≫ p) := isGood_vanishingLocus D p hp L s
  have hE' : D.IsGood ((vanishingLocus D p hp L' s').1.ι ≫ p) := isGood_vanishingLocus D p hp L' s'
  have hYWg := isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩
  -- the Gysin components of `[W]` as Weil divisors on `W`
  obtain ⟨σ, hσ, hσs, hσeq⟩ :=
    exists_closedSubspaceCyclePushforward_gysinComponentCycle_eq_canonicalDivisorCycleAt D p hp s
      hL W hW
  obtain ⟨σ', hσ', hσs', hσ'eq⟩ :=
    exists_closedSubspaceCyclePushforward_gysinComponentCycle_eq_canonicalDivisorCycleAt D p hp s'
      hL' W hW
  have hk2 : deltaDimensionClosed D (W.subspace.ι ≫ p) hYWg Set.univ isClosed_univ =
      ((k + 1 + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D p hp W, hW]
  rw [gysinCycleMap_integralCycle D p (vanishingLocus D p hp L s) hE (k + 1) _ hW,
    gysinCycleMap_integralCycle D p (vanishingLocus D p hp L' s') hE' (k + 1) _ hW]
  have KW :=
    isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_canonicalDivisorCycleAt_sub.{v}
      D (W.subspace.ι ≫ p) hYWg W.isIntegralSpace _
      (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp ⟨W.subspace, W.isClosedSubspace⟩ hL)
      (closedSubspaceModuleRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩) _
      (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp ⟨W.subspace, W.isClosedSubspace⟩ hL')
      (closedSubspaceModuleRestrictSection D p hp L' s' ⟨W.subspace, W.isClosedSubspace⟩) hk2 σ hσ
      hσs σ' hσ' hσs'
  have KX := KW.closedPushforward (hX := hp) (W.subspace.ι ≫ p) hYWg W.isClosedSubspace.2 rfl
  -- the target set
  obtain ⟨T, hT⟩ : ∃ T : Set (points D.site D.base D.base_mem X),
      T = subspacePointSet D.site D.base D.base_mem X W.subspace ∩
        (subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L s).1 ∩
          subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L' s').1) :=
    ⟨_, rfl⟩
  -- the components of `i^*[W]` lie over `W`
  have hcompW : ∀ (E₀ : ClosedSubspaces D.site D.base D.base_mem X)
      (hE₀ : D.IsGood (E₀.1.ι ≫ p)) (rule₀ : GysinComponentRule D p E₀ (k + 1))
      (Z : IntegralClosedSubspace D.site D.base D.base_mem E₀.1.toFunctor),
      (gysinComponentCycle D p E₀ hE₀ (k + 1) rule₀ W).1 Z ≠ 0 →
        subspacePointSet D.site D.base D.base_mem X
          (closedSubspaceComponentImage D p hp E₀.1 E₀.2 Z).subspace ⊆
            subspacePointSet D.site D.base D.base_mem X W.subspace := by
    intro E₀ hE₀ rule₀ Z hZ
    rw [IntegralClosedSubspace.subspacePointSet_pushforward]
    rintro _ ⟨z, hz, rfl⟩
    exact subspacePointSet_subset_of_gysinComponentCycle_ne_zero D p E₀ hE₀ (k + 1) rule₀ W Z hZ
      hz
  -- the two sides `i^*[W]` and `(i')^*[W]`, each compared with its reading on `W`
  have side := fun {M M' : Modules.{u, u} D.site D.base D.base_mem X hp.1} (t : M.sections)
      (t' : M'.sections) (hM : IsInvertibleSheaf D p hp M) (hM' : IsInvertibleSheaf D p hp M')
      (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor hYWg.1
        (closedSubspaceModuleRestrict D p hp M ⟨W.subspace, W.isClosedSubspace⟩))
      (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem _ hYWg.1 _ τ)
      (hτs : ¬ (⊤ : Subfunctor W.subspace.toFunctor) ≤
          (closedSubspaceVanishingLocus D p hp M t ⟨W.subspace, W.isClosedSubspace⟩).1 →
        τ = globalSectionMeromorphic D.site D.base D.base_mem hYWg.1 _
          (closedSubspaceModuleRestrictSection D p hp M t ⟨W.subspace, W.isClosedSubspace⟩))
      (hTm : ∀ x, x ∈ subspacePointSet D.site D.base D.base_mem X W.subspace →
        x ∈ subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp M t).1 →
        x ∈ subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp M' t').1 →
        x ∈ T) => by
    have R₂ :=
      isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_closedSubspaceCyclePushforward_sub
        D p hp t' ⟨W.subspace, W.isClosedSubspace⟩ hM' k
        (canonicalDivisorCycleAt D (W.subspace.ι ≫ p) hYWg W.isIntegralSpace _
          (isInvertibleModule_closedSubspaceModuleRestrict D p hp ⟨W.subspace, W.isClosedSubspace⟩
            M (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM)) τ hτ hk2)
    have R₁ :=
      isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_closedSubspaceCyclePushforward_sub
        D p hp t' (vanishingLocus D p hp M t) hM' k
        (gysinComponentCycle D p (vanishingLocus D p hp M t) (isGood_vanishingLocus D p hp M t)
          (k + 1) (sectionGysinRule D p hp M t (k + 1) hM) W)
    refine (R₂.mono (show _ ⊆ T from fun x hx => ?_)).sub
      (R₁.mono (show _ ⊆ T from fun x hx => ?_)) neg_mem_canonicalPrincipalDivisors
    · obtain ⟨hxW, hxE'⟩ := range_pointsMap_closedSubspaceVanishingLocus_subset D p hp t' hM'
        ⟨W.subspace, W.isClosedSubspace⟩ hx.1
      obtain ⟨V, hV⟩ := Set.mem_iUnion.1 hx.2
      split_ifs at hV with hV0
      · exact absurd hV (Set.notMem_empty x)
      · have hle := le_vanishingLocus_of_canonicalDivisorCycle_ne_zero D (W.subspace.ι ≫ p)
          hYWg W.isIntegralSpace _ (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp
            ⟨W.subspace, W.isClosedSubspace⟩ hM) _ hk2 τ hτ hτs V hV0
        exact hTm x hxW (subspacePointSet_mono_of_le D
          ((le_closedSubspaceVanishingLocus_iff D p hp t ⟨W.subspace, W.isClosedSubspace⟩ hM V).1
            hle) hV) hxE'
    · obtain ⟨hxE, hxE'⟩ := range_pointsMap_closedSubspaceVanishingLocus_subset D p hp t' hM'
        (vanishingLocus D p hp M t) hx.1
      obtain ⟨Z, hZ⟩ := Set.mem_iUnion.1 hx.2
      split_ifs at hZ with hZ0
      · exact absurd hZ (Set.notMem_empty x)
      · exact hTm x (hcompW _ (isGood_vanishingLocus D p hp M t) _ Z hZ0 hZ) hxE hxE'
  have S := side s s' hL hL' σ hσ hσs fun x hxW hxE hxE' => by rw [hT]; exact ⟨hxW, hxE, hxE'⟩
  have S' := side s' s hL' hL σ' hσ' hσs' fun x hxW hxE' hxE => by
    rw [hT]; exact ⟨hxW, hxE, hxE'⟩
  rw [hσeq] at S
  rw [hσ'eq] at S'
  -- the key formula on `W`, read on `X`
  have hpre : ∀ {M : Modules.{u, u} D.site D.base D.base_mem X hp.1} (t : M.sections)
      (hM : IsInvertibleSheaf D p hp M) (y : points D.site D.base D.base_mem W.subspace.toFunctor),
      y ∈ subspacePointSet D.site D.base D.base_mem W.subspace.toFunctor
        (closedSubspaceVanishingLocus D p hp M t ⟨W.subspace, W.isClosedSubspace⟩).1 →
      pointsMap D.site D.base D.base_mem _ W.subspace.ι y ∈
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp M t).1 := by
    intro M t hM y hy
    rwa [closedSubspaceVanishingLocus_eq_preimage D p hp t ⟨W.subspace, W.isClosedSubspace⟩ hM,
      subspacePointSet_preimage] at hy
  have KXT := KX.mono (show _ ⊆ T from fun x hx => by
    obtain ⟨y, ⟨hyE, hyE'⟩, rfl⟩ := hx
    rw [hT]
    exact ⟨⟨y, rfl⟩, hpre s hL y hyE, hpre s' hL' y hyE'⟩)
  -- read on `Z(s|_{E'})`
  have hj : IsClosedImmersion D.site D.base D.base_mem
      ((closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s')).1.ι ≫
        (vanishingLocus D p hp L' s').1.ι) :=
    isClosedImmersion_comp D.site D.base D.base_mem _ _
      (closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s')).2.2
      (vanishingLocus D p hp L' s').2.2
  have hTsub : T ⊆ Set.range (pointsMap D.site D.base D.base_mem _
      ((closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s')).1.ι ≫
        (vanishingLocus D p hp L' s').1.ι)) := by
    rw [hT]
    intro x hx
    exact subset_range_pointsMap_closedSubspaceVanishingLocus D p hp s hL
      (vanishingLocus D p hp L' s') ⟨hx.2.2, hx.2.1⟩
  refine (IsCanonicallyRationallyEquivalentToZeroWithin.of_closedPushforward (hX := hp) _
    (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s')) _ _)
    hj (Category.assoc _ _ _) hTsub ?_).mono ?_
  swap
  · intro x hx
    rw [Set.mem_preimage, hT] at hx
    simpa only [Set.mem_preimage, Function.comp_apply, pointsMap_comp_apply] using hx.1
  have H := (S.add KXT).sub S' neg_mem_canonicalPrincipalDivisors
  convert H using 1
  rw [map_sub, cycleGroupClosedPushforward_comparisonPushforward_eq D p hp
      (isGood_closedSubspace D p hp (vanishingLocus D p hp L s))
      (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L s)) _ _)
      (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s')) _ _),
    cycleGroupClosedPushforward_comp_ι_eq D p hp
      (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s'))
      (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s')) _ _)]
  simp only [map_sub]
  abel

/-- **Stacks 0ERC: the two refined Gysin maps of a pair of sections commute.** In Situation 0EDT
let `X/B` be good and let `(ℒ, s, i : E → X)`, `(ℒ', s', i' : E' → X)` be two triples as in
Stacks 0ER1. Let `j : Z(s'|_E) → E` and `j' : Z(s|_{E'}) → E'` be the closed immersions of the
triples `(ℒ'|_E, s'|_E)` on `E` and `(ℒ|_{E'}, s|_{E'})` on `E'`, both vanishing loci being
`E ∩ E'` (`AlgebraicGeometry.Space.vanishingLocusIntersectionComparison`). For every
`(k + 2)`-cycle `α` on `X`,

`j^* (i^* α) = (j')^* ((i')^* α)` in `CH_k(E ∩ E')`.

All four Gysin maps are the cycle-level maps of Stacks 0ER1, parts (1) and (2), at the canonical
component cycles (`AlgebraicGeometry.Space.gysinCycleMap` at
`AlgebraicGeometry.Space.sectionGysinRule`); the left side is carried to `Z(s|_{E'})` by the
identification of the two vanishing loci, and the classes are taken in the Chow group of
Stacks 0EQ6, `AlgebraicGeometry.Space.chowGroupCanonical`, whose rational equivalences are sums of
principal divisors at the canonical embeddings of Stacks 0ENK. As every class of `CH_{k+2}(X)` is
the class of a cycle, this is the identity of the source on representatives.

The proof is the source's: the case `α = [W]` is the key formula on `W`
(`isRationallyEquivalentToZeroWithin_comparisonPushforward_gysinCycleMap_sub_integralCycle`),
a sum of canonical principal divisors lying over `|W|`, and the general case follows by
Stacks 0EQ8 (`AlgebraicGeometry.Space.isCycleFamilySumWithin_closedPushforward_gysin_gysin_sub`). -/
@[stacks 0ERC "j^* i^* α = (j')^* (i')^* α in CH_k(D ∩ D') for every (k+2)-cycle α on X \
representing a class of CH_{k+2}(X), all four maps the refined Gysin maps of Stacks 0ER1 on cycles \
at the canonical component cycles, D ∩ D' being Z(s'|_D) identified with Z(s|_{D'}), the classes \
taken in the Chow group of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK \
(chowGroupCanonical); nothing carried"]
theorem chowClassCanonical_gysinCycleMap_gysinCycleMap_comm (k : ℤ)
    (α : CycleGroup D p (k + 1 + 1)) :
    chowClassCanonical.{max (u + 1) v} D
        ((closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s')).1.ι ≫
          (vanishingLocus D p hp L' s').1.ι ≫ p)
        (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s')) _ _)
        k
        (comparisonPushforward D p (vanishingLocus D p hp L s) (vanishingLocus D p hp L' s') k
          (closedSubspaceVanishingLocus D p hp L' s' (vanishingLocus D p hp L s))
          (closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s'))
          (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L s)) _ _)
          (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s'))
            _ _)
          (isClosedImmersion_vanishingLocusIntersectionComparison D p hp s s' hL hL')
          (vanishingLocusIntersectionComparison_comp_ι D p hp s s' hL hL')
          (gysinCycleMap D _ (closedSubspaceVanishingLocus D p hp L' s' (vanishingLocus D p hp L s))
            (isGood_vanishingLocus D _
              (isGood_closedSubspace D p hp (vanishingLocus D p hp L s)) _ _)
            k (sectionGysinRule D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L s)) _
              (closedSubspaceModuleRestrictSection D p hp L' s' (vanishingLocus D p hp L s)) k
              (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp (vanishingLocus D p hp L s)
                hL'))
            (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s)
              (k + 1) (sectionGysinRule D p hp L s (k + 1) hL) α))) =
      chowClassCanonical.{max (u + 1) v} D
        ((closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s')).1.ι ≫
          (vanishingLocus D p hp L' s').1.ι ≫ p)
        (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s')) _ _)
        k
        (gysinCycleMap D _ (closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s'))
          (isGood_vanishingLocus D _
            (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s')) _ _)
          k (sectionGysinRule D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s')) _
            (closedSubspaceModuleRestrictSection D p hp L s (vanishingLocus D p hp L' s')) k
            (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp (vanishingLocus D p hp L' s')
              hL))
          (gysinCycleMap D p (vanishingLocus D p hp L' s') (isGood_vanishingLocus D p hp L' s')
            (k + 1) (sectionGysinRule D p hp L' s' (k + 1) hL') α)) := by
  rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  exact IsCanonicallyRationallyEquivalentToZeroWithin.isRationallyEquivalentToZeroCanonical
    (isCycleFamilySumWithin_closedPushforward_gysin_gysin_sub D p
      (vanishingLocus D p hp L s) (vanishingLocus D p hp L' s') (isGood_vanishingLocus D p hp L s)
      (isGood_vanishingLocus D p hp L' s') k _ _ _ _ _ _ _ _
      (isClosedImmersion_vanishingLocusIntersectionComparison D p hp s s' hL hL')
      (vanishingLocusIntersectionComparison_comp_ι D p hp s s' hL hL')
      neg_mem_canonicalPrincipalDivisors
      (fun W hW =>
        isRationallyEquivalentToZeroWithin_comparisonPushforward_gysinCycleMap_sub_integralCycle
          D p hp s s' hL hL' k W hW) α)

/-- Stacks 0ERC in the Chow group `AlgebraicGeometry.Space.chowGroup`, whose rational
equivalences quantify the embedding `R(W) → Q(𝒪^h_{W,ξ})` existentially, with `(j')^*` read
through `AlgebraicGeometry.Space.sectionRefinedGysin`: the image of
`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_gysinCycleMap_comm` under the comparison
map `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup`. -/
theorem sectionRefinedGysin_gysinCycleMap_comm (k : ℤ) (α : CycleGroup D p (k + 1 + 1)) :
    chowClass.{max (u + 1) v} D
        ((closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s')).1.ι ≫
          (vanishingLocus D p hp L' s').1.ι ≫ p)
        (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s')) _ _)
        k
        (comparisonPushforward D p (vanishingLocus D p hp L s) (vanishingLocus D p hp L' s') k
          (closedSubspaceVanishingLocus D p hp L' s' (vanishingLocus D p hp L s))
          (closedSubspaceVanishingLocus D p hp L s (vanishingLocus D p hp L' s'))
          (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L s)) _ _)
          (isGood_vanishingLocus D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s'))
            _ _)
          (isClosedImmersion_vanishingLocusIntersectionComparison D p hp s s' hL hL')
          (vanishingLocusIntersectionComparison_comp_ι D p hp s s' hL hL')
          (gysinCycleMap D _ (closedSubspaceVanishingLocus D p hp L' s' (vanishingLocus D p hp L s))
            (isGood_vanishingLocus D _
              (isGood_closedSubspace D p hp (vanishingLocus D p hp L s)) _ _)
            k (sectionGysinRule D _ (isGood_closedSubspace D p hp (vanishingLocus D p hp L s)) _
              (closedSubspaceModuleRestrictSection D p hp L' s' (vanishingLocus D p hp L s)) k
              (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp (vanishingLocus D p hp L s)
                hL'))
            (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s)
              (k + 1) (sectionGysinRule D p hp L s (k + 1) hL) α))) =
      sectionRefinedGysin.{max (u + 1) v} D _
        (isGood_closedSubspace D p hp (vanishingLocus D p hp L' s'))
        (closedSubspaceModuleRestrict D p hp L (vanishingLocus D p hp L' s'))
        (closedSubspaceModuleRestrictSection D p hp L s (vanishingLocus D p hp L' s')) k
        (isInvertibleSheaf_closedSubspaceModuleRestrict D p hp (vanishingLocus D p hp L' s') hL)
        (gysinCycleMap D p (vanishingLocus D p hp L' s') (isGood_vanishingLocus D p hp L' s')
          (k + 1) (sectionGysinRule D p hp L' s' (k + 1) hL') α) := by
  rw [(sectionRefinedGysin_apply D _ _ _ _ k _ _).1]
  exact congrArg (chowGroupCanonicalToChowGroup.{max (u + 1) v} D _ _ k)
    (chowClassCanonical_gysinCycleMap_gysinCycleMap_comm D p hp s s' hL hL' k α)

end Commutativity


end AlgebraicGeometry.Space

end
