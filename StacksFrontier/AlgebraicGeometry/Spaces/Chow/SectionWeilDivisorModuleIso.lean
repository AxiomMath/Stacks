module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.WeilDivisorOfInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorMeromorphicSectionIso
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionPullbackRegular

/-!
# The Weil divisor of a meromorphic section along an isomorphism of modules

In Situation 0EDT let `X/B` be good and integral with `n = dim_δ(X)`, and let `e : ℒ ≅ 𝒩` be an
isomorphism of invertible `𝒪_X`-modules. A meromorphic section `t` of `𝒩` is carried by the
isomorphism `𝒦_X(𝒩) ≅ 𝒦_X(ℒ)` attached to `e⁻¹` to a meromorphic section `e⁻¹(t)` of `ℒ`, and
the two have the same Weil divisor of Stacks 0EQE:

  `div_ℒ(e⁻¹(t)) = div_𝒩(t)` in `Z_{n-1}(X)`.

## Main results

* `AlgebraicGeometry.Space.sectionsMap_meromorphicSectionSheafMap_inv_ne_zero`: the image of a
  nonzero meromorphic section along an isomorphism of invertible modules is nonzero.
* `AlgebraicGeometry.Space.sectionWeilDivisor_sectionsMap_meromorphicSectionSheafMap_inv`: the
  identity of cycles displayed above.
* `AlgebraicGeometry.Space.isInvertibleSheaf_unit`,
  `AlgebraicGeometry.Space.isInvertibleSheaf_modulePullback` and
  `AlgebraicGeometry.Space.pullbackMeromorphicSection_ne_zero_of_isFlat`: the structure sheaf is
  invertible, the pullback of an invertible module is invertible, and the flat pullback of a
  nonzero meromorphic section of an invertible module to an integral space is nonzero.

## References

* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    {L N : Modules.{u, u} D.site D.base D.base_mem X hX.1}
    (hL : IsInvertibleSheaf D sX hX L) (hN : IsInvertibleSheaf D sX hX N)

/-- On a good integral space, a meromorphic section of an invertible module is regular iff
nonzero. -/
private theorem isRegularMeromorphicSection_iff_ne_zero_of_isGood
    (hint : IsIntegralSpace D.site D.base D.base_mem X) (hL : IsInvertibleSheaf D sX hX L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s ↔ s ≠ 0 :=
  isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hX.1 hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) s

include hint hL hN in
/-- **The image of a nonzero meromorphic section along an isomorphism of invertible modules is
nonzero.** If `e : ℒ ≅ 𝒩` and `t ≠ 0` is a meromorphic section of `𝒩`, then its image under the
isomorphism `𝒦_X(𝒩) ≅ 𝒦_X(ℒ)` attached to `e⁻¹` is nonzero. -/
theorem sectionsMap_meromorphicSectionSheafMap_inv_ne_zero (e : L ≅ N)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N) (ht : t ≠ 0) :
    SheafOfModules.sectionsMap
        (meromorphicSectionSheafMap D.site D.base D.base_mem X hX.1 e.inv) t ≠ 0 := by
  have hreg := (isRegularMeromorphicSection_iff_ne_zero_of_isGood D sX hX hint hN t).2 ht
  exact (isRegularMeromorphicSection_iff_ne_zero_of_isGood D sX hX hint hL _).1
    (isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem X hX.1 e.symm t hreg)

/-- **The Weil divisor of a meromorphic section does not change along an isomorphism of
invertible modules.** In Situation 0EDT let `X/B` be good and integral with `n = dim_δ(X)`, let
`e : ℒ ≅ 𝒩` be an isomorphism of invertible `𝒪_X`-modules and let `t` be a nonzero meromorphic
section of `𝒩`. Then

  `div_ℒ(e⁻¹(t)) = div_𝒩(t)` in `Z_{n-1}(X)`,

where `e⁻¹(t)` is the image of `t` under the isomorphism `𝒦_X(𝒩) ≅ 𝒦_X(ℒ)` attached to `e⁻¹`, and
both divisors are those of Stacks 0EQE. -/
theorem sectionWeilDivisor_sectionsMap_meromorphicSectionSheafMap_inv {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) (e : L ≅ N)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N) (ht : t ≠ 0) :
    sectionWeilDivisor D sX hX hint L hL hn
        (SheafOfModules.sectionsMap
          (meromorphicSectionSheafMap D.site D.base D.base_mem X hX.1 e.inv) t)
        (sectionsMap_meromorphicSectionSheafMap_inv_ne_zero D sX hX hint hL hN e t ht) =
      sectionWeilDivisor D sX hX hint N hN hn t ht := by
  have hNo := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  have hreg := (isRegularMeromorphicSection_iff_ne_zero_of_isGood D sX hX hint hN t).2 ht
  let := (genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint hNo).nontrivial
  let := (genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint hNo).isNoetherianRing
  let := (genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint hNo).krullDimLE
  refine Subtype.ext (funext fun Z => ?_)
  change divisorCycleCoefficients D sX hX hint.2.1 L _ _ Z =
    divisorCycleCoefficients D sX hX hint.2.1 N t _ Z
  by_cases h : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1
  · rw [divisorCycleCoefficients_of_codimension_eq_one D sX hX hint.2.1 L _ _ h,
      divisorCycleCoefficients_of_codimension_eq_one D sX hX hint.2.1 N _ _ h]
    exact (Z.toPrimeDivisor D.site D.base D.base_mem hX.1
      h).orderOfVanishingSection_canonicalLocalRatio_sectionsMap
      D.site D.base D.base_mem hX.1 hint.2.1 L N
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL)
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hN) hint hNo e t hreg
  · rw [divisorCycleCoefficients_of_codimension_ne_one D sX hX hint.2.1 L _ _ h,
      divisorCycleCoefficients_of_codimension_ne_one D sX hX hint.2.1 N _ _ h]

/-! ### Side conditions for the divisor of a pulled-back or trivialised section -/

/-- **The structure sheaf of a good algebraic space is an invertible module.** -/
theorem isInvertibleSheaf_unit :
    IsInvertibleSheaf D sX hX (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1).O)) :=
  @Stacks.SheafOfModules.isInvertible_unit _ _
    (SmallEtale.topology D.site D.base D.base_mem X) _ _
    (inferInstanceAs ((SmallEtale.topology D.site D.base D.base_mem X).WEqualsLocallyBijective
      AddCommGrpCat.{u}))
    (inferInstanceAs (HasWeakSheafify (SmallEtale.topology D.site D.base D.base_mem X)
      AddCommGrpCat.{u}))

variable {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sY : Y ⟶ D.space) (hY : D.IsGood sY)

/-- **The pullback of an invertible module along a morphism of good algebraic spaces is
invertible.** -/
theorem isInvertibleSheaf_modulePullback
    (f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩)
    (hL : IsInvertibleSheaf D sX hX L) :
    IsInvertibleSheaf D sY hY ((modulePullback D.site D.base D.base_mem f).obj L) :=
  isInvertible_modulePullback_obj D.site D.base D.base_mem f L hL

include hint in
/-- **The flat pullback of a nonzero meromorphic section of an invertible module to an integral
space is nonzero.** -/
theorem pullbackMeromorphicSection_ne_zero_of_isFlat
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (f : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩)
    (hflat : IsFlat D.site D.base D.base_mem f.hom) (hL : IsInvertibleSheaf D sX hX L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L) (hs : s ≠ 0) :
    pullbackMeromorphicSection D.site D.base D.base_mem f L
      (pullbacksMeromorphicSections_of_flat D.site D.base D.base_mem f.hom hflat) s ≠ 0 := by
  have hreg := (isRegularMeromorphicSection_iff_ne_zero_of_isGood D sX hX hint hL s).2 hs
  exact (isRegularMeromorphicSection_iff_ne_zero_of_isGood D sY hY hintY
    (isInvertibleSheaf_modulePullback D sX hX sY hY f hL) _).1
    (isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem f
      (pullbacksMeromorphicSections_of_flat D.site D.base D.base_mem f.hom hflat) L hL s hreg)

end AlgebraicGeometry.Space

end
