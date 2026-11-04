module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineBaseChangeModuli
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineModuliInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineGroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSourceOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperImageAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubmersiveComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.AffineQuotientPoints

/-!
# The moduli map of a well-nigh affine stack is a separated, quasi-compact universal homeomorphism

Let `𝒳` be a well-nigh affine algebraic stack with chart `x : U ⟶ 𝒳` and moduli morphism
`f : 𝒳 ⟶ M = Spec C` (`AlgebraicGeometry.Stack.WellNighAffineChart.moduliMap`). This file proves
the second sentence of Stacks 0DUP: `f` is separated, quasi-compact and a universal
homeomorphism.

* Separatedness: `𝒳` is separated over `S` (Stacks 0DUM), and the relative diagonal of
  `M ⟶ S` is separated because that 1-morphism is representable by algebraic spaces, so `f` is
  separated by Stacks 050M, part (3), in the form of Stacks 050N, part (7).
* Quasi-compactness: `f ∘ x` is the 1-morphism of the quotient map `U ⟶ M`, which is integral
  (Stacks 03BJ), hence affine and quasi-compact; since `x` is surjective, `f` is quasi-compact by
  Stacks 050X.
* Universal closedness: `U ⟶ M` is integral, hence universally closed (Stacks 01WM), and `f` is
  universally closed by Stacks 0CQK.
* Surjectivity: `U ⟶ M` is surjective by Stacks 03BL, so `f` is.
* Universal homeomorphism: every base change of `f` is continuous, closed, injective (universal
  injectivity, `AlgebraicGeometry.Stack.WellNighAffineChart.universallyInjective_moduliMap`) and
  surjective on points, hence a homeomorphism on points.

## Implementation notes

The relative properties of `f ∘ x` (in the sense of Stacks 04XB) are transported from those of
the 1-morphism `U ⟶ M` of represented stacks along the comparison equivalence between the slice
over `M` and the category of elements of `h_M`
(`AlgebraicGeometry.Stack.WellNighAffineChart.chart_comp_moduliMap_eq`), by
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences_symm`.

## References

* [Stacks Project, Tag 0DUP](https://stacks.math.columbia.edu/tag/0DUP)
* [Stacks Project, Tag 050M](https://stacks.math.columbia.edu/tag/050M)
* [Stacks Project, Tag 050X](https://stacks.math.columbia.edu/tag/050X)
* [Stacks Project, Tag 0CQK](https://stacks.math.columbia.edu/tag/0CQK)
* [Stacks Project, Tag 03BJ](https://stacks.math.columbia.edu/tag/03BJ)
* [Stacks Project, Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Morphisms

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A well-nigh affine algebraic stack is separated over `S`**, read off the groupoid
presentation of Stacks 0DUM. -/
theorem isSeparatedOver_of_isWellNighAffine (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) : IsSeparatedOver.{u, w} B S hS 𝒳 := by
  obtain ⟨U, R, s, t, c, hG, hU, -, hs, ht, he⟩ :=
    hasAffineFiniteLocallyFreeGroupoidPresentation_of_isWellNighAffine B S hS 𝒳 h𝒳
  exact isSeparatedOver_of_representedGroupoid_isFiniteLocallyFree B S hS 𝒳 s t c hG hU hs ht he

namespace WellNighAffineChart

variable {B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS} (K : WellNighAffineChart.{u, w} B S hS 𝒳)

/-- **`f ∘ x` is the 1-morphism of the quotient map `U ⟶ M` followed by the comparison of the
slice over `M` with the category of elements of `h_M`.** -/
theorem chart_comp_moduliMap_eq :
    BasedFunctor.comp K.chart.hom.hom K.moduliMap.hom.hom =
      BasedFunctor.comp (schemeFibredCategoryMap B S hS K.quotientMap).hom
        (sliceElementsComparison B S hS K.moduliObject) := by
  rw [K.chart_comp_moduliMap]
  have : (fibredCategory B S hS K.moduliSpace.obj).val.p.IsFiberedInSets :=
    inferInstanceAs (PresheafOfCategories.discreteProjection K.moduliSpace.obj).IsFiberedInSets
  refine BasedCategory.BasedFunctor.ext' ?_
  refine Functor.IsFiberedInSets.eq_of_obj_eq _ _ _ _
    (BasedFunctor.comp (sliceElementsComparison B S hS K.U)
      (associatedMap B S hS (yoneda.map K.quotientMap)).1.hom).w
    (BasedFunctor.comp (schemeFibredCategoryMap B S hS K.quotientMap).hom
      (sliceElementsComparison B S hS K.moduliObject)).w (fun z => ?_)
  exact (comp_sliceElementsComparison_obj _ z).trans rfl

/-- `f ∘ x` is representable by algebraic spaces, its source being a scheme. -/
theorem isRepresentable_chart_comp_moduliMap :
    IsRepresentableByAlgebraicSpaces B S hS (K.chart ≫ K.moduliMap).hom.hom :=
  isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
    (algebraicSpaceStack.{u, w} B S hS K.moduliSpace.obj K.moduliSpace.property).property
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS K.U) (K.chart ≫ K.moduliMap).hom

/-- **`f ∘ x` has every relative property (Stacks 04XB) of the quotient map `U ⟶ M`.** -/
theorem hasRelativeProperty_chart_comp_moduliMap (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hP : P (schemeSpaceMap K.quotientMap :
      (schemeSpace K.U : AlgebraicSpaces B S hS) ⟶
        schemeSpace K.moduliObject)) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P (K.chart ≫ K.moduliMap).hom
      K.isRepresentable_chart_comp_moduliMap := by
  have : Functor.IsEquivalence
      (BasedFunctor.id (schemeFibredCategory B S hS K.U).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 _))
  exact relativeProperty_of_equivalences_symm B S hS P
    (schemeFibredCategoryMap B S hS K.quotientMap).hom
    (BasedFunctor.comp K.chart.hom.hom K.moduliMap.hom.hom)
    (BasedFunctor.id _) (sliceElementsComparison B S hS K.moduliObject)
    (eqToIso K.chart_comp_moduliMap_eq)
    (hasRelativeProperty_schemeFibredCategoryMap B S hS P K.quotientMap hP)

/-- The quotient map `U ⟶ M` is integral (Stacks 03BJ). -/
instance isIntegralHom_toScheme_map_quotientMap :
    IsIntegralHom ((BigFppfOver.toScheme B S hS).map K.quotientMap) := by
  rw [toScheme_map_quotientMap]
  exact GroupoidScheme.isIntegralHom_objectsToInvariantSpectrum K.groupoidScheme

/-- **`f` is surjective.** The quotient map `U ⟶ M` is surjective by Stacks 03BL, so `f ∘ x` is,
and therefore so is `f`. -/
theorem isSurjective_moduliMap : IsSurjective B S hS K.moduliMap := by
  have hsurj : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map K.quotientMap) := by
    rw [toScheme_map_quotientMap]
    exact ⟨GroupoidScheme.surjective_objectsToInvariantSpectrum K.groupoidScheme⟩
  have h : IsSurjective B S hS (K.chart ≫ K.moduliMap) :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS _
      K.isRepresentable_chart_comp_moduliMap).2
      (K.hasRelativeProperty_chart_comp_moduliMap (Space.surjectiveMorphismProperty B S hS)
        (Space.isSurjective_yoneda_map B S hS K.quotientMap hsurj))
  intro z
  obtain ⟨y, hy⟩ := h z
  refine ⟨AlgebraicStacks.pointsMap B S hS K.chart y, ?_⟩
  exact (congrFun (AlgebraicStacks.pointsMap_comp' B S hS K.chart K.moduliMap) y).symm.trans hy

/-- **`f` is quasi-compact**, by Stacks 050X: `f ∘ x` is the 1-morphism of the quotient map
`U ⟶ M`, an affine morphism, and `x` is surjective. -/
theorem isQuasiCompactMorphism_moduliMap : IsQuasiCompactMorphism.{u, w} B S hS K.moduliMap := by
  let : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isQuasiCompact_isLocalAtTarget_fppf B S hS
  have hrel : IsQuasiCompact B S hS (K.chart ≫ K.moduliMap).hom :=
    K.hasRelativeProperty_chart_comp_moduliMap (Space.quasiCompactProperty B S hS)
      (Space.isQuasiCompact_yoneda_map_of_isAffineHom B S hS K.quotientMap inferInstance)
  have hp := (isQuasiCompact_iff_baseChange_quasiCompact B S hS (K.chart ≫ K.moduliMap)
    K.isRepresentable_chart_comp_moduliMap).1 hrel
  exact isQuasiCompactMorphism_of_comp_of_isSurjective B S hS K.chart (K.chart ≫ K.moduliMap)
    K.moduliMap (Iso.refl _) K.isSurjective_chart hp

/-- **`f` is universally closed**, by Stacks 0CQK: `f ∘ x` is the 1-morphism of the integral,
hence universally closed, quotient map `U ⟶ M` (Stacks 01WM), and `x` is surjective. -/
theorem universallyClosed_moduliMap : AlgebraicStacks.UniversallyClosed B S hS K.moduliMap := by
  have hucLT : (Space.universallyClosedProperty B S hS).IsLocalAtTarget
      (Space.Topology.precoverage.{u, u} .fppf B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.precoverage.{u, u} .fpqc B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hrel : UniversallyClosed B S hS (K.chart ≫ K.moduliMap).hom :=
    K.hasRelativeProperty_chart_comp_moduliMap (Space.universallyClosedProperty B S hS)
      (Space.universallyClosed_yoneda_map B S hS K.quotientMap inferInstance)
  have hp : AlgebraicStacks.UniversallyClosed B S hS (K.chart ≫ K.moduliMap) :=
    (representable_universallyClosed_iff_closedMap_baseChange B S hS (K.chart ≫ K.moduliMap)
      K.isRepresentable_chart_comp_moduliMap).1 hrel
  exact AlgebraicStacks.universallyClosed_of_surjective_comp B S hS K.chart K.moduliMap hp
    K.isSurjective_chart

/-- **`f` is separated.** `𝒳` is separated over `S` by Stacks 0DUM and the relative diagonal of
the structure morphism of `M` is separated, `M` being an algebraic space; Stacks 050M, part (3)
concludes. -/
theorem isSeparated_moduliMap (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) :
    AlgebraicStacks.IsSeparated B S hS K.moduliMap :=
  isSeparated_of_isSeparatedOver_of_isSeparated_diagonal B S hS K.moduliMap
    (isSeparatedOver_of_isWellNighAffine B S hS 𝒳 h𝒳)
    (isSeparated_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS
      (structureMorphism B S hS
        (algebraicSpaceStack.{u, w} B S hS K.moduliSpace.obj K.moduliSpace.property))
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).property
        (isRepresentableByAlgebraicSpace_fibredCategory B S hS K.moduliSpace.obj
          K.moduliSpace.property)
        (structureMorphism B S hS
          (algebraicSpaceStack.{u, w} B S hS K.moduliSpace.obj K.moduliSpace.property)).hom)).2

/-- **`f` is a universal homeomorphism.** Every base change of `f` is continuous on points,
closed (universal closedness), injective (universal injectivity) and surjective (surjectivity of
`f`, Stacks 04XH). -/
theorem universalHomeomorphism_moduliMap : UniversalHomeomorphism B S hS K.moduliMap := by
  intro 𝒵 g P hP
  let := pointTopology B S hS P.pt.val
  let := pointTopology B S hS 𝒵.val
  refine isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨continuous_pointsMap B S hS _ _ _, ?_, K.universallyInjective_moduliMap 𝒵 g P hP, ?_⟩
  · exact isClosedMap_pointsMap_fst_congr B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g K.moduliMap).underlying P.underlying
      (isTwoFibreProduct_underlying_algebraicStacks B S hS _
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g K.moduliMap))
      (isTwoFibreProduct_underlying_algebraicStacks B S hS _ hP) (K.universallyClosed_moduliMap 𝒵 g)
  · intro z
    obtain ⟨x, hx⟩ := K.isSurjective_moduliMap (AlgebraicStacks.pointsMap B S hS g z)
    obtain ⟨p, hp, -⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS P hP z x hx.symm
    exact ⟨p, hp⟩

end WellNighAffineChart

end AlgebraicGeometry.Stack

end
