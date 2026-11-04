module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.ResidueFieldClosedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldSpectrumCoverFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented

/-!
# Finitely presented field-valued points of a locally Noetherian stack

For an algebraic stack `𝒵` the following are equivalent:

1. `𝒵` is reduced, locally Noetherian, and `|𝒵|` is a singleton;
2. there is a 1-morphism `Spec k ⟶ 𝒵` with `k` a field which is locally of finite presentation,
   surjective and flat.

This file proves (1) ⟹ (2) and the equivalence.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_schemeFibredCategoryMap`: a morphism of
  objects of the big fppf site which is locally of finite presentation induces a 1-morphism of
  the algebraic stacks they represent which is locally of finite presentation.
* `AlgebraicGeometry.Stack.exists_locallyOfFinitePresentation_surjective_fieldSpectrumCover`: a
  locally Noetherian algebraic stack whose space of points is a singleton admits a surjective
  1-morphism from the algebraic stack of the spectrum of a field which is locally of finite
  presentation.
* `hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian`, in the namespace
  `AlgebraicGeometry.Stack`: condition (1) implies condition (2).
* the equivalence `IsReducedLocallyNoetherianWithUniquePoint B S hS 𝒵 ↔`
  `HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒵` of conditions (1) and (2), in
  the namespace `AlgebraicGeometry.Stack`, named by joining the two predicates, decapitalized,
  by `_iff_`.

## References

* [Stacks Project, Tag 06MM](https://stacks.math.columbia.edu/tag/06MM)
* [Stacks Project, Tag 06MN](https://stacks.math.columbia.edu/tag/06MN)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06Q3](https://stacks.math.columbia.edu/tag/06Q3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of objects of the big fppf site which is locally of finite presentation induces
a 1-morphism of the algebraic stacks they represent which is locally of finite presentation.** -/
theorem isLocallyOfFinitePresentation_schemeFibredCategoryMap {V U : BigFppfOver B S hS}
    (j : V ⟶ U) (hj : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map j)) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS j) :
        schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS U) := by
  refine (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    (schemeStack.{u, w} B S hS V).property (schemeStack.{u, w} B S hS U).property _).2 ?_
  rw [hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (schemeStack.{u, w} B S hS V).property (schemeStack.{u, w} B S hS U).property
      (yoneda.obj V) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS U)
      (PresheafOfCategories.sliceElementsEquivalenceOver V)
      (PresheafOfCategories.sliceElementsEquivalenceOver U),
    representingMap_schemeFibredCategoryMap]
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget j).2 hj

/-- **A locally Noetherian algebraic stack with a single point admits a surjective field-valued
point which is locally of finite presentation.** -/
theorem exists_locallyOfFinitePresentation_surjective_fieldSpectrumCover
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (hnoeth : IsLocallyNoetherianStack B S hS 𝒵)
    (hne : Nonempty (AlgebraicStacks.points B S hS 𝒵))
    (hsub : Subsingleton (AlgebraicStacks.points B S hS 𝒵)) :
    ∃ (F : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵),
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f ∧ IsSurjective B S hS f := by
  obtain ⟨U, a, haSurj, haSmooth, hUnoeth⟩ := hnoeth
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) := hUnoeth
  obtain ⟨z⟩ := hne
  obtain ⟨zU, -⟩ := haSurj z
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  have x : (BigFppfOver.toScheme B S hS).obj U := pointsHomeomorphScheme B S hS U zU
  obtain ⟨R, g, hfield, hmono, hlfp⟩ :=
    exists_mono_locallyOfFinitePresentation_from_spec_isField
      ((BigFppfOver.toScheme B S hS).obj U) x
  let : Field R := hfield.toField
  have hcontains : B.Contains (Spec (CommRingCat.of R)) :=
    BigFppfSite.contains_of_mono B g U.left.2
  obtain ⟨Z, j, e, hje⟩ := Space.exists_siteObject_toScheme_map_eq B S hS hcontains g
  have hjlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map j) := by
    rw [hje]
    infer_instance
  refine ⟨{ carrier := R, base := Z, isSpec := e },
    Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS j) ≫ a, ?_, ?_⟩
  · exact AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS _ a
      (isLocallyOfFinitePresentation_schemeFibredCategoryMap.{u, w} B S hS j hjlfp)
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a haSmooth)
  · obtain ⟨p⟩ := nonempty_points_fieldSpectrumStack.{u, w} B S hS
      { carrier := R, base := Z, isSpec := e }
    exact fun _ => ⟨p, Subsingleton.elim _ _⟩

/-- A reduced, locally Noetherian algebraic stack whose space of points is a singleton admits a
1-morphism from the algebraic stack of the spectrum of a field which is locally of finite
presentation, surjective and flat. -/
theorem hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h : IsReducedLocallyNoetherianWithUniquePoint B S hS 𝒵) :
    HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒵 := by
  obtain ⟨hred, hnoeth⟩ := h
  obtain ⟨F₀, f₀, hf₀surj, hf₀flat⟩ :=
    hasFlatFieldSpectrumCover_of_isReducedWithUniquePoint.{u, w} B S hS 𝒵 hred
  obtain ⟨F, f, hlfp, hsurj⟩ :=
    exists_locallyOfFinitePresentation_surjective_fieldSpectrumCover.{u, w} B S hS 𝒵
      hnoeth hred.2.1 hred.2.2
  exact ⟨F, f, hlfp, hsurj,
    isFlat_of_fieldSpectrum_cover.{u, w} B S hS 𝒵 F₀ F f₀ f hf₀surj hf₀flat⟩

/-- For an algebraic stack `𝒵` over `S` the following are equivalent:

1. `𝒵` is reduced, locally Noetherian, and its space of points `|𝒵|` is a singleton;
2. there is a 1-morphism `Spec k ⟶ 𝒵` with `k` a field which is locally of finite presentation,
   surjective and flat. -/
@[stacks 06MP]
theorem
  isReducedLocallyNoetherianWithUniquePoint_iff_hasLocallyOfFinitePresentationFlatFieldSpectrumCover
    (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    IsReducedLocallyNoetherianWithUniquePoint B S hS 𝒵 ↔
      HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒵 :=
  ⟨hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian.{u, w} B S hS 𝒵,
    isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation.{u, w} B S hS 𝒵⟩

end AlgebraicGeometry.Stack

end
