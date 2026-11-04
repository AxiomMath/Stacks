module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.EtaleLocalProperties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.UnramifiedPointTest
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty

/-!
# Étale local properties over a cartesian thickening, at the point test of Section 04XB

This file restates **Stacks 0BPJ**, parts (1) and (4), of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.EtaleLocalProperties` with the
square given by morphisms of the category of algebraic spaces over `S` and the properties by
morphism properties of that category.

## Main results

* `AlgebraicGeometry.Space.locallyQuasiFiniteProperty_iff_of_cartesianSquareOfThickeningHoms` and
  `AlgebraicGeometry.Space.formallyUnramifiedCharts_iff_of_cartesianSquareOfThickeningHoms`: the
  two parts at the point test of Section 04XB.

## Implementation notes

The two point-test statements are the same equivalences with the two smaller spaces given by
objects, rather than by subfunctors, of the category of algebraic spaces over `S`. That is the
shape in which the point test of **Stacks 03YK** reads a property of morphisms of algebraic spaces.

## References

* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two properties at the point test of Section 04XB

A condition of Stacks 04XB on a 1-morphism of categories fibred in groupoids representable by
algebraic spaces is a property of morphisms of the *category*
`AlgebraicGeometry.AlgebraicSpaces` of algebraic spaces over `S`, tested on the representing
morphism of each scheme-valued point of the target (**Stacks 03YK**,
`AlgebraicGeometry.Stack.HasRelativeProperty`). The two statements of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.EtaleLocalProperties` are read at
the subfunctor presentation of a thickening and so are not of that shape; the two below are the
same statements with the square given by four objects and four morphisms of that category, the two
vertical ones thickenings in the sense of `AlgebraicGeometry.Space.IsThickeningHom`.
-/

/-- **Stacks 0BPJ, part (1), at the point test of Section 04XB.** Let
`(f, f') : (X ⊂ X') → (Y ⊂ Y')` be a morphism of thickenings of algebraic spaces over `S` with
`f` and `f'` locally of finite type and `X = Y ×_{Y'} X'`. Then `f` is locally quasi-finite if
and only if `f'` is locally quasi-finite.

The square is given by morphisms of the category of algebraic spaces over `S` and the three
properties by morphism properties of that category. -/
@[stacks 0BPJ "part (1): locally quasi-finite, at the Section 04XB point test"]
theorem locallyQuasiFiniteProperty_iff_of_cartesianSquareOfThickeningHoms
    {X X' Y Y' : AlgebraicSpaces B S hS} {i : X ⟶ X'} {j : Y ⟶ Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j) (hsq : IsPullback f i j f')
    (hft : locallyOfFiniteTypeProperty B S hS f)
    (hft' : locallyOfFiniteTypeProperty B S hS f') :
    locallyQuasiFiniteProperty B S hS f ↔ locallyQuasiFiniteProperty B S hS f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianSquareOfThickeningHoms _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    (fun E => E.locallyQuasiFinite_iff) hi hj hsq hft hft'

/-- **Stacks 0BPJ, part (4), at the point test of Section 04XB.** Let
`(f, f') : (X ⊂ X') → (Y ⊂ Y')` be a morphism of thickenings of algebraic spaces over `S` with
`f` and `f'` locally of finite type and `X = Y ×_{Y'} X'`. Then `Ω_{X/Y} = 0` if and only if
`Ω_{X'/Y'} = 0`, the vanishing of the relative differentials being expressed, as in
`AlgebraicGeometry.Space.formallyUnramifiedCharts_iff_of_cartesianMorphismOfThickenings`, by
formal unramifiedness of the morphism of schemes in every commuting square of étale charts.

The square is given by morphisms of the category of algebraic spaces over `S`. -/
@[stacks 0BPJ "part (4): vanishing relative differentials, at the Section 04XB point test"]
theorem formallyUnramifiedCharts_iff_of_cartesianSquareOfThickeningHoms
    {X X' Y Y' : AlgebraicSpaces B S hS} {i : X ⟶ X'} {j : Y ⟶ Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j) (hsq : IsPullback f i j f')
    (hft : locallyOfFiniteTypeProperty B S hS f)
    (hft' : locallyOfFiniteTypeProperty B S hS f') :
    HoldsOnEveryEtaleChart B S hS
        (@_root_.AlgebraicGeometry.FormallyUnramified.{u} : MorphismProperty Scheme.{u}) f.hom ↔
      HoldsOnEveryEtaleChart B S hS
        (@_root_.AlgebraicGeometry.FormallyUnramified.{u} :
          MorphismProperty Scheme.{u}) f'.hom := by
  have hunr := unramifiedMorphismProperty_iff_of_cartesianSquareOfThickeningHoms
    B S hS hi hj hsq hft hft'
  simp only [unramifiedMorphismProperty,
    isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramifiedCharts] at hunr
  exact ⟨fun h => (hunr.mp ⟨hft, h⟩).2, fun h => (hunr.mpr ⟨hft', h⟩).2⟩

end AlgebraicGeometry.Space

end
