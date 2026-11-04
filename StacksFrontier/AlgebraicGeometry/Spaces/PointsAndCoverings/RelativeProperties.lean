module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transferring étaleness and surjectivity to the big fppf site over a scheme

Stability facts for the morphism properties from which properties of morphisms of algebraic
spaces over `S` are built: stability under base change of an inverse image along a functor
preserving fibre products, preservation of fibre products by
`AlgebraicGeometry.BigFppfOver.toScheme`, and stability of surjectivity under composition.

## Main results

* `CategoryTheory.MorphismProperty.inverseImage_isStableUnderBaseChange`: the inverse image
  of a base-change-stable property along a functor preserving fibre products is again
  stable under base change.
* `AlgebraicGeometry.Space.preservesLimitsOfShape_walkingCospan_toScheme`: the functor from
  the big fppf site over `S` to schemes preserves fibre products.
* `AlgebraicGeometry.surjective_isStableUnderComposition`: surjectivity of scheme morphisms is
  stable under composition.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.MorphismProperty

/-- The inverse image of a base-change-stable morphism property along a functor which preserves
fibre products is stable under base change. -/
theorem inverseImage_isStableUnderBaseChange {C : Type v} {D : Type w}
    [Category C] [Category D] (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    (P : MorphismProperty D) [P.IsStableUnderBaseChange] :
    (P.inverseImage F).IsStableUnderBaseChange where
  of_isPullback sq hg := IsStableUnderBaseChange.of_isPullback (P := P) (sq.map F) hg

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

/-- Surjectivity of scheme morphisms is stable under composition. -/
@[ega "I 2.2.7"]
theorem surjective_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

namespace Space

/-- The canonical functor from the big fppf site over `S` to schemes preserves fibre products. -/
theorem preservesLimitsOfShape_walkingCospan_toScheme (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
  comp_preservesLimitsOfShape _ _

end Space

end AlgebraicGeometry

end
