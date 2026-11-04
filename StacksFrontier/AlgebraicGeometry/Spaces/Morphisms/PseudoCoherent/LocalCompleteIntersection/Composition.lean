module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.FlatBaseChange

/-!
# Composition of local complete intersection morphisms of algebraic spaces

A composition of local complete intersection morphisms of algebraic spaces over `S` is a local
complete intersection morphism.

## Main results

* `AlgebraicGeometry.Space.isLocalCompleteIntersection_comp`: if `f : X ⟶ Y` and `g : Y ⟶ Z` are
  local complete intersection morphisms of algebraic spaces, so is `f ≫ g`.

## References

* [Stacks Project, Tag 06C8](https://stacks.math.columbia.edu/tag/06C8)
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- A composition of local complete intersection morphisms of algebraic spaces over `S` is a
local complete intersection morphism: if `f : X ⟶ Y` and `g : Y ⟶ Z` are local complete
intersection morphisms, so is `f ≫ g`. -/
@[stacks 06C8]
public theorem isLocalCompleteIntersection_comp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsLocalCompleteIntersection B S hS f)
    (hg : IsLocalCompleteIntersection B S hS g) :
    IsLocalCompleteIntersection B S hS (f ≫ g) := by
  have : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
        MorphismProperty Scheme.{u}) :=
    ⟨_root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_comp⟩
  exact holdsOnEveryEtaleChart_comp B S hS
    (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
      MorphismProperty Scheme.{u})
    (isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism
      _root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale)
    hX hY hZ f g hf hg

end AlgebraicGeometry.Space

end
