module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings

/-!
# Deformation diagrams of algebraic spaces

Two standing situations for deformation problems over algebraic spaces are recorded here, both
of them the algebraic-space counterpart of a diagram of schemes already in the library.

A *cartesian morphism of thickenings* is a commutative square between two thickenings
`X ⊂ X'` and `Y ⊂ Y'` of algebraic spaces which identifies `X` with `Y ×_{Y'} X'`, with both
horizontal maps locally of finite type. This is the situation in which a property of `X ⟶ Y`
is compared with the same property of its deformation `X' ⟶ Y'`.

A *flat deformation diagram* is a morphism of thickenings `X ⊂ X'`, `Y ⊂ Y'` over a thickening
`B ⊂ B'` of bases in which both unprimed spaces are the base changes of their primed
counterparts, the ambient target is locally of finite type over the ambient base, and the
ambient source is flat and locally of finite presentation over it.

## Main definitions

* `AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings` packages the two
  thickenings, their morphism, and the cartesian and finite-type conditions.
* `AlgebraicGeometry.Space.FlatDeformationDiagram` packages the six algebraic spaces, the three
  thickenings, the two horizontal morphisms, the two structure morphisms, and all the
  hypotheses.

## Implementation notes

A thickening of algebraic spaces is, as in `AlgebraicGeometry.Space.IsThickening`, a closed
subspace given as a `CategoryTheory.Subfunctor` of its ambient space whose inclusion is
surjective on points. In the first situation the smaller spaces are therefore given as
subfunctors and the morphism of thickenings is a morphism in the arrow category of presheaves,
whose `left` and `right` components are the two horizontal maps. In the second the six spaces
are all objects of `AlgebraicGeometry.AlgebraicSpaces`, so that the composites appearing in the
flatness and finiteness hypotheses are morphisms of algebraic spaces; the thickening condition
is then imposed on the range of each inclusion, which is required to be a monomorphism.

The base-change assertions are recorded by `CategoryTheory.IsPullback`, so neither situation
chooses an isomorphism to a particular fibre-product object. The scheme-level counterparts are
`Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram` and
`Stacks.Thickenings.FlatDeformationDiagram`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A cartesian morphism of thickenings of algebraic spaces over `S` whose two component maps
are locally of finite type. -/
structure CartesianLocallyFiniteTypeMorphismOfThickenings
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The ambient source algebraic space `X'`. -/
  X' : AlgebraicSpaces B S hS
  /-- The ambient target algebraic space `Y'`. -/
  Y' : AlgebraicSpaces B S hS
  /-- The smaller source algebraic space `X ⊂ X'`. -/
  X : Subfunctor X'.1
  /-- The smaller target algebraic space `Y ⊂ Y'`. -/
  Y : Subfunctor Y'.1
  /-- The source inclusion is a thickening. -/
  sourceThickening : IsThickening B S hS X' X
  /-- The target inclusion is a thickening. -/
  targetThickening : IsThickening B S hS Y' Y
  /-- The commutative square `(f, f')` between the two thickenings. -/
  morphism : Arrow.mk X.ι ⟶ Arrow.mk Y.ι
  /-- The map `f : X ⟶ Y` is locally of finite type. -/
  locallyOfFiniteType_left : IsLocallyOfFiniteType B S hS morphism.left
  /-- The map `f' : X' ⟶ Y'` is locally of finite type. -/
  locallyOfFiniteType_right : IsLocallyOfFiniteType B S hS morphism.right
  /-- The square identifies `X` with `Y ×_{Y'} X'`. -/
  cartesian : IsPullback morphism.left X.ι Y.ι morphism.right

namespace CartesianLocallyFiniteTypeMorphismOfThickenings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The map between the smaller algebraic spaces. -/
abbrev f (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) :
    T.X.toFunctor ⟶ T.Y.toFunctor := T.morphism.left

/-- The map between the ambient algebraic spaces. -/
abbrev f' (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) :
    T.X'.1 ⟶ T.Y'.1 := T.morphism.right

end CartesianLocallyFiniteTypeMorphismOfThickenings

/-- A flat deformation diagram of algebraic spaces over a scheme: a morphism of thickenings
over a thickening of bases, with cartesian special fibres, a locally finite type ambient
target, and a flat, locally finitely presented ambient source. -/
structure FlatDeformationDiagram
    (T : BigFppfSite.{u}) (S : Scheme.{u}) (hS : T.Contains S) where
  /-- The source of the morphism under study. -/
  X : AlgebraicSpaces T S hS
  /-- The ambient source. -/
  X' : AlgebraicSpaces T S hS
  /-- The target of the morphism under study. -/
  Y : AlgebraicSpaces T S hS
  /-- The ambient target. -/
  Y' : AlgebraicSpaces T S hS
  /-- The base. -/
  B : AlgebraicSpaces T S hS
  /-- The ambient base. -/
  B' : AlgebraicSpaces T S hS
  /-- The source thickening. -/
  iX : X ⟶ X'
  /-- The target thickening. -/
  iY : Y ⟶ Y'
  /-- The base thickening. -/
  iB : B ⟶ B'
  /-- The morphism under study. -/
  f : X ⟶ Y
  /-- Its ambient deformation. -/
  f' : X' ⟶ Y'
  /-- The structure morphism of the target over the base. -/
  g : Y ⟶ B
  /-- The structure morphism of the ambient target over the ambient base. -/
  g' : Y' ⟶ B'
  /-- The source inclusion is a monomorphism. -/
  iX_mono : Mono iX.hom
  /-- The target inclusion is a monomorphism. -/
  iY_mono : Mono iY.hom
  /-- The base inclusion is a monomorphism. -/
  iB_mono : Mono iB.hom
  /-- The source inclusion is a thickening. -/
  iX_thickening : IsThickening T S hS X' (Subfunctor.range iX.hom)
  /-- The target inclusion is a thickening. -/
  iY_thickening : IsThickening T S hS Y' (Subfunctor.range iY.hom)
  /-- The base inclusion is a thickening. -/
  iB_thickening : IsThickening T S hS B' (Subfunctor.range iB.hom)
  /-- The morphism of thickenings commutes. -/
  comm_f : iX ≫ f' = f ≫ iY
  /-- The maps to the base thickening commute. -/
  comm_g : iY ≫ g' = g ≫ iB
  /-- The source is the base change of the ambient source. -/
  isPullback_X : IsPullback iX (f ≫ g) (f' ≫ g') iB
  /-- The target is the base change of the ambient target. -/
  isPullback_Y : IsPullback iY g g' iB
  /-- The ambient target is locally of finite type over the ambient base. -/
  finiteType_Y' : IsLocallyOfFiniteType T S hS g'.hom
  /-- The ambient source is flat over the ambient base. -/
  flat_X' : IsFlat T S hS (f' ≫ g').hom
  /-- The ambient source is locally of finite presentation over the ambient base. -/
  finitePresentation_X' : IsLocallyOfFinitePresentation T S hS (f' ≫ g').hom

end AlgebraicGeometry.Space

end
