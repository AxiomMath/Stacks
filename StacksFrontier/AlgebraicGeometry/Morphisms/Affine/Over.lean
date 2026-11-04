module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute

/-!
# Schemes affine over a base

Affine schemes over a scheme `S` form a full subcategory of the category of schemes over `S`,
and base change along a morphism `T ⟶ S` carries it into the corresponding subcategory over
`T`. This file also records the structural map `g⁻¹ 𝒪_S ⟶ 𝒪_T` attached to a morphism of
schemes.

## Main definitions

* `AlgebraicGeometry.IsAffineHomOver` is the property of an object over `S` that its structure
  morphism is affine.
* `AlgebraicGeometry.AffineOver` is the category of schemes affine over `S`.
* `AlgebraicGeometry.inverseImageStructureMap` is the structural map `g⁻¹ 𝒪_S ⟶ 𝒪_T`.
* `AlgebraicGeometry.affineBaseChange` is base change of schemes, restricted to affine objects
  over the base.

## Implementation notes

`inverseImageStructureMap` is the adjunct of the comorphism `g.c` under the
pullback-pushforward adjunction on sheaves of commutative rings, so it needs no choice of a
construction of inverse images. `affineBaseChange` is well defined because affineness of a
morphism is stable under base change.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The property of an object over `S` that its structure morphism is affine. -/
abbrev IsAffineHomOver (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X ↦ IsAffineHom X.hom

/-- The category of schemes affine over `S`. -/
abbrev AffineOver (S : Scheme.{u}) := (IsAffineHomOver S).FullSubcategory

/-- The structural map `g⁻¹ 𝒪_S ⟶ 𝒪_T` associated to a scheme morphism
`g : T ⟶ S`. -/
noncomputable def inverseImageStructureMap {T S : Scheme.{u}} (g : T ⟶ S) :
    (TopCat.Sheaf.pullback CommRingCat g.base).obj S.sheaf ⟶ T.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).homEquiv
    S.sheaf T.sheaf).symm ⟨g.c⟩

/-- Base change of schemes, restricted to affine objects over the base. -/
noncomputable def affineBaseChange {T S : Scheme.{u}} (g : T ⟶ S) :
    AffineOver S ⥤ AffineOver T :=
  ObjectProperty.lift _ ((IsAffineHomOver S).ι ⋙ Over.pullback g) (fun X ↦ by
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback X.obj.hom g) X.property)

end AlgebraicGeometry
