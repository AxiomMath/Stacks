module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat

/-!
# Flat pointed base change for purity

Comparing purity of a module along a fibre with purity after a base change requires the base
change to be pointed — a distinguished point of the new base over the distinguished point of
the old one — and flat at that point. This file packages that standing data together with the
finite type morphism and the finite type quasi-coherent module it is about.

## Main definitions

* `AlgebraicGeometry.FlatPointedBaseChangeSituation` records a finite type morphism, a finite
  type quasi-coherent module on its source, and a pointed base change which is flat at its
  distinguished point.

## Implementation notes

Following Mathlib, a morphism of finite type is represented by the two typeclass hypotheses
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`. The morphism of
pointed schemes is represented by its underlying morphism of schemes together with the equation
on distinguished points, and flatness at a point by
`AlgebraicGeometry.IsFlatAt` for the induced morphism of ringed spaces.

## References

* [Stacks Project, Tag 05J9](https://stacks.math.columbia.edu/tag/05J9)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The standing situation for a pointed base change which is flat at the distinguished point,
together with a finite type morphism and a finite type quasi-coherent module on its source. -/
public structure FlatPointedBaseChangeSituation where
  /-- The source scheme `X`. -/
  X : Scheme.{u}
  /-- The base scheme `S`. -/
  S : Scheme.{u}
  /-- The finite type morphism `f : X ⟶ S`. -/
  f : X ⟶ S
  /-- The morphism `f` is locally of finite type. -/
  [fLocallyOfFiniteType : LocallyOfFiniteType f]
  /-- The morphism `f` is quasi-compact. -/
  [fQuasiCompact : QuasiCompact f]
  /-- The finite type quasi-coherent module on `X`. -/
  F : X.Modules
  /-- The module `F` is of finite type. -/
  [FIsFiniteType : F.IsFiniteType]
  /-- The module `F` is quasi-coherent. -/
  [FIsQuasicoherent : F.IsQuasicoherent]
  /-- The distinguished point `s` of `S`. -/
  s : S
  /-- The source scheme `S'` of the pointed base change. -/
  S' : Scheme.{u}
  /-- The distinguished point `s'` of `S'`. -/
  s' : S'
  /-- The base-change morphism `S' ⟶ S`. -/
  g : S' ⟶ S
  /-- The base-change morphism preserves the distinguished points. -/
  mapsTo : g s' = s
  /-- The base-change morphism is flat at `s'`. -/
  flatAt : IsFlatAt g.toLRSHom.toShHom s'

attribute [instance]
  FlatPointedBaseChangeSituation.fLocallyOfFiniteType
  FlatPointedBaseChangeSituation.fQuasiCompact
  FlatPointedBaseChangeSituation.FIsFiniteType
  FlatPointedBaseChangeSituation.FIsQuasicoherent

end AlgebraicGeometry
