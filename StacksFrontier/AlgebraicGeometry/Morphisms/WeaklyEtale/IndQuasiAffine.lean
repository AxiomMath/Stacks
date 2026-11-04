module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksCore.Tactic.StacksAttribute

/-!
# Ind-quasi-affine schemes and morphisms

A scheme is ind-quasi-affine when each of its quasi-compact open subschemes is quasi-affine.
A morphism is ind-quasi-affine when the inverse image of every affine open subscheme of its
target is an ind-quasi-affine scheme.

## Main definitions

* `AlgebraicGeometry.IsIndQuasiAffine` is the ind-quasi-affineness predicate for schemes.
* `AlgebraicGeometry.IsIndQuasiAffineHom` is the ind-quasi-affineness predicate for morphisms
  of schemes.

## Implementation notes

An open subscheme is represented by `U.toScheme`. Quasi-compactness of the open is expressed
as compactness of its underlying subset.

## References

* [Stacks Project, Tag 0AP6](https://stacks.math.columbia.edu/tag/0AP6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A scheme is ind-quasi-affine if each quasi-compact open subscheme is quasi-affine. -/
@[stacks 0AP6 "schemes"]
class IsIndQuasiAffine (X : Scheme.{u}) : Prop where
  isQuasiAffine (U : X.Opens) (hU : IsCompact (U : Set X)) : U.toScheme.IsQuasiAffine

mk_iff_of_inductive_prop AlgebraicGeometry.IsIndQuasiAffine
  AlgebraicGeometry.isIndQuasiAffine_iff

/-- A morphism of schemes is ind-quasi-affine if the inverse image of every affine open subscheme
of its target is an ind-quasi-affine scheme. -/
@[stacks 0AP6 "morphisms"]
class IsIndQuasiAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  isIndQuasiAffine_preimage (U : Y.Opens) (hU : IsAffineOpen U) :
    IsIndQuasiAffine (f ⁻¹ᵁ U).toScheme

mk_iff_of_inductive_prop AlgebraicGeometry.IsIndQuasiAffineHom
  AlgebraicGeometry.isIndQuasiAffineHom_iff

end AlgebraicGeometry
