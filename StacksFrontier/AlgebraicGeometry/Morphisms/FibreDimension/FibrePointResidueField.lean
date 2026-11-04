module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocusSpreadOut
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentFibre

/-!
# The residue field at a fibre point

Let `f : X ⟶ S` be a morphism of schemes and let `x` be a point of `X`. The point `x` lies in the
scheme-theoretic fibre `X_{f(x)}` as `f.asFiber x`, and the two points have the same residue
field. This file constructs that identification.

## Main definitions

* `AlgebraicGeometry.fiberResidueFieldMap` is the canonical map from the residue field of `x` to
  the residue field of the fibre at `f.asFiber x`, an isomorphism. Its inverse as a ring
  equivalence is `AlgebraicGeometry.fiberResidueFieldEquiv`, from
  `StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentFibre`.

## Main results

* `AlgebraicGeometry.ofHom_fiberResidueFieldEquiv` identifies that ring equivalence with the
  inverse of the residue-field map of the fibre embedding, transported to `x`.

## Implementation notes

The identification is obtained from the fibre embedding `f.fiberι (f x)`, which is a
preimmersion and hence surjective on stalks, so its residue-field map at `f.asFiber x` is an
isomorphism; transporting along `Scheme.Hom.fiberι_asFiber` lands it at `x`. The ring
equivalence in the other direction, and its characterising equation
`AlgebraicGeometry.fiberResidueFieldEquiv_spec`, are stated in
`StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentFibre`.

That the residue-field map of a morphism surjective on stalks is an isomorphism is
`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks`, available as an
instance through
`StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocusSpreadOut`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The canonical map from the residue field of `x` to the residue field of the fibre of `f` at
`f.asFiber x`. -/
public noncomputable def fiberResidueFieldMap (f : X ⟶ S) (x : X) :
    X.residueField x ⟶ (f.fiber (f x)).residueField (f.asFiber x) :=
  (X.residueFieldCongr (f.fiberι_asFiber x)).inv ≫
    (f.fiberι (f x)).residueFieldMap (f.asFiber x)

/-- The canonical map from the residue field of `x` to the residue field of the fibre at
`f.asFiber x` is an isomorphism. -/
public instance (f : X ⟶ S) (x : X) : IsIso (fiberResidueFieldMap f x) := by
  unfold fiberResidueFieldMap
  infer_instance

/-- `fiberResidueFieldEquiv` is the inverse of the residue-field map of the fibre embedding,
transported to `x`. -/
public theorem ofHom_fiberResidueFieldEquiv (f : X ⟶ S) (x : X) :
    CommRingCat.ofHom (fiberResidueFieldEquiv f x).toRingHom =
      inv ((f.fiberι (f x)).residueFieldMap (f.asFiber x)) ≫
        (X.residueFieldCongr (f.fiberι_asFiber x)).hom := rfl

end AlgebraicGeometry

end
