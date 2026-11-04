module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianStalkRingTensorFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange

/-!
# Relative Tor amplitude at the stalks of a cartesian square of algebraic spaces

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --h---> Y
```

be a cartesian square of algebraic spaces over a scheme `S` with `f` flat, and let `x̄'` be a
geometric point of `X'`.  Read at the stalks of the structure sheaves at the points of the small
étale sites determined by `x̄'` and its images, extension of scalars along the stalk map
`𝒪_{X, x̄} ⟶ 𝒪_{X', x̄'}` of Stacks 05V5 carries a K-flat complex of `𝒪_{X, x̄}`-modules with Tor
amplitude in `[a, b]` over `𝒪_{Y, ȳ}` to a complex with Tor amplitude in `[a, b]` over
`𝒪_{Y', ȳ'}`.  This is the stalkwise content of Stacks 0DKD, part (1), which is how the source
proves the base change of relative perfectness, Stacks 0DKT.

The commutative algebra is
`AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_torIndependent_flatBaseChange`:
`𝒪_{X, x̄}` is flat over `𝒪_{Y, ȳ}`, so the two are Tor independent with `𝒪_{Y', ȳ'}`, and
`𝒪_{X', x̄'}` is flat over `𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'}` by
`AlgebraicGeometry.Space.cartesian_stalkRing_tensor_flat`.

## Main results

* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_structureStalk_of_cartesian`: the
  statement above.

## References

* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 0DKT](https://stacks.math.columbia.edu/tag/0DKT)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Relative Tor amplitude survives base change, at the stalks.**  For a cartesian square of
algebraic spaces with `f` flat and a geometric point `x̄'` of `X'`, extension of scalars along
the stalk map `𝒪_{X, x̄} ⟶ 𝒪_{X', x̄'}` of a K-flat complex of `𝒪_{X, x̄}`-modules with Tor
amplitude in `[a, b]` over `𝒪_{Y, ȳ}` has Tor amplitude in `[a, b]` over `𝒪_{Y', ȳ'}`. -/
theorem hasTorAmplitudeCanonical_structureStalk_of_cartesian {X' X Y' Y : AlgebraicSpaces B S hS}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (h : Y' ⟶ Y) (hpb : IsPullback g' f' f h)
    (hf : IsFlat B S hS f.hom) (x' : GeometricPoint B S hS X'.1)
    (K : CochainComplex
      (ModuleCat.{u} (structureStalkRing B S hS X (geometricPointMap g'.hom x'))) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) (a b : ℤ) :
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (structureStalkRing B S hS X (geometricPointMap g'.hom x')))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (structureStalkRing B S hS Y
      (geometricPointMap f.hom (geometricPointMap g'.hom x'))))
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (structureStalkRing B S hS Y' (geometricPointMap f'.hom x')))
    HasTorAmplitudeCanonical
      (structureStalkRing B S hS Y (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ((ModuleCat.restrictScalars
          (smallEtaleStalkPullbackRingMap B S hS f
            (geometricPointMap g'.hom x'))).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)) a b →
    HasTorAmplitudeCanonical (structureStalkRing B S hS Y' (geometricPointMap f'.hom x'))
      (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars
              (smallEtaleStalkPullbackRingMap B S hS f' x')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars
              (smallEtaleStalkPullbackRingMap B S hS g' x')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K))) a b := by
  intro hamp
  let R := structureStalkRing B S hS Y (geometricPointMap f.hom (geometricPointMap g'.hom x'))
  let A := structureStalkRing B S hS X (geometricPointMap g'.hom x')
  let B' := structureStalkRing B S hS Y' (geometricPointMap f'.hom x')
  let C := structureStalkRing B S hS X' x'
  have hφ := cartesian_stalkRing_tensor_flat B S hS g' f' f h hpb x'
  let : Algebra R A :=
    (smallEtaleStalkPullbackRingMap B S hS f (geometricPointMap g'.hom x')).toAlgebra
  let : Algebra R B' :=
    ((smallEtaleStalkPullbackRingMap B S hS h (geometricPointMap f'.hom x')).comp
      (eqToHom (congrArg (structureStalkRing B S hS Y)
        (geometricPointMap_comm B S hS hpb.w x'))).hom).toAlgebra
  obtain ⟨φ, hleft, hright, hflat⟩ := hφ
  let T := A ⊗[R] B'
  let : Algebra B' T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R B' T := Algebra.TensorProduct.right_isScalarTower
  let : Algebra.IsPushout R A B' T := TensorProduct.isPushout
  let : Algebra T C := φ.toAlgebra
  let : Algebra A C := (smallEtaleStalkPullbackRingMap B S hS g' x').toAlgebra
  let : Algebra B' C := (smallEtaleStalkPullbackRingMap B S hS f' x').toAlgebra
  let : IsScalarTower A T C := IsScalarTower.of_algebraMap_eq' hleft.symm
  let : IsScalarTower B' T C := IsScalarTower.of_algebraMap_eq' hright.symm
  let : Module.Flat T C := RingHom.flat_algebraMap_iff.mp hflat
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp
    (flat_smallEtaleStalkPullbackRingMap B S hS f hf (geometricPointMap g'.hom x'))
  exact hasTorAmplitudeCanonical_torIndependent_flatBaseChange (T := T) (C := C)
    (RingTheory.TorIndependence.torIndependent_of_flat_left) K hK a b hamp

end AlgebraicGeometry.Space

end
