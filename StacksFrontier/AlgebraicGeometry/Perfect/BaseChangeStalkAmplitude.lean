module

public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalkCartesian
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude

/-!
# Tor amplitude at a stalk of a Tor-independent base change

This file joins the three ring-level ingredients of Stacks 0C0V into one statement about a
cartesian square of schemes, read at a single point of the upper-left corner:

* `AlgebraicGeometry.BaseChangeStalk.cartesian_stalk_tensor_flat` presents the local ring of
  the upper-left corner as a flat algebra over the tensor product of the other three;
* `AlgebraicGeometry.BaseChangeTorAmplitude.ringTorIndependent_of_schemeTorIndependent_stalks`
  turns Tor independence of the square into Tor independence of those local rings;
* `AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_torIndependent_flatBaseChange`
  is the transfer of canonical Tor amplitude across such a square of rings.

## Main results

* `AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_stalk_of_cartesian`: for a
  Tor-independent cartesian square of schemes, a point of the upper-left corner, and a K-flat
  complex of modules over the local ring upstairs on `X`, extension of scalars to the local
  ring of the upper-left corner preserves the canonical Tor amplitude read over the local ring
  of `S'`.

## Implementation notes

The statement is written entirely with the geometric stalk maps, so it carries no `Algebra`
instance in its binders; the algebra structures, scalar towers and the pushout datum the
ring-level transfer needs are installed inside the proof, where the two factorizations
`φ ∘ includeLeft = g'` and `φ ∘ includeRight = f'` supplied by
`cartesian_stalk_tensor_flat` are exactly the two `IsScalarTower` witnesses.

None of the four rings is named by a local `let`: the implicit arguments of the ring-level
transfer are pinned by the explicit arguments `K` and the Tor-independence hypothesis, whose
types use the written-out stalks, so instances stated at a `let`-bound name are not the ones
looked for.  The tensor product alone is a named `let`, because it is passed explicitly.
`Algebra.TensorProduct.rightAlgebra` is not a global instance, so it and the two instances
depending on it — `IsScalarTower R B T` and the pushout datum — are installed by hand.

What this does *not* yet state is part (1) of the tag: that conclusion is about the derived
pullback of a derived object on `X`, and reaching it from here needs the identification of the
stalk complex of a module pullback with this extension of scalars, which is
`Stacks.RingedSpace.stalkModulePullbackComplexIso`
(`StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback`) read through
`SemilinearStalk.commStalkRingEquiv`.

## References

* [Stacks Project, Tag 0C0V](https://stacks.math.columbia.edu/tag/0C0V)
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open StacksDraft.TorAmplitude
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.BaseChangeTorAmplitude

attribute [local instance] HasDerivedCategory.standard

/-- At a point of the upper-left corner of a Tor-independent cartesian square of schemes,
extension of scalars along the stalk map of `g'` carries canonical Tor amplitude over the local
ring of `S` to canonical Tor amplitude over the local ring of `S'`. -/
public theorem hasTorAmplitudeCanonical_stalk_of_cartesian
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hpb : IsPullback g' f' f g)
    (htor : AlgebraicGeometry.TorIndependent f g) (x' : X')
    (K : CochainComplex (ModuleCat.{u} (X.presheaf.stalk (g'.base x'))) ℤ)
    (hK : K.KFlat) (a b : ℤ)
    (hamp : HasTorAmplitudeCanonical (S.presheaf.stalk (f.base (g'.base x')))
      ((ModuleCat.restrictScalars (f.stalkMap (g'.base x')).hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)) a b) :
    HasTorAmplitudeCanonical (S'.presheaf.stalk (f'.base x'))
      (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (f'.stalkMap x').hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars (g'.stalkMap x').hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K))) a b := by
  have hxy : f.base (g'.base x') = g.base (f'.base x') :=
    congrArg (fun k : X' ⟶ S => k.base x') hpb.w
  let : Algebra (S.presheaf.stalk (f.base (g'.base x'))) (X.presheaf.stalk (g'.base x')) :=
    (f.stalkMap (g'.base x')).hom.toAlgebra
  let : Algebra (S.presheaf.stalk (f.base (g'.base x'))) (S'.presheaf.stalk (f'.base x')) :=
    (eqToHom (congrArg (fun z => S.presheaf.stalk z) hxy) ≫
      g.stalkMap (f'.base x')).hom.toAlgebra
  let T := TensorProduct (S.presheaf.stalk (f.base (g'.base x')))
    (X.presheaf.stalk (g'.base x')) (S'.presheaf.stalk (f'.base x'))
  let : Algebra (S'.presheaf.stalk (f'.base x')) T := Algebra.TensorProduct.rightAlgebra
  let : Algebra (S.presheaf.stalk (f.base (g'.base x'))) T := inferInstance
  let : Algebra (X.presheaf.stalk (g'.base x')) T := inferInstance
  let : IsScalarTower (S.presheaf.stalk (f.base (g'.base x')))
      (X.presheaf.stalk (g'.base x')) T := inferInstance
  let : IsScalarTower (S.presheaf.stalk (f.base (g'.base x')))
      (S'.presheaf.stalk (f'.base x')) T := Algebra.TensorProduct.right_isScalarTower
  let : Algebra.IsPushout (S.presheaf.stalk (f.base (g'.base x')))
      (X.presheaf.stalk (g'.base x')) (S'.presheaf.stalk (f'.base x')) T :=
    TensorProduct.isPushout
  obtain ⟨φ, hleft, hright, hflat⟩ :=
    AlgebraicGeometry.BaseChangeStalk.cartesian_stalk_tensor_flat g' f' f g hpb x'
  let : Algebra T (X'.presheaf.stalk x') := φ.toAlgebra
  let : Algebra (X.presheaf.stalk (g'.base x')) (X'.presheaf.stalk x') :=
    (g'.stalkMap x').hom.toAlgebra
  let : Algebra (S'.presheaf.stalk (f'.base x')) (X'.presheaf.stalk x') :=
    (f'.stalkMap x').hom.toAlgebra
  let : IsScalarTower (X.presheaf.stalk (g'.base x')) T (X'.presheaf.stalk x') :=
    IsScalarTower.of_algebraMap_eq' hleft.symm
  let : IsScalarTower (S'.presheaf.stalk (f'.base x')) T (X'.presheaf.stalk x') :=
    IsScalarTower.of_algebraMap_eq' hright.symm
  let : Module.Flat T (X'.presheaf.stalk x') := hflat
  exact hasTorAmplitudeCanonical_torIndependent_flatBaseChange
    (T := T) (C := X'.presheaf.stalk x')
    (ringTorIndependent_of_schemeTorIndependent_stalks htor (g'.base x') (f'.base x') hxy)
    K hK a b hamp

end AlgebraicGeometry.BaseChangeTorAmplitude
