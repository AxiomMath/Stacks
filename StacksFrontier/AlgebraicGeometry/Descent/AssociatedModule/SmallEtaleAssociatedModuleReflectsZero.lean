module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleMonoidal
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePullbackExact
public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.Exactness

/-!
# The two presentations of `ε` are one, and `ε^*` detects zero objects

`ε = id_{small, étale, Zar} : S_étale → S_Zar` carries two presentations in this development:
`AlgebraicGeometry.SmallEtale.toZariskiRingedSiteHom`, a morphism of ringed sites at independent
universes, and `AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom`, a two-field
morphism of ringed topoi.  The first has an associated morphism of ringed topoi, and
`toRingedToposHom_toZariskiRingedSiteHom` below says it *is* the second, by `rfl`: both have the
adjoint pair `ε⁻¹ ⊣ ε_*` of `AlgebraicGeometry.SmallEtale.toZariskiMorphismOfTopoi` underneath,
and both read `AlgebraicGeometry.SmallEtale.commRingStructureMap` through the same
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`.

Zero detection, the assertion of Stacks 08H8, holds for the pullback along the abstract
morphism, as `AlgebraicGeometry.SmallEtale.isZero_of_isZero_toZariskiModulePullback`, with no
hypothesis, and for the associated-module functor of Stacks 03DU (4) for a quasi-coherent module,
as `AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule`.  The two functors are
isomorphic, so the first statement transports to the second functor without the quasi-coherence
hypothesis.

## Main definitions

* `AlgebraicGeometry.SmallEtale.associatedModuleIsoToZariskiModulePullback`: the pullback of
  sheaves of modules along the abstract morphism of ringed topoi of `ε` is the associated-module
  functor `𝓕 ↦ 𝓕^a`.

## Main results

* `AlgebraicGeometry.SmallEtale.toRingedToposHom_toZariskiRingedSiteHom`: the morphism of ringed
  topoi associated to `ε` as a morphism of ringed sites is `ε` as an abstract morphism of ringed
  topoi.
* `AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_zariskiModules`: if the
  associated module `𝓕^a` of an arbitrary `𝒪_S`-module `𝓕` is zero, then `𝓕` is zero.

## Implementation notes

`AlgebraicGeometry.SmallEtale.assocIso` of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSmallModelPullbackExact.lean`
states the same isomorphism `ε^* ≅ (𝓕 ↦ 𝓕^a)`.  It is built there from
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` at
`toZariskiRingedSiteHom`, and here from
`AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso`; both are one-line readings of a
comparison of the two left adjoints.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
* [Stacks Project, Tag 08WK](https://stacks.math.columbia.edu/tag/08WK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two presentations of `ε` -/

/-- **The two presentations of `ε = id_{small, étale, Zar} : S_étale → S_Zar` are one morphism of
ringed topoi.**  The morphism of ringed topoi associated to `ε` as a morphism of ringed sites at
independent universes is `ε` as an abstract two-field morphism of ringed topoi, on the nose. -/
public theorem toRingedToposHom_toZariskiRingedSiteHom :
    (toZariskiRingedSiteHom B S hS).toRingedToposHom =
      toZariskiAbstractRingedToposHom B S hS :=
  rfl

/-- **The pullback of sheaves of modules along the abstract morphism of ringed topoi of `ε` is
the associated-module functor `𝓕 ↦ 𝓕^a` of Stacks 03DU (4).**  This is
`AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso` read through
`toRingedToposHom_toZariskiRingedSiteHom`. -/
public def associatedModuleIsoToZariskiModulePullback :
    toZariskiModulePullback B S hS ≅ associatedModule B S hS :=
  pullbackModulesToZariskiIso B S hS

/-! ### Zero detection along `ε^*` -/

/-- **The zero-detection assertion of Stacks 08H8, for an arbitrary `𝒪_S`-module.**  If the
associated module `𝓕^a = ε^*𝓕` of Stacks 03DU (4) is a zero object, then so is `𝓕`. -/
public theorem isZero_of_isZero_associatedModule_zariskiModules (F : S.Modules)
    (h : IsZero ((associatedModule B S hS).obj F)) : IsZero F :=
  isZero_of_isZero_toZariskiModulePullback B S hS F
    (h.of_iso ((associatedModuleIsoToZariskiModulePullback B S hS).app F))

end AlgebraicGeometry.SmallEtale

end
