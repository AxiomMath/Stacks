module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RingEquivIso

/-!
# Transporting the derived change-of-rings tensor product along ring isomorphisms

`StacksDraft.DerivedRingEquivIso` transports the functors attached to a ring homomorphism
`f : B → C` along ring isomorphisms `eB : B' ≃+* B` and `eC : C' ≃+* C` of its source and its
target: derived Hom by `StacksDraft.DerivedRingEquivIso.derivedHomRingEquivIso` and derived
extension of scalars by `StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIso`.  This file
reduces the same transport for the third functor of the chapter, the derived change-of-rings tensor
product `CochainComplex.DerivedTensor.DerivedTensorChangeOfRings`, to one functor over a single
ring.

A `DerivedTensorChangeOfRings` bundle has seventeen fields, three of them universal properties and
one of them the coherence identity normalizing the change-of-rings isomorphism by the three
counits.  Transporting it field by field is not necessary: the bundle carries its own
factorization `F ≅ B ⋙ G` as the field `changeOfRings`, and once both sides are read through that
factorization the transport of `F` needs only the transports of `B` and of `G` separately.

`StacksDraft.DerivedRingEquivIso.derivedTensorBundleExtensionIso` is the transport of `B`, and it
assumes nothing: a bundle's `B` is a total left derived functor of extension of scalars, which is
exactly what `StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIso` transports.
`StacksDraft.DerivedRingEquivIso.derivedTensorBundleRingEquivIso` assembles the two halves, taking
the transport of `G` as the hypothesis `hG`.  That hypothesis holds whenever the two tensor
factors correspond: it is `StacksDraft.DerivedRingEquivIso.derivedTensorRingEquivIsoG`.

## Main definitions

* `StacksDraft.DerivedRingEquivIso.derivedTensorBundleExtensionIso` — the derived extension of
  scalars of a change-of-rings bundle, transported along ring isomorphisms of the source and the
  target.
* `StacksDraft.DerivedRingEquivIso.derivedTensorBundleRingEquivIso` — the derived change-of-rings
  tensor product of a bundle, transported along ring isomorphisms of the source and the target,
  given the transport of the bundle's derived tensor product over the target ring.

## Implementation notes

The hypothesis `hG` is one functor rather than a bundle: derived tensor product over a *single*
ring, transported along a ring isomorphism of that ring.  It does not need the comparison one might
expect — one identifying `CochainComplex.tensorRightLarge` over `C` with
`CochainComplex.tensorRightLarge` over `C'` across the equivalence of module categories, for the
lifted monoidal structures `ModuleCat.liftedModuleMonoidalStruct`, a statement about the
totalization of the tensor bifunctor and its signed differentials.  A bundle already carries that
comparison as its field `directTensorUnderlying`, which says that the direct tensor functor,
followed by restriction of scalars back along the ring map, is ordinary tensoring over the source
ring.  Taking the bundle along the ring isomorphism itself and reading that field through the
equivalence proves `hG`; the argument is in the documentation of
`StacksFrontier.RingTheory.Dualizing.TrivialDualityBundlePerfectAnyModuleUniverse`.

*Why the transport.* Stacks 0BZU, in
`Dualizing.PolynomialPresentation.upperShriekFunctor_iso_derivedTensorProduct`, and Stacks 0BZH, in
`Dualizing.InvertibleKernel.derivedHomIsoDerivedTensorConormalInverseShift`, are
stated at an arbitrary module universe, whereas Stacks 0BZE is proved through the differential
graded chapter, which is stated at the ring's own module universe.  Passing from the ring universe
to an independent module universe is what `ULift.ringEquiv` does — for a ring `R : Type u` the
lifted ring `ULift.{max v u} R` has module universe equal to its ring universe, and
`ModuleCat.{max v u} R ≌ ModuleCat.{max v u} (ULift.{max v u} R)`.  Transporting Stacks 0BZE that
way needs derived Hom, derived extension of scalars and the derived change-of-rings tensor
product; the first two are in `StacksFrontier/RingTheory/Dualizing/UpperShriek/RingEquivIso.lean`,
and this file treats the third.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.DerivedTensor
open Dualizing

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace StacksDraft.DerivedRingEquivIso

variable {B C : Type u} [CommRing B] [CommRing C]
  {B' C' : Type (max v u)} [CommRing B'] [CommRing C']

/-- **Derived extension of scalars of a change-of-rings bundle, transported along ring
isomorphisms of the source and the target.** The field `B` of a
`CochainComplex.DerivedTensor.DerivedTensorChangeOfRings` bundle is a total left derived functor of
extension of scalars, normalized by the field `alphaB`, so
`StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIso` applies to it verbatim. Nothing is
assumed, and the tensor factors of the two bundles are unrelated: the field `B` does not see
them. -/
noncomputable def derivedTensorBundleExtensionIso
    (eB : B' ≃+* B) (eC : C' ≃+* C) (f : B →+* C)
    (N : CochainComplex (ModuleCat.{max v u} C) ℤ)
    (N' : CochainComplex (ModuleCat.{max v u} C') ℤ)
    (T : DerivedTensorChangeOfRings.{u, u, v} f N)
    (T' : DerivedTensorChangeOfRings.{max v u, max v u, 0}
      (eC.symm.toRingHom.comp (f.comp eB.toRingHom)) N') :
    let EB := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eB)
    let EC := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC)
    EB.functor ⋙ T'.B ≅ T.B ⋙ EC.functor := by
  -- The bundle spells the target of `alphaB` as `CochainComplex.extendScalarsLarge`, and
  -- `derivedExtensionRingEquivIso` spells it as the underlying `mapHomologicalComplex`; the two
  -- are definitionally equal, but instance search is syntactic, so each universal property is
  -- restated at the spelling the consumer uses.
  haveI : T.B.IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ T.B ⟶
        (ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from T.alphaB)
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ)) :=
    T.isLeftDerivedB
  haveI : T'.B.IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ T'.B ⟶
        (ModuleCat.extendScalars.{max v u, max v u, max v u}
          (eC.symm.toRingHom.comp (f.comp eB.toRingHom))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from T'.alphaB)
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B') (ComplexShape.up ℤ)) :=
    T'.isLeftDerivedB
  exact derivedExtensionRingEquivIso.{u, v} eB eC f T.B T.alphaB T'.B T'.alphaB

/-- **The derived change-of-rings tensor product of a bundle, transported along ring isomorphisms
of the source and the target**, given the corresponding transport `hG` of the bundle's derived
tensor product over the target ring.

The bundle's own field `changeOfRings` factors its derived change-of-rings tensor product as
derived extension of scalars followed by derived tensor product over the target ring. Reading both
bundles through that factorization leaves two transports: the one of derived extension of scalars,
which is `StacksDraft.DerivedRingEquivIso.derivedTensorBundleExtensionIso` and assumes nothing,
and `hG`. So a seventeen-field bundle transport is exactly one functor transport, over a single
ring, and that one is
`StacksDraft.DerivedRingEquivIso.derivedTensorRingEquivIsoG`. -/
noncomputable def derivedTensorBundleRingEquivIso
    (eB : B' ≃+* B) (eC : C' ≃+* C) (f : B →+* C)
    (N : CochainComplex (ModuleCat.{max v u} C) ℤ)
    (N' : CochainComplex (ModuleCat.{max v u} C') ℤ)
    (T : DerivedTensorChangeOfRings.{u, u, v} f N)
    (T' : DerivedTensorChangeOfRings.{max v u, max v u, 0}
      (eC.symm.toRingHom.comp (f.comp eB.toRingHom)) N')
    (hG : (mapDerivedCategoryEquivalenceOfEquivalence
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC)).functor ⋙
        T'.G ≅
      T.G ⋙ (mapDerivedCategoryEquivalenceOfEquivalence
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC)).functor) :
    let EB := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eB)
    let EC := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC)
    EB.functor ⋙ T'.F ≅ T.F ⋙ EC.functor := by
  intro EB EC
  exact Functor.isoWhiskerLeft EB.functor T'.changeOfRings ≪≫
    (Functor.associator EB.functor T'.B T'.G).symm ≪≫
    Functor.isoWhiskerRight (derivedTensorBundleExtensionIso.{u, v} eB eC f N N' T T') T'.G ≪≫
    Functor.associator T.B EC.functor T'.G ≪≫
    Functor.isoWhiskerLeft T.B hG ≪≫
    (Functor.associator T.B T.G EC.functor).symm ≪≫
    Functor.isoWhiskerRight T.changeOfRings.symm EC.functor

end StacksDraft.DerivedRingEquivIso

end
