module

public import StacksFrontier.Homology.Devissage.DerivedHomCoproductsLargeUniverse
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityBundlePerfect
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensorRingEquivIso

/-!
# Stacks 0BZE in the derived change-of-rings shape, at an arbitrary module universe

`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect` proves Stacks 0BZE in the
derived change-of-rings shape of Stacks 06Y6 for modules in the universe of the rings themselves,
which is the generality of the differential graded chapter (Tag 09JJ). This file carries it to a
module universe `max v u` independent of the ring universe `u`, by renaming the rings along
`ULift.ringEquiv`: for `R : Type u` the ring `ULift.{max v u} R` lives in the universe of its own
modules, and `ModuleCat.{max v u} R ≌ ModuleCat.{max v u} (ULift.{max v u} R)` is restriction of
scalars along that isomorphism.

Three functors have to be carried across that equivalence: derived coextension of scalars, derived
extension of scalars, and the derived change-of-rings tensor product.
`StacksDraft.DerivedRingEquivIso.derivedHomRingEquivIso` and
`StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIso` do the first two, and
`StacksFrontier/RingTheory/Dualizing/UpperShriek/DerivedTensorRingEquivIso.lean` reduces the third
to one functor over a single ring, its hypothesis `hG`. That hypothesis is proved here.

## Main results

* `StacksDraft.DerivedRingEquivIso.derivedTensorRingEquivIsoG` — derived tensor product over a
  ring, carried along a ring isomorphism of that ring. This is the hypothesis `hG` of
  `StacksDraft.DerivedRingEquivIso.derivedTensorBundleRingEquivIso`.
* `StacksDraft.DerivedRingEquivIso.derivedTensorBundleRingEquivIsoOfFactorIso` — the derived
  change-of-rings tensor product of a bundle, carried along ring isomorphisms of the source and
  the target whenever the two tensor factors correspond.
* `Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect_anyModuleUniverse` —
  **Stacks 0BZE in the shape of Tag 06Y6, at an arbitrary module universe.**
* `CochainComplex.DerivedTensor.canonicalDerivedTensorUniverseIso` — the canonical bundle read
  with either of the two universe annotations that give the module universe `max v u` has the same
  derived tensor functor.

## Implementation notes

*How `hG` is proved.* What is asked for is an isomorphism `E ⋙ (- ⊗ᴸ_{C'} N') ≅ (- ⊗ᴸ_C N) ⋙ E`
for the scalar equivalence `E` attached to `e : C' ≃+* C`. Its ordinary-level shadow — a
comparison of `CochainComplex.tensorRightLarge` over `C` with the one over `C'` across the
equivalence of module categories — is not needed, because a change-of-rings bundle already carries
it. Take the canonical bundle `S` of Stacks 06Y6 for the ring homomorphism `e.symm : C → C'` with
tensor factor `N'`. Its field `directTensorUnderlying` says that `S.directTensor`, followed by
restriction of scalars back along `e.symm`, is ordinary tensoring with `N` over `C`; restriction
along a ring isomorphism is an equivalence, so `S.directTensor` *is* tensoring with `N` over `C`
followed by the equivalence. Hence `S.F` and `(- ⊗ᴸ_C N) ⋙ E` are total left derived functors of
one ordinary functor — postcomposition with `E` preserves the universal property because `E`, being
an equivalence, is a right adjoint — and uniqueness of left derived functors identifies them.
On the other side `S.F ≅ S.B ⋙ S.G` is the field `changeOfRings`, `S.B ≅ E` because both are left
adjoint to derived restriction of scalars along `e.symm`, and `S.G ≅ (- ⊗ᴸ_{C'} N')` by uniqueness
again. Nothing about signed differentials or totalization enters.

*The perfectness hypothesis.* Stacks 0BZE assumes `A` perfect as an `R`-module, tested in
`D(ModuleCat.{u} R)`. The renamed statement needs `ULift.{max v u} A` perfect over
`ULift.{max v u} R`, tested in `D(ModuleCat.{max v u} (ULift.{max v u} R))`. That is two steps:
`StacksDraft.Perfect.isPerfectModule_ulift` raises the module universe, and
`StacksDraft.Perfect.isPerfect_restrictScalars_ringEquiv` renames the scalars.

*The tensor factor.* The statement is at an arbitrary complex `L` of `A`-modules whose class in
`D(A)` is `RHom_R(A, R)`, with `R` read as the free module of rank one on the lifted carrier —
the tensor unit of `ModuleCat.liftedModuleMonoidalStruct`. The complex used on the renamed side
is the image of `L` under the scalar equivalence, so the two tensor factors correspond by the unit
of that equivalence and no choice of representative is made.

## References

* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex CochainComplex.DerivedTensor
open Dualizing

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace CochainComplex.DerivedTensor

/-- **The two universe annotations of the canonical derived change-of-rings tensor product agree.**
For `R A : Type u` and a complex `N` of `A`-modules in the universe `max v u`, the canonical bundle
of Stacks 06Y6 can be read with its own universe parameter either `v` or `max v u`; the module
universe is `max v u` either way, but the two readings are two applications of
`CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings` and so two choices of bundle.
Their derived tensor functors agree, because the ordinary functors they are left derived from are
the same and a total left derived functor is unique. -/
def canonicalDerivedTensorUniverseIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (N : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    (canonicalDerivedTensorChangeOfRings.{u, u, v} f N).F ≅
      (canonicalDerivedTensorChangeOfRings.{u, u, max v u} f N).F := by
  let Tsmall := canonicalDerivedTensorChangeOfRings.{u, u, v} f N
  let Tlarge := canonicalDerivedTensorChangeOfRings.{u, u, max v u} f N
  let W := HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)
  letI : MonoidalCategoryStruct (ModuleCat.{max v u} A) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  letI : MonoidalCategory (ModuleCat.{max v u} A) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  let eDirect : Tsmall.directTensor ≅ Tlarge.directTensor :=
    Tsmall.directTensorComparison ≪≫ Tlarge.directTensorComparison.symm
  exact Functor.leftDerivedNatIso Tsmall.F Tlarge.F Tsmall.alphaF Tlarge.alphaF
    (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight eDirect DerivedCategory.Q)

end CochainComplex.DerivedTensor

namespace StacksDraft.DerivedRingEquivIso

section Tensor

variable {C : Type u} [CommRing C] {C' : Type (max v u)} [CommRing C']

/-- **Derived tensor product over a ring, carried along a ring isomorphism of that ring.** Let
`eC : C' ≃+* C` be an isomorphism, let `N` be a complex of `C`-modules and `N'` a complex of
`C'`-modules restricting to `N`, and let `G` and `G'` be total left derived functors of ordinary
tensoring with `N` over `C` and with `N'` over `C'`. Then `G` and `G'` agree across the
equivalence of derived categories induced by `eC`.

This is the hypothesis `hG` of
`StacksDraft.DerivedRingEquivIso.derivedTensorBundleRingEquivIso`, proved. The route is through the
canonical change-of-rings bundle of Stacks 06Y6 along `eC.symm`, whose field
`directTensorUnderlying` supplies the comparison of ordinary tensor products that the two sides
need; this module's documentation says how. -/
def derivedTensorRingEquivIsoG (eC : C' ≃+* C)
    (N : CochainComplex (ModuleCat.{max v u} C) ℤ)
    (N' : CochainComplex (ModuleCat.{max v u} C') ℤ)
    (eN : (CochainComplex.restrictScalarsLarge.{0, u, max v u} eC.symm.toRingHom).obj N' ≅ N)
    (G : DerivedCategory (ModuleCat.{max v u} C) ⥤ DerivedCategory (ModuleCat.{max v u} C))
    (alphaG : DerivedCategory.Q ⋙ G ⟶
      CochainComplex.tensorRightLarge.{u, max v u} N ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor alphaG
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} C) (ComplexShape.up ℤ))]
    (G' : DerivedCategory (ModuleCat.{max v u} C') ⥤ DerivedCategory (ModuleCat.{max v u} C'))
    (alphaG' : DerivedCategory.Q ⋙ G' ⟶
      CochainComplex.tensorRightLarge.{max v u, max v u} N' ⋙ DerivedCategory.Q)
    [G'.IsLeftDerivedFunctor alphaG'
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} C') (ComplexShape.up ℤ))] :
    letI EC := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC)
    EC.functor ⋙ G' ≅ G ⋙ EC.functor := by
  letI : MonoidalCategoryStruct (ModuleCat.{max v u} C) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, max v u}
  letI : MonoidalCategory (ModuleCat.{max v u} C) :=
    ModuleCat.liftedModuleMonoidal.{u, max v u}
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC
  let EC := mapDerivedCategoryEquivalenceOfEquivalence E
  let ec := E.mapHomologicalComplex (ComplexShape.up ℤ)
  let S := canonicalDerivedTensorChangeOfRings.{u, max v u, 0} eC.symm.toRingHom N'
  let W_C := HomologicalComplex.quasiIso (ModuleCat.{max v u} C) (ComplexShape.up ℤ)
  let W_C' := HomologicalComplex.quasiIso (ModuleCat.{max v u} C') (ComplexShape.up ℤ)
  -- The bundle's derived extension of scalars is the scalar equivalence: both are left adjoint
  -- to derived restriction of scalars along `eC.symm`.
  haveI : S.B.IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ S.B ⟶
        (ModuleCat.extendScalars.{u, max v u, max v u}
          eC.symm.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q from S.alphaB) W_C :=
    S.isLeftDerivedB
  let eB : S.B ≅ EC.functor :=
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, max v u, 0}
      eC.symm.toRingHom S.B
      (show DerivedCategory.Q ⋙ S.B ⟶
        (ModuleCat.extendScalars.{u, max v u, max v u}
          eC.symm.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q from S.alphaB)).leftAdjointUniq EC.toAdjunction
  -- The bundle's derived tensor product over `C'` is `G'`.
  let eG' : S.G ≅ G' := Functor.leftDerivedNatIso S.G G' S.alphaG alphaG' W_C' (Iso.refl _)
  -- The bundle's ordinary direct tensor functor, read through the equivalence, is ordinary
  -- tensoring with `N` over `C`.
  let tR := (curriedTensor (ModuleCat.{max v u} C)).map₂CochainComplex.flip
  let eDir : S.directTensor ≅ CochainComplex.tensorRightLarge.{u, max v u} N ⋙ ec.functor :=
    (Functor.rightUnitor S.directTensor).symm ≪≫
      Functor.isoWhiskerLeft S.directTensor ec.counitIso.symm ≪≫
      (Functor.associator S.directTensor ec.inverse ec.functor).symm ≪≫
      Functor.isoWhiskerRight (S.directTensorUnderlying ≪≫ tR.mapIso eN) ec.functor
  -- Postcomposition with the equivalence preserves the left derived universal property.
  haveI : EC.functor.IsRightAdjoint := EC.symm.toAdjunction.isRightAdjoint
  let beta : DerivedCategory.Q ⋙ (G ⋙ EC.functor) ⟶
      (CochainComplex.tensorRightLarge.{u, max v u} N ⋙ DerivedCategory.Q) ⋙ EC.functor :=
    (Functor.associator DerivedCategory.Q G EC.functor).inv ≫
      Functor.whiskerRight alphaG EC.functor
  let eTarget : S.directTensor ⋙ DerivedCategory.Q ≅
      (CochainComplex.tensorRightLarge.{u, max v u} N ⋙ DerivedCategory.Q) ⋙ EC.functor :=
    Functor.isoWhiskerRight eDir DerivedCategory.Q ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (CochainComplex.tensorRightLarge.{u, max v u} N)
        E.functor.mapDerivedCategoryFactors.symm ≪≫
      (Functor.associator _ _ _).symm
  let eF : S.F ≅ G ⋙ EC.functor :=
    Functor.leftDerivedNatIso S.F (G ⋙ EC.functor) S.alphaF beta W_C eTarget
  exact Functor.isoWhiskerRight eB.symm G' ≪≫ Functor.isoWhiskerLeft S.B eG'.symm ≪≫
    S.changeOfRings.symm ≪≫ eF

end Tensor

section Bundle

variable {B C : Type u} [CommRing B] [CommRing C]
  {B' C' : Type (max v u)} [CommRing B'] [CommRing C']

/-- **The derived change-of-rings tensor product of a bundle, carried along ring isomorphisms of
the source and the target.** The two tensor factors are required to correspond: `N'` restricts to
`N` along `eC.symm`.

This is `StacksDraft.DerivedRingEquivIso.derivedTensorBundleRingEquivIso` with its hypothesis `hG`
supplied by `StacksDraft.DerivedRingEquivIso.derivedTensorRingEquivIsoG`, and with the renamed
bundle taken at the universe annotation that
`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect` produces, namely the one
whose module universe and ring universe are spelled by the same parameter. -/
def derivedTensorBundleRingEquivIsoOfFactorIso (eB : B' ≃+* B) (eC : C' ≃+* C) (f : B →+* C)
    (N : CochainComplex (ModuleCat.{max v u} C) ℤ)
    (N' : CochainComplex (ModuleCat.{max v u} C') ℤ)
    (eN : (CochainComplex.restrictScalarsLarge.{0, u, max v u} eC.symm.toRingHom).obj N' ≅ N)
    (T : DerivedTensorChangeOfRings.{u, u, max v u} f N)
    (T' : DerivedTensorChangeOfRings.{max v u, max v u, max v u}
      (eC.symm.toRingHom.comp (f.comp eB.toRingHom)) N') :
    letI EB := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eB)
    letI EC := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC)
    EB.functor ⋙ T'.F ≅ T.F ⋙ EC.functor := by
  let f' := eC.symm.toRingHom.comp (f.comp eB.toRingHom)
  let EB := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eB)
  let EC := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC)
  haveI : T.B.IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ T.B ⟶
        (ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from T.alphaB)
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ)) :=
    T.isLeftDerivedB
  haveI : T'.B.IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ T'.B ⟶
        (ModuleCat.extendScalars.{max v u, max v u, max v u} f').mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from T'.alphaB)
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B') (ComplexShape.up ℤ)) :=
    T'.isLeftDerivedB
  let hB : EB.functor ⋙ T'.B ≅ T.B ⋙ EC.functor :=
    derivedExtensionRingEquivIso.{u, max v u} eB eC f T.B
      (show DerivedCategory.Q ⋙ T.B ⟶
        (ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from T.alphaB) T'.B
      (show DerivedCategory.Q ⋙ T'.B ⟶
        (ModuleCat.extendScalars.{max v u, max v u, max v u} f').mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from T'.alphaB)
  let hG : EC.functor ⋙ T'.G ≅ T.G ⋙ EC.functor :=
    derivedTensorRingEquivIsoG.{u, max v u} eC N N' eN T.G T.alphaG T'.G T'.alphaG
  exact Functor.isoWhiskerLeft EB.functor T'.changeOfRings ≪≫
    (Functor.associator EB.functor T'.B T'.G).symm ≪≫
    Functor.isoWhiskerRight hB T'.G ≪≫
    Functor.associator T.B EC.functor T'.G ≪≫
    Functor.isoWhiskerLeft T.B hG ≪≫
    (Functor.associator T.B T.G EC.functor).symm ≪≫
    Functor.isoWhiskerRight T.changeOfRings.symm EC.functor

end Bundle

end StacksDraft.DerivedRingEquivIso

namespace Dualizing

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Perfectness of `A` as an `R`-module, read for the lifted rings: `ULift.{max v u} A` is a
perfect `ULift.{max v u} R`-module. The module universe is raised by
`StacksDraft.Perfect.isPerfectModule_ulift` and the scalars are renamed by
`StacksDraft.Perfect.isPerfect_restrictScalars_ringEquiv`. -/
theorem isPerfectModule_ulift_ringEquiv (f : R →+* A)
    (hperf : letI := f.toAlgebra
      StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := R) A) :
    letI eR : ULift.{max v u} R ≃+* R := ULift.ringEquiv
    letI eA : ULift.{max v u} A ≃+* A := ULift.ringEquiv
    letI f' : ULift.{max v u} R →+* ULift.{max v u} A :=
      eA.symm.toRingHom.comp (f.comp eR.toRingHom)
    letI := f'.toAlgebra
    StacksDraft.Perfect.IsPerfectModule.{max v u, max v u, max v u + 1}
      (R := ULift.{max v u} R) (ULift.{max v u} A) := by
  let := f.toAlgebra
  let eR : ULift.{max v u} R ≃+* R := ULift.ringEquiv
  exact StacksDraft.Perfect.isPerfect_of_iso
    (((ModuleCat.restrictScalars.{max v u} eR.toRingHom).mapDerivedCategorySingleFunctor
      0).app (ModuleCat.of R (ULift.{max v u} A))).symm
    (StacksDraft.Perfect.isPerfect_restrictScalars_ringEquiv.{u, max v u, max v u} eR
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
        (ModuleCat.of R (ULift.{max v u} A)))
      (StacksDraft.Perfect.isPerfectModule_ulift.{u, max v u, u + 1, max v u + 1, u} A hperf))

/-- Cancelling an equivalence from the right of an isomorphism of functors. -/
private def cancelPostcompEquivalence {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟] [Category* ℰ]
    {X Y : 𝒞 ⥤ 𝒟} (E : 𝒟 ≌ ℰ) (e : X ⋙ E.functor ≅ Y ⋙ E.functor) : X ≅ Y :=
  (Functor.rightUnitor X).symm ≪≫ Functor.isoWhiskerLeft X E.unitIso ≪≫
    (Functor.associator X E.functor E.inverse).symm ≪≫
    Functor.isoWhiskerRight e E.inverse ≪≫
    Functor.associator Y E.functor E.inverse ≪≫
    Functor.isoWhiskerLeft Y E.unitIso.symm ≪≫ Functor.rightUnitor Y

/-- **Stacks 0BZE in the derived change-of-rings shape of Tag 06Y6, at an arbitrary module
universe.** Let `f : R → A` make `A` a perfect `R`-module and let `L` be a complex of `A`-modules,
in a universe `max v u` above the ring universe `u`, whose class in `D(A)` is the value
`RHom_R(A, R)` of derived coextension of scalars at the free module of rank one on the lifted
carrier. Then `RHom_R(A, -) : D(R) ⥤ D(A)` is the canonical derived change-of-rings tensor product
of Stacks 06Y6 with `L`.

This is `Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect` — which holds at
module universe equal to the ring universe, the generality of the differential graded chapter —
renamed along `ULift.ringEquiv`, where the module universe `max v u` *is* the ring universe. All
three functors involved are carried across that renaming: derived coextension of scalars by
`StacksDraft.DerivedRingEquivIso.derivedHomRingEquivIso`, and derived extension of scalars together
with the derived change-of-rings tensor product by
`StacksDraft.DerivedRingEquivIso.derivedTensorBundleRingEquivIsoOfFactorIso`. The perfectness
hypothesis is the one Stacks 0BZE itself assumes, read for the lifted rings by
`Dualizing.isPerfectModule_ulift_ringEquiv`. -/
@[stacks 0BZE "in the derived change-of-rings shape of Tag 06Y6, at an arbitrary module universe \
above the ring universe, with no carried hypothesis"]
theorem nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect_anyModuleUniverse (f : R →+* A)
    (hperf : letI := f.toAlgebra
      StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := R) A)
    (L : CochainComplex (ModuleCat.{max v u} A) ℤ)
    (hL : Nonempty (DerivedCategory.Q.obj L ≅
      (Dualizing.derivedHom.{u, v} f).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{max v u} R))))) :
    Nonempty (Dualizing.derivedHom.{u, v} f ≅
      (canonicalDerivedTensorChangeOfRings.{u, u, max v u} f L).F) := by
  let eR : ULift.{max v u} R ≃+* R := ULift.ringEquiv
  let eA : ULift.{max v u} A ≃+* A := ULift.ringEquiv
  let f' : ULift.{max v u} R →+* ULift.{max v u} A :=
    eA.symm.toRingHom.comp (f.comp eR.toRingHom)
  let ER := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eR)
  let eqA := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eA
  let EA := mapDerivedCategoryEquivalenceOfEquivalence eqA
  let ecA := eqA.mapHomologicalComplex (ComplexShape.up ℤ)
  let L' := ecA.functor.obj L
  let U := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
    (ModuleCat.of R (ULift.{max v u} R))
  -- Derived coextension of scalars, carried across the renaming.
  let eH := StacksDraft.DerivedRingEquivIso.derivedHomRingEquivIso.{u, max v u} eR eA f
  -- The class of the renamed tensor factor is `RHom_{R'}(A', R')`.
  have hL' : Nonempty (DerivedCategory.Q.obj L' ≅
      (Dualizing.derivedHom.{max v u, max v u} f').obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} (ULift.{max v u} R)) 0).obj
          (ModuleCat.of (ULift.{max v u} R) (ULift.{max v u} R)))) :=
    hL.map fun hl => ((ModuleCat.restrictScalars.{max v u}
          eA.toRingHom).mapDerivedCategoryFactors.app L).symm ≪≫
      EA.functor.mapIso hl ≪≫ (eH.app U).symm ≪≫
      (Dualizing.derivedHom.{max v u, max v u} f').mapIso
        (((ModuleCat.restrictScalars.{max v u}
          eR.toRingHom).mapDerivedCategorySingleFunctor 0).app
            (ModuleCat.of R (ULift.{max v u} R)))
  -- Stacks 0BZE for the lifted rings, where the module universe is the ring universe.
  obtain ⟨e'⟩ := Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect.{max v u}
    f' (isPerfectModule_ulift_ringEquiv.{u, v} f hperf) L' hL'
  -- Derived extension of scalars and the derived tensor product, carried across the renaming.
  exact ⟨cancelPostcompEquivalence EA (eH.symm ≪≫ Functor.isoWhiskerLeft ER.functor e' ≪≫
    StacksDraft.DerivedRingEquivIso.derivedTensorBundleRingEquivIsoOfFactorIso.{u, max v u}
      eR eA f L L' (ecA.unitIso.app L).symm
      (canonicalDerivedTensorChangeOfRings.{u, u, max v u} f L)
      (canonicalDerivedTensorChangeOfRings.{max v u, max v u, max v u} f' L'))⟩

end Dualizing

end
