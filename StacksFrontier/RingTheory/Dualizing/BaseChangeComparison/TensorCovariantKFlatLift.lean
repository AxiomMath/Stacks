module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsTransposeLocalization
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsComponent
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeCanonicalValue

/-!
# The slots of [stacks 0E1W] at the K-flat descriptions of `L` and of `F (K ⊗ᴸ_R L)`

`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q`
computes the component of the change-of-rings isomorphism of [stacks 0E1W] at a pair of
`D(R)ᵒᵖ × D(A)`, relative to isomorphisms `eX`, `eY`, `e₁`, `e₂`, `e₃` identifying objects of
the derived categories of `ULift R`- and `ULift A`-modules with classes of cochain complexes.
This file supplies these witnesses at the pair `(Q L, F (Q K ⊗ᴸ_R Q L))` for K-flat complexes `K`
and `L`, through their K-flat descriptions:

* `F (Q K ⊗ᴸ_R Q L)` is the class of the complex `A ⊗_R (K ⊗_R L)`, by
  `CochainComplex.DerivedTensor.derivedTensor_comparison` and the comparison of the model `F`,
  which is invertible at the K-flat complex `K ⊗_R L`;
* the functor of `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` is derived
  restriction of scalars along `ULift.ringEquiv`, so it carries the class of a cochain complex to
  the class of its restriction, and it preserves K-flatness;
* the covariant witness is completed by a K-injective resolution of the resulting complex of
  `ULift A`-modules.

## Main definitions

* `Stacks.DerivedHom.BaseChange.scalarLiftQObjIso` — the scalar lift of the class of a cochain
  complex of `B`-modules is the class of its restriction of scalars along `ULift.ringEquiv`.
* `Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso` — the K-flat description of
  `F (Q K ⊗ᴸ_R Q L)` as the class of the degreewise extension of scalars of the total tensor
  complex `K ⊗_R L`.
* `Stacks.DerivedHom.BaseChange.tensorKFlatComparisonLiftIso` — the scalar lift of
  `F (Q K ⊗ᴸ_R Q L)` as the class of a cochain complex of `ULift A`-modules.
* `Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift` — the isomorphism of the scalar lift
  of `F (Q K ⊗ᴸ_R Q L)` with the class of a K-injective complex of `ULift A`-modules, factoring
  through the K-flat description.

## Main results

* `Stacks.DerivedHom.BaseChange.kFlat_scalarLift` — K-flatness survives the scalar lift.
* `Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso_hom` — the K-flat description is `F`
  applied to `CochainComplex.DerivedTensor.derivedTensor_comparison` followed by the model
  comparison.
* `Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift_hom` — the value of
  `tensorKFlatKInjectiveLift`: the scalar lift of that composite, followed by the localization
  comparison of the scalar lift and the resolution.
* `Stacks.DerivedHom.BaseChange.exists_tensorKFlatKInjectiveLift` — such an isomorphism exists
  for every K-flat pair.
* `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso_hom_scalarLift` — the
  representative model comparison of [stacks 0E1W] at the scalar lift of `L` is the localized
  change-of-rings map of Hom complexes.
* `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_tensorKFlat` — the
  component of [stacks 0E1W] at `(Q L, F (Q K ⊗ᴸ_R Q L))`, with the contravariant variable
  presented by the scalar lift of `L` and the covariant one by `tensorKFlatKInjectiveLift`.

## Implementation notes

The K-injective resolution is a hypothesis of
`Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift` rather than an existential, matching the
convention of `Stacks.DerivedHom.BaseChange.kFlatKInjectiveJoin`.
`Stacks.DerivedHom.BaseChange.kFlatKInjectiveJoin` itself does not apply: it is stated for two
rings of one universe, whereas here the rings live in `uR` and `uA` with modules at
`max uR uA uM`.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 090Y](https://stacks.math.columbia.edu/tag/090Y)
* [Stacks Project, Tag 0795](https://stacks.math.columbia.edu/tag/0795)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

section ScalarLift

universe u v

/-- **The scalar lift of the class of a cochain complex.**  The functor of
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` is derived restriction of
scalars along the ring isomorphism `ULift B ≃+* B`, so it carries the class of a cochain complex
of `B`-modules to the class of its degreewise restriction. -/
noncomputable def scalarLiftQObjIso (B : Type u) [CommRing B]
    (X : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u,
          v} B).functor.obj (DerivedCategory.Q.obj X) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{max u v}
          (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) :=
  (ModuleCat.restrictScalars.{max u v}
    (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapDerivedCategoryFactors.app X

/-- **K-flatness survives the scalar lift.**  The complex of `ULift B`-modules carrying the scalar
lift of the class of a K-flat complex is again K-flat, in the sense of `CochainComplex.KFlat`. -/
theorem kFlat_scalarLift (B : Type u) [CommRing B]
    (X : CochainComplex (ModuleCat.{max u v} B) ℤ) (hX : IsKFlat.{u, v} X) :
    CochainComplex.KFlat.{max u v, max u v}
      (((ModuleCat.restrictScalars.{max u v}
        (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X) := by
  have h := isKFlat_restrictScalars_of_ringEquiv (ULift.ringEquiv : ULift.{v} B ≃+* B) X hX
  exact (isKFlat_iff_kFlat.{max u v, max u v} _).mp (fun M hM => h M hM)

end ScalarLift

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

variable (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

set_option linter.checkUnivs false in
/-- The total tensor complex of two K-flat complexes is K-flat, in the sense of
`CochainComplex.KFlat`. -/
theorem kFlat_tensorComplex (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    CochainComplex.KFlat.{uR, max uM uA} (tensorComplex.{uR, max uR uA uM} K L) :=
  (isKFlat_iff_kFlat.{uR, max uR uA uM} _).mp (isKFlat_tensor.{uR, max uR uA uM} K L hK hL)

include hF in
/-- **The K-flat description of `F (Q K ⊗ᴸ_R Q L)`.**  For `K`, `L` K-flat the [stacks 0A63]
derived tensor product of their classes is the class of the total tensor complex `K ⊗_R L`, and
`F (Q K ⊗ᴸ_R Q L)` is the class of the complex `A ⊗_R (K ⊗_R L)`. -/
noncomputable def tensorKFlatComparisonIso (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    F.obj ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
        (tensorComplex.{uR, max uR uA uM} K L)) :=
  F.mapIso (derivedTensor_comparison.{uR, max uR uA uM} R K L hL) ≪≫
    @asIso _ _ _ _ (comparison.app (tensorComplex.{uR, max uR uA uM} K L))
      (CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat f F comparison _
        (kFlat_tensorComplex.{uR, uA, uM} K L hK hL))

include hF in
/-- The K-flat description of `F (Q K ⊗ᴸ_R Q L)` is `F` applied to
`CochainComplex.DerivedTensor.derivedTensor_comparison`, followed by the model comparison. -/
@[simp]
theorem tensorKFlatComparisonIso_hom (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    (tensorKFlatComparisonIso.{uR, uA, uM} f F comparison K L hK hL).hom =
      F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom ≫
        comparison.app (tensorComplex.{uR, max uR uA uM} K L) :=
  rfl

include hF in
/-- **The K-flat description of `F (Q K ⊗ᴸ_R Q L)`, transported into the scalar-lift world.**  The
scalar lift of `F (Q K ⊗ᴸ_R Q L)` is the class of the cochain complex of `ULift A`-modules
obtained from `A ⊗_R (K ⊗_R L)` by restricting scalars along `ULift A ≃+* A`. -/
noncomputable def tensorKFlatComparisonLiftIso
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
          max uR uA uM} A).functor.obj
        (F.obj ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
            (tensorComplex.{uR, max uR uA uM} K L))) :=
  (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
        max uR uA uM} A).functor.mapIso
      (tensorKFlatComparisonIso.{uR, uA, uM} f F comparison K L hK hL) ≪≫
    scalarLiftQObjIso.{uA, max uR uA uM} A
      ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
        (tensorComplex.{uR, max uR uA uM} K L))

include hF in
/-- **The scalar lift of `F (Q K ⊗ᴸ_R Q L)` as the class of a K-injective complex.** For K-flat
`K`, `L` and a K-injective resolution `n` of the complex of `ULift A`-modules underlying
`Stacks.DerivedHom.BaseChange.tensorKFlatComparisonLiftIso`, the isomorphism of the scalar lift
of `F (Q K ⊗ᴸ_R Q L)` with the class of the target of `n`. -/
noncomputable def tensorKFlatKInjectiveLift
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L)
    (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) [J.IsKInjective]
    (n : ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
            (tensorComplex.{uR, max uR uA uM} K L)) ⟶ J) [QuasiIso n] :
    (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
          max uR uA uM} A).functor.obj
        (F.obj ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))) ≅
      DerivedCategory.Q.obj J :=
  tensorKFlatComparisonLiftIso.{uR, uA, uM} f F comparison K L hK hL ≪≫
    asIso (DerivedCategory.Q.map n)

include hF in
/-- The value of `Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift`: the scalar lift of the
K-flat description, followed by the localization comparison of the scalar lift and the class of
the resolution. -/
@[simp]
theorem tensorKFlatKInjectiveLift_hom (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L)
    (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) [J.IsKInjective]
    (n : ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
            (tensorComplex.{uR, max uR uA uM} K L)) ⟶ J) [QuasiIso n] :
    (tensorKFlatKInjectiveLift.{uR, uA, uM} f F comparison K L hK hL J n).hom =
      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
            max uR uA uM} A).functor.map
          (F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom ≫
            comparison.app (tensorComplex.{uR, max uR uA uM} K L)) ≫
        (scalarLiftQObjIso.{uA, max uR uA uM} A ((extensionOfScalarsCochain.{uR, uA,
          max uR uA uM} f).obj (tensorComplex.{uR, max uR uA uM} K L))).hom ≫
          DerivedCategory.Q.map n :=
  Category.assoc _ _ _

include hF in
/-- **The scalar lift of `F (Q K ⊗ᴸ_R Q L)` is the class of a K-injective complex** of
`ULift A`-modules, for every K-flat pair `K`, `L`. -/
theorem exists_tensorKFlatKInjectiveLift (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    ∃ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (_ : J.IsKInjective),
      Nonempty ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
            max uR uA uM} A).functor.obj
          (F.obj ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.obj
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))) ≅
        DerivedCategory.Q.obj J) := by
  obtain ⟨J, n, hn, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective
    (((ModuleCat.restrictScalars.{max uR uA uM}
      (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
          (tensorComplex.{uR, max uR uA uM} K L)))
  have := hn
  have := hJ
  exact ⟨J, hJ, ⟨tensorKFlatKInjectiveLift.{uR, uA, uM} f F comparison K L hK hL J n⟩⟩

/-- **The representative model comparison of [stacks 0E1W] at the scalar lift of a K-flat
complex is chain-level.** The model comparison
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` at the scalar lift of `L` is the
localized change-of-rings map of Hom complexes, conjugated by the two representations. -/
theorem derivedHomChangeOfRingsModelIso_hom_scalarLift
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hL : IsKFlat.{uR, max uR uA uM} L) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q],
    letI : IsIso (T.alphaB.app K₀) :=
      isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB K₀
        (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    letI := quasiIso_homComplexChangeOfRingsMap_of_kFlat f' K₀ J I q T.B T.alphaB
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    (derivedHomChangeOfRingsModelIso f' T.B T.alphaB K₀ J I q
          (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom =
      (homModelIso K₀ I (Iso.refl _)
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app J ≪≫
            @asIso _ _ _ _ (DerivedCategory.Q.map q)
              ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).hom ≫
        inv (DerivedCategory.Q.map (homComplexChangeOfRingsMap f' K₀ J I q)) ≫
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app
              (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
                ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                  max uR uA uM} f').obj K₀) J)).inv ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.map
              (homModelIso ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                  max uR uA uM} f').obj K₀) J
                (asIso (T.alphaB.app K₀)) (Iso.refl _)).inv := by
  intro f' T K₀ J I hJ hI q hq
  have := hJ
  have := hI
  have := hq
  exact _root_.Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_homComplex
    f' T.B T.alphaB K₀ J I q (kFlat_scalarLift.{uR, max uR uA uM} R L hL)

/-- **The component of [stacks 0E1W] at `(Q L, F (Q K ⊗ᴸ_R Q L))` for K-flat `K` and `L`, with
both variables given by their K-flat descriptions.** This is
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q` with the
contravariant witness the scalar lift of `L` and the covariant witness
`Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift`; the remaining witnesses `X₁`, `X₂`,
`e₁`, `e₂`, `I`, `q` are hypotheses. -/
theorem derivedHomRestrictScalarsNatIso_hom_app_tensorKFlat
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L),
    let a :=
      CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
        f F comparison
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uA
      uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max uR uA
      uM} A
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    let M := F.obj ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))
    let X₃ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
            (tensorComplex.{uR, max uR uA uM} K L))
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L
    ∀ (X₁ X₂ : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (e₁ : HA.obj (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
        S.functor.obj M) ≅ DerivedCategory.Q.obj X₁)
      (e₂ : T.B.obj (E.functor.obj (DerivedCategory.Q.obj L)) ≅ DerivedCategory.Q.obj X₂)
      (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q]
      (n : X₃ ⟶ J) [QuasiIso n],
    let e₃ := tensorKFlatComparisonLiftIso.{uR, uA, uM} f F comparison K L hK hL
    let eX := scalarLiftQObjIso.{uR, max uR uA uM} R L
    let eY := tensorKFlatKInjectiveLift.{uR, uA, uM} f F comparison K L hK hL J n
    (derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).hom.app
        (Opposite.op (DerivedCategory.Q.obj L), M) =
      E.inverse.map (HR.map (CategoryTheory.Prod.mkHom
          (𝟙 (Opposite.op (E.functor.obj (DerivedCategory.Q.obj L))))
          (E.functor.map (U.map (S.unitIso.hom.app M) ≫ U.map (S.inverse.map e₃.hom) ≫
              δ.hom.app (DerivedCategory.Q.obj X₃) ≫ E.inverse.map (V.map e₃.inv)) ≫
            E.counitIso.hom.app (V.obj (S.functor.obj M))))) ≫
        E.inverse.map ((homRestrictSource f').map
              (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
            (derivedHomChangeOfRingsModelIso f' T.B T.alphaB K₀ J I q
              (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
              (homRestrictTarget f' T.B).map
                (CategoryTheory.Prod.mkHom eX.hom.op eY.inv)) ≫
          E.inverse.map (V.map (HA.map (CategoryTheory.Prod.mkHom
              (S.functor.map (F.map (E.toAdjunction.unit.app (DerivedCategory.Q.obj L) ≫
                    E.inverse.map (a'.unit.app (E.functor.obj (DerivedCategory.Q.obj L))))) ≫
                  S.functor.map (F.map ((V ⋙ E.inverse).map e₂.hom ≫
                      δ.inv.app (DerivedCategory.Q.obj X₂) ≫
                        (S.inverse ⋙ U).map e₂.inv)) ≫
                    S.functor.map
                        (a.counit.app (S.inverse.obj
                          (T.B.obj (E.functor.obj (DerivedCategory.Q.obj L))))) ≫
                      S.toAdjunction.counit.app
                        (T.B.obj (E.functor.obj (DerivedCategory.Q.obj L)))).op
              (𝟙 (S.functor.obj M))))) ≫
            (V ⋙ E.inverse).map e₁.hom ≫
              δ.inv.app (DerivedCategory.Q.obj X₁) ≫ (S.inverse ⋙ U).map e₁.inv := by
  intro F comparison hF K L hK hL a E S f' U V T a' δ HR HA M X₃ K₀
    X₁ X₂ e₁ e₂ J I hJ hI q hq n hn e₃ eX eY
  have := hF
  have := hJ
  have := hI
  have := hq
  have := hn
  exact derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q.{uR, uA, uM} f F comparison
    (Opposite.op (DerivedCategory.Q.obj L)) M X₁ X₂ X₃ e₁ e₂ e₃ K₀ J I q
    (kFlat_scalarLift.{uR, max uR uA uM} R L hL) eX eY

end Stacks.DerivedHom.BaseChange

end
