module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsTensorHomTranspose
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorCovariantKFlatLift

/-!
# The keystone's change-of-rings map as a [stacks 0A63] transpose

At the scalar lift `f' : ULift R →+* ULift A` of a ring map and the scalar lift `K₀` of a K-flat
complex `L`, the localization of the chain-level map
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f' K₀ J I q` is a composite of
[stacks 0A63] transposes and the K-flat and K-injective comparisons. This is
`StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsTensorHomTranspose`, stated for rings of one
universe, at the rings `ULift R` and `ULift A` of the universe `max uR uA uM`, with the
K-flatness of the Hom-source given by `Stacks.DerivedHom.BaseChange.kFlat_scalarLift`.

Substituted into `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso_hom_scalarLift`, it
removes the last factor of the `ν` side of the keystone that is not a unit, a counit, a
localization comparison or a K-flat description. The keystone equation `ν ≫ μ' = 𝟙` of
`Dualizing.tensorBaseChangeMor_eq_iff_section_comp` is not proved here.

## Main results

* `Stacks.DerivedHom.BaseChange.Q_map_homComplexChangeOfRingsMap_scalarLift`: the localized
  change-of-rings map at the keystone's data, as a [stacks 0A63] transpose.
* `Stacks.DerivedHom.BaseChange.inv_Q_map_homComplexChangeOfRingsMap_scalarLift`: the inverse of
  the localized change-of-rings map, followed by that transpose, is the inverse of the K-injective
  representation of derived internal Hom.
* `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso_hom_scalarLift_transpose`: the
  representative model comparison of [stacks 0E1W] at the keystone's contravariant complex, with
  no Hom-complex change-of-rings map left in its value.

## Implementation notes

The complex `J` is left arbitrary. In the keystone it is a K-injective resolution of the scalar
lift of `A ⊗_R (K ⊗_R L)`, supplied by
`Stacks.DerivedHom.BaseChange.exists_tensorKFlatKInjectiveLift`.

No `@[stacks]` attribute is placed here: this file only rewrites one factor of an open
obligation, and covers no tag.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.ExtendScalars

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

/-- **The keystone's change-of-rings map as a [stacks 0A63] transpose.** At the scalar lift `f'`
of `f` and the scalar lift `K₀` of a K-flat complex `L`, for any complex `J`, any K-injective `I`
and any `q`, the localization of `homComplexChangeOfRingsMap f' K₀ J I q` is the inverse
[stacks 0A63] transpose of the K-flat comparison followed by `Q W`, followed by the K-injective
Hom comparison. This is `Stacks.DerivedHom.BaseChangeIso.Q_map_homComplexChangeOfRingsMap_eq` at
these data. -/
theorem Q_map_homComplexChangeOfRingsMap_scalarLift
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hL : IsKFlat.{uR, max uR uA uM} L) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I),
    let adj := (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj K₀) J
    let P := (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
      f').obj Z
    let W := adj.homEquiv (P ⊗ K₀) J
        ((extendScalarsMonoidalIso f' P K₀).inv ≫
          DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q
    DerivedCategory.Q.map
          (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f' K₀ J I q) =
      (DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K₀)
            (DerivedCategory.Q.obj I)).symm
          (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
              (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
            DerivedCategory.Q.map W) ≫
        ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).homIso K₀ I).hom := by
  intro f' K₀ J I hI q adj Z P W
  exact Stacks.DerivedHom.BaseChangeIso.Q_map_homComplexChangeOfRingsMap_eq
    f' K₀ J I q (kFlat_scalarLift.{uR, max uR uA uM} R L hL)

/-- **The keystone's change-of-rings map, inverted, with the inverse eliminated.** At the data of
`Stacks.DerivedHom.BaseChange.Q_map_homComplexChangeOfRingsMap_scalarLift`, when the localization
of `homComplexChangeOfRingsMap f' K₀ J I q` is invertible, its inverse followed by the inverse
[stacks 0A63] transpose of the K-flat comparison followed by `Q W` is the inverse of the
K-injective Hom comparison. This is
`Stacks.DerivedHom.BaseChangeIso.inv_Q_map_homComplexChangeOfRingsMap_comp` at these data. -/
theorem inv_Q_map_homComplexChangeOfRingsMap_scalarLift
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hL : IsKFlat.{uR, max uR uA uM} L) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I)
      [IsIso (DerivedCategory.Q.map
        (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f' K₀ J I q))],
    let adj := (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj K₀) J
    let P := (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
      f').obj Z
    let W := adj.homEquiv (P ⊗ K₀) J
        ((extendScalarsMonoidalIso f' P K₀).inv ≫
          DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q
    inv (DerivedCategory.Q.map
            (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f' K₀ J I q)) ≫
        (DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K₀)
            (DerivedCategory.Q.obj I)).symm
          (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
              (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
            DerivedCategory.Q.map W) =
      ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).homIso K₀ I).inv := by
  intro f' K₀ J I hI q hiso adj Z P W
  exact Stacks.DerivedHom.BaseChangeIso.inv_Q_map_homComplexChangeOfRingsMap_comp
    f' K₀ J I q (kFlat_scalarLift.{uR, max uR uA uM} R L hL)

/-- **The representative model comparison of [stacks 0E1W] at the keystone's contravariant
complex, with no Hom-complex change-of-rings map left in it.** For K-injective `J` and `I` and a
quasi-isomorphism `q`, the hom of `derivedHomChangeOfRingsModelIso f' T.B T.alphaB K₀ J I q` is
the representation isomorphism `Stacks.DerivedHom.BaseChange.homModelIso` at `K₀` and `I`,
followed by the inverse of the K-injective Hom comparison, the inverse of the [stacks 0A63]
transpose of the K-flat comparison followed by `Q W`, the inverse of the comparison
`mapDerivedCategoryFactors` of restriction of scalars, and restriction of scalars applied to the
inverse of `homModelIso` at the extension of scalars of `K₀` and `J`. -/
theorem derivedHomChangeOfRingsModelIso_hom_scalarLift_transpose
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
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
    let adj := (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj K₀) J
    let P := (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
      f').obj Z
    let W := adj.homEquiv (P ⊗ K₀) J
        ((extendScalarsMonoidalIso f' P K₀).inv ≫
          DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q
    letI : IsIso ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
          (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
              (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
            DerivedCategory.Q.map W)) :=
      Stacks.DerivedHom.BaseChangeIso.isIso_homEquiv_symm_tensorIso f' K₀ J I q
        (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    (derivedHomChangeOfRingsModelIso f' T.B T.alphaB K₀ J I q
          (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom =
      (homModelIso K₀ I (Iso.refl _)
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app J ≪≫
            @asIso _ _ _ _ (DerivedCategory.Q.map q)
              ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).hom ≫
        ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).homIso K₀ I).inv ≫
          inv ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
              (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
                  (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
                DerivedCategory.Q.map W)) ≫
            ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app
                (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
                  ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                    max uR uA uM} f').obj K₀) J)).inv ≫
              (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.map
                (homModelIso ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                    max uR uA uM} f').obj K₀) J
                  (asIso (T.alphaB.app K₀)) (Iso.refl _)).inv := by
  intro f' T K₀ J I hJ hI q hq adj Z P W
  let := quasiIso_homComplexChangeOfRingsMap_of_kFlat f' K₀ J I q T.B T.alphaB
    (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
  let : IsIso ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
        (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
            (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
          DerivedCategory.Q.map W)) :=
    Stacks.DerivedHom.BaseChangeIso.isIso_homEquiv_symm_tensorIso f' K₀ J I q
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
  have hinv : inv (DerivedCategory.Q.map (homComplexChangeOfRingsMap f' K₀ J I q)) =
      ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).homIso K₀ I).inv ≫
        inv ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
            (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso P K₀
                (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
              DerivedCategory.Q.map W)) :=
    Stacks.DerivedHom.BaseChangeIso.inv_Q_map_homComplexChangeOfRingsMap_eq f' K₀ J I q
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
  refine (derivedHomChangeOfRingsModelIso_hom_scalarLift.{uR, uA, uM} f L hL J I q).trans ?_
  refine congrArg (fun z => (homModelIso K₀ I (Iso.refl _)
      ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app J ≪≫
        @asIso _ _ _ _ (DerivedCategory.Q.map q)
          ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).hom ≫ z) ?_
  rw [hinv, Category.assoc]

end Stacks.DerivedHom.BaseChange

end
