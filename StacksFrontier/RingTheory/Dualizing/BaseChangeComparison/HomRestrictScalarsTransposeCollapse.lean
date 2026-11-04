module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsTransposeModel
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorCovariantKFlatLiftCollapse

/-!
# The uncurried inverse component of [stacks 0E1W] at the keystone's pair, fully collapsed

`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat` values
the [stacks 0A63] transpose `ψ` of the inverse component of [stacks 0E1W] at the keystone's pair
with its one content factor carried by the chain-level map
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` sitting *uncurried inside a
fixed-universe transpose*, followed by the K-injective Hom comparison.

`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat_q_map` collapses
those three factors into one, `DerivedCategory.Q.map` of the chain map.  Passing that through the
substitution hook
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_model_value`
gives `ψ`'s value with the chain map localized and nothing around it, which is what this file
records.

This is the side of the keystone's `hmu` that the [stacks 068I] candidate has to be compared with,
and the comparison is now between two localized chain maps: this one, and
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, the one the [stacks 068I] side carries by
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom`.

**What is not done here.**  No tag is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open, and in particular
the comparison identity `h` is untouched; its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_q_map`
  -- the uncurried inverse component of [stacks 0E1W] at the keystone's pair, with the chain-level
  map of [stacks 0E1W] localized and nothing around it.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public section

open CategoryTheory StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

/-- **The uncurried inverse component of [stacks 0E1W] at the keystone's pair, with the
chain-level map localized and nothing around it.**

`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat` with
the content factor replaced by
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat_q_map`, in which the
fixed-universe transpose and the [stacks 0A63] uncurrying around
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` have cancelled against the K-injective
Hom comparison.

What is left in the value is: the two counits `c₁` and `c₂`, still hypotheses because neither sits
at a class; the scalar equivalence of the scalar-restriction comparison `δ` and of the transported
one `τ`; the comparison `eF` of the two derived extensions of scalars; the two K-flat
presentations `eX` and `eY` through the two source and target functors of the change-of-rings Hom
comparison; two `Stacks.DerivedHom.BaseChange.homModelIso` representation isomorphisms; one
component of `CategoryTheory.Functor.mapDerivedCategoryFactors`; and the localization of the
chain-level map of [stacks 0E1W]. -/
theorem homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_q_map
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
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    let M := F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))
    let X₃ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            ((CochainComplex.DerivedTensor.extensionOfScalarsCochain.{uR, uA,
              max uR uA uM} f).obj (CochainComplex.DerivedTensor.tensorComplex.{uR,
                max uR uA uM} K L))
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q]
      (n : X₃ ⟶ J) [QuasiIso n],
    letI : IsIso (T.alphaB.app K₀) :=
      isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB K₀
        (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    letI := quasiIso_homComplexChangeOfRingsMap_of_kFlat f' K₀ J I q T.B T.alphaB
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    let eX := scalarLiftQObjIso.{uR, max uR uA uM} R L
    let eY := tensorKFlatKInjectiveLift.{uR, uA, uM} f F comparison K L hK hL J n
    let Z := CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj K₀) J
    ∀ (c₁ : E.functor.obj (E.inverse.obj (V.obj (HA.obj
            (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
              S.functor.obj M)))) ⟶
          V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
            S.functor.obj M)))
    (c₂ : E.inverse.obj (E.functor.obj (U.obj M)) ⟶ U.obj M)
    (_hc₁ : (derivedScalarEquivalence.{uR, max uR uA uM,
          max uR uA uM + 1} R).symm.toAdjunction.counit.app
        (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
          S.functor.obj M))) = c₁)
    (_hc₂ : (derivedScalarEquivalence.{uR, max uR uA uM,
          max uR uA uM + 1} R).toAdjunction.counit.app (U.obj M) = c₂),
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
        (U.obj (S.inverse.obj (HA.obj
          (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))), S.functor.obj M))))
        (DerivedCategory.Q.obj L) (U.obj M)
        ((derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison).inv.app
          (Opposite.op (DerivedCategory.Q.obj L), M)) =
      E.inverse.map
          ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).map
              ((E.functor.map (δ.hom.app (HA.obj
                      (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                        S.functor.obj M))) ≫
                  c₁,
                𝟙 (E.functor.obj (DerivedCategory.Q.obj L))) :
                  ((E.functor.obj (U.obj (S.inverse.obj (HA.obj
                        (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                          S.functor.obj M)))),
                      E.functor.obj (DerivedCategory.Q.obj L)) :
                    DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (V.obj (HA.obj
                        (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                          S.functor.obj M)),
                      E.functor.obj (DerivedCategory.Q.obj L))) ≫
            DerivedInternalHom.Model.homEquiv
              (V.obj (HA.obj (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                S.functor.obj M)))
              (E.functor.obj (DerivedCategory.Q.obj L)) (E.functor.obj (U.obj M))
              (V.map (HA.map (CategoryTheory.Prod.mkHom
                  (eF.hom.app (DerivedCategory.Q.obj L)).op (𝟙 (S.functor.obj M)))) ≫
                ((homRestrictTarget f' T.B).map
                      (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
                    (V.map (homModelIso ((CochainComplex.extendScalarsLarge.{max uR uA uM,
                            max uR uA uM, max uR uA uM} f').obj K₀) J
                          (asIso (T.alphaB.app K₀)) (Iso.refl _)).hom ≫
                        ((ModuleCat.restrictScalars.{max uR uA uM}
                            f').mapDerivedCategoryFactors.app Z).hom ≫
                          DerivedCategory.Q.map (homComplexChangeOfRingsMap f' K₀ J I q) ≫
                            (homModelIso K₀ I (Iso.refl _)
                              ((ModuleCat.restrictScalars.{max uR uA uM}
                                  f').mapDerivedCategoryFactors.app J ≪≫
                                @asIso _ _ _ _ (DerivedCategory.Q.map q)
                                  ((DerivedCategory.isIso_Q_map_iff_quasiIso _
                                    q).2 inferInstance))).inv) ≫
                      (homRestrictSource f').map
                        (CategoryTheory.Prod.mkHom eX.hom.op eY.inv)) ≫
                  HR.map (CategoryTheory.Prod.mkHom
                    (𝟙 (Opposite.op (E.functor.obj (DerivedCategory.Q.obj L))))
                    (τ.inv.app M)))) ≫
        c₂ := by
  intro F comparison hF K L hK hL a E S f' U V T a' δ τ eF HR HA M X₃ K₀ J I hJ hI q hq n hn
    eX eY Z c₁ c₂ hc₁ hc₂
  exact homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_model_value.{uR, uA, uM} f F
    comparison (Opposite.op (DerivedCategory.Q.obj L)) M c₁ c₂ _ hc₁ hc₂
    (modelRestrictScalarsNatIso_inv_app_tensorKFlat_q_map.{uR, uA, uM} f F comparison
      K L hK hL J I q n)

end Stacks.DerivedHom.BaseChange

end
