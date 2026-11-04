module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsComponent
public import StacksFrontier.Homology.HomComplex.RHom.BaseChangeResolution
import StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionTransport

/-!
# [stacks 0E1X] with its change-of-rings factor evaluated

`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models` expands the morphism of
[stacks 0E1X] at arbitrary objects into named data, but one of its factors is the component of the
change-of-rings isomorphism of [stacks 0E1W] at `(K, F M)`, carried verbatim.  That component is
pinned by
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q`, whose
hypotheses are a K-flat/K-injective join of the two scalar lifts and three presentations of
objects of `D(ULift A)` as classes of cochain complexes.

This file performs that substitution.  The result,
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_Q`, has exactly one factor
that is not a unit, a counit, a localization comparison, a component of the scalar-restriction
comparison at a class of a cochain complex or a chosen isomorphism: the representative model
comparison `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso`.

That last factor is eliminated in turn by
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomBaseChangeMonoidalValue`, which
substitutes
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso` here and
leaves the degreewise monoidality isomorphism
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` as the only chain map of the value.

## Main results

* `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_Q` — the value of
  [stacks 0E1X] with the [stacks 0E1W] factor replaced by its component formula.

## Implementation notes

The witnesses of the component formula are taken as hypotheses, in the same order as in
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q`, so that
the equation composes with whatever identification of the two variables a consumer holds; that
they always exist is `Stacks.DerivedHom.BaseChange.exists_kFlatKInjectiveJoin` together with
`Stacks.DerivedHom.BaseChange.isoQObjPreimage`.

## References

* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory StacksDraft.DerivedHom

namespace Stacks.DerivedHom.ExtensionOfScalars

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

/-- **The morphism of [stacks 0E1X] with the change-of-rings factor of [stacks 0E1W]
evaluated.**

This is `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models` with its one
remaining opaque factor — the component of the change-of-rings isomorphism of [stacks 0E1W] at
`(K, F M)` — replaced by
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q`.  Every
factor of the right-hand side is then a unit or counit of one of the adjunctions in play, a
component of the scalar-restriction comparison at a class of a cochain complex, a localization
comparison, a chosen isomorphism, or the representative model comparison
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso`.

Nothing is assumed of `K` or `M`: the K-flat model `X` of `M` exists by
`CochainComplex.DerivedExtensionScalars.exists_kFlat_model`, the models `Y`, `X₁`, `X₂`, `X₃` by
essential surjectivity of `DerivedCategory.Q`, and `K₀`, `J`, `I`, `q` by
`Stacks.DerivedHom.BaseChange.exists_kFlatKInjectiveJoin`. -/
theorem derivedHomBaseChange_eq_of_models_Q
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
    (K M : DerivedCategory (ModuleCat.{max uR uA uM} R)),
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
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse :=
      _root_.Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, uM} f
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    ∀ (X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
      (hX : CochainComplex.KFlat.{uR, max uM uA} X)
      (φ : M ≅ DerivedCategory.Q.obj X)
      (Y : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
      (ψ : (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A).obj
          (Opposite.op (F.obj K), F.obj M) ≅ DerivedCategory.Q.obj Y)
      (X₁ X₂ X₃ : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (e₁ : HA.obj (Opposite.op (S.functor.obj (F.obj K)), S.functor.obj (F.obj M)) ≅
        DerivedCategory.Q.obj X₁)
      (e₂ : T.B.obj (E.functor.obj K) ≅ DerivedCategory.Q.obj X₂)
      (e₃ : S.functor.obj (F.obj M) ≅ DerivedCategory.Q.obj X₃)
      (K₀ : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q] (hK₀ : K₀.KFlat)
      (eX : E.functor.obj K ≅ DerivedCategory.Q.obj K₀)
      (eY : S.functor.obj (F.obj M) ≅ DerivedCategory.Q.obj J),
    letI : IsIso (comparison.app X) :=
      CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM}
        f F comparison X hX
    derivedHomBaseChange.{uR, uA, uM} f F comparison K M =
      F.map ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR,
              max uR uA uM} R).map
            (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op K))
              (φ.hom ≫
                (DerivedCategory.Q.map
                    (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR,
                      uA} f).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app X) ≫
                  (ModuleCat.restrictScalars.{max uR uA uM, uR,
                      uA} f).mapDerivedCategoryFactors.inv.app
                      (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj X) ≫
                    (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
                      (inv (comparison.app X))) ≫
                (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
                  (show (DerivedCategory.Q ⋙ F).obj X ⟶ F.obj M from F.map φ.inv))) ≫
          (E.inverse.map (HR.map (CategoryTheory.Prod.mkHom
                (𝟙 (Opposite.op (E.functor.obj K)))
                (show E.functor.obj (U.obj (F.obj M)) ⟶ V.obj (S.functor.obj (F.obj M)) from
                  E.functor.map (U.map (S.unitIso.hom.app (F.obj M)) ≫
                        U.map (S.inverse.map e₃.hom) ≫
                        δ.hom.app (DerivedCategory.Q.obj X₃) ≫ E.inverse.map (V.map e₃.inv)) ≫
                    E.counitIso.hom.app (V.obj (S.functor.obj (F.obj M)))))) ≫
              E.inverse.map ((_root_.Stacks.DerivedHom.BaseChange.homRestrictSource f').map
                    (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
                  (_root_.Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso f' T.B
                    T.alphaB K₀ J I q hK₀).hom ≫
                    (_root_.Stacks.DerivedHom.BaseChange.homRestrictTarget f' T.B).map
                      (CategoryTheory.Prod.mkHom eX.hom.op eY.inv)) ≫
                E.inverse.map (V.map (HA.map (CategoryTheory.Prod.mkHom
                    (S.functor.map (F.map (E.toAdjunction.unit.app K ≫
                          E.inverse.map (a'.unit.app (E.functor.obj K)))) ≫
                        S.functor.map (F.map ((V ⋙ E.inverse).map e₂.hom ≫
                            δ.inv.app (DerivedCategory.Q.obj X₂) ≫
                              (S.inverse ⋙ U).map e₂.inv)) ≫
                          S.functor.map
                              (a.counit.app (S.inverse.obj (T.B.obj (E.functor.obj K)))) ≫
                            S.toAdjunction.counit.app (T.B.obj (E.functor.obj K))).op
                    (𝟙 (S.functor.obj (F.obj M)))))) ≫
                  (V ⋙ E.inverse).map e₁.hom ≫
                    δ.inv.app (DerivedCategory.Q.obj X₁) ≫ (S.inverse ⋙ U).map e₁.inv)) ≫
        F.map ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
            ψ.hom) ≫
          (F.map ((ModuleCat.restrictScalars.{max uR uA uM, uR,
                uA} f).mapDerivedCategoryFactors.hom.app Y) ≫
            comparison.app (((ModuleCat.restrictScalars.{max uR uA uM, uR,
                uA} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≫
              DerivedCategory.Q.map
                (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR,
                  uA} f).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app Y)) ≫
          ψ.inv := by
  let : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  let : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
  let : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  let : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
  intro F comparison hF K M a E S f' U V T a' δ HR HA X hX φ Y ψ X₁ X₂ X₃ e₁ e₂ e₃ K₀ J I hJ hI
    q hq hK₀ eX eY
  have := hF
  have := hJ
  have := hI
  have := hq
  have : IsIso (comparison.app X) :=
    CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM}
      f F comparison X hX
  rw [derivedHomBaseChange_eq_of_models.{uR, uA, uM} f F comparison K M X hX φ Y ψ,
    _root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q.{
      uR, uA, uM} f F comparison (Opposite.op K) (F.obj M) X₁ X₂ X₃ e₁ e₂ e₃ K₀ J I q hK₀ eX eY]
  rfl

end Stacks.DerivedHom.ExtensionOfScalars

end
