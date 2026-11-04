module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoMonoidal
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomBaseChangeComponentValue

/-!
# [stacks 0E1X] with a chain-level value whose only chain map is the monoidality isomorphism

`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_Q` expands the morphism of
[stacks 0E1X] at arbitrary objects into named data with exactly one factor that is not a unit, a
counit, a localization comparison, a component of the scalar-restriction comparison or a chosen
isomorphism: the representative model comparison
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` of [stacks 0E1W].  And
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso` gives *that*
a value whose only chain-level ingredient is
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, the monoidality isomorphism of degreewise
extension of scalars — the chain-level lax monoidal structure map.

Substituting the second into the first is this file.  The outcome is a determinate value for
[stacks 0E1X] in which the only chain maps are the degreewise monoidality isomorphism, the chosen
quasi-isomorphism `q` of the K-flat/K-injective join, and the counit of degreewise
extension--restriction.  Via
`Dualizing.derivedTensorBaseChange_eq_evaluation`, which writes the lax monoidal structure map `μ`
of derived base change as the morphism of [stacks 0E1X] tensored with an identity followed by an
evaluation, the same value serves `μ`; so `μ` and the component of [stacks 0E1W] are both pinned
to the degreewise monoidality isomorphism, with no existential anywhere.

## Main results

* `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_monoidalIso` — the value
  of [stacks 0E1X] with the model comparison of [stacks 0E1W] replaced by its monoidality formula.

## Implementation notes

The witnesses are taken as hypotheses in the same order as in
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_Q`, with the four `let`s
naming the data of the monoidality formula inserted after them; that they always exist is
`Stacks.DerivedHom.BaseChange.exists_kFlatKInjectiveJoin` together with
`Stacks.DerivedHom.BaseChange.isoQObjPreimage` and
`CochainComplex.DerivedExtensionScalars.exists_kFlat_model`.

The scalar-lift ring `f' : ULift R →+* ULift A` puts both rings and all their modules in one
universe, which is the shape the inputs of the monoidality formula are stated at.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory StacksDraft.DerivedHom

namespace Stacks.DerivedHom.ExtensionOfScalars

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

/-- **The morphism of [stacks 0E1X] with the model comparison of [stacks 0E1W] read through the
monoidality isomorphism of degreewise extension of scalars.**

This is `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_Q` with its one
remaining opaque factor — the representative model comparison
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` — replaced by
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso`.  Every
factor of the right-hand side is then a unit or counit of one of the adjunctions in play, a
component of the scalar-restriction comparison at a class of a cochain complex, a localization
comparison, a representative isomorphism, a piece of [stacks 0A63] data, or the inverse of the
[stacks 0A63] transpose of `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` followed by the
uncurried counit of degreewise extension--restriction and by `q`.

Nothing is assumed of `K` or `M`: the K-flat model `X` of `M` exists by
`CochainComplex.DerivedExtensionScalars.exists_kFlat_model`, the models `Y`, `X₁`, `X₂`, `X₃` by
essential surjectivity of `DerivedCategory.Q`, and `K₀`, `J`, `I`, `q` by
`Stacks.DerivedHom.BaseChange.exists_kFlatKInjectiveJoin`. -/
theorem derivedHomBaseChange_eq_of_models_monoidalIso
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
    let adj₀ := (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z₀ := CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
      ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj K₀) J
    let P₀ := (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
      f').obj Z₀
    let W₀ := adj₀.homEquiv (P₀ ⊗ K₀) J
        ((CochainComplex.ExtendScalars.extendScalarsMonoidalIso f' P₀ K₀).inv ≫
          DerivedInternalHom.Model.uncurry (adj₀.counit.app Z₀)) ≫ q
    letI := T.isLeftDerivedB
    letI : IsIso (T.alphaB.app K₀) :=
      _root_.Stacks.DerivedHom.BaseChange.isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB
        K₀ hK₀
    letI := _root_.Stacks.DerivedHom.BaseChange.quasiIso_homComplexChangeOfRingsMap_of_kFlat.{max
      uR uA uM, max uR uA uM, max uR uA uM} f' K₀ J I q T.B T.alphaB hK₀
    letI : IsIso ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P₀)
        (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
          (((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso
            P₀ K₀ hK₀).hom ≫ DerivedCategory.Q.map W₀)) :=
      _root_.Stacks.DerivedHom.BaseChangeIso.isIso_homEquiv_symm_tensorIso f' K₀ J I q hK₀
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
                  ((_root_.Stacks.DerivedHom.BaseChange.homModelIso K₀ I (Iso.refl _)
                        ((ModuleCat.restrictScalars.{max uR uA uM, max uR uA uM,
                            max uR uA uM} f').mapDerivedCategoryFactors.app J ≪≫
                          @asIso _ _ _ _ (DerivedCategory.Q.map q)
                            ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2
                              inferInstance))).hom ≫
                      ((DerivedInternalHom.Model.adjunction
                        (ULift.{max uR uA uM} R)).homIso K₀ I).inv ≫
                        inv ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P₀)
                            (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
                          (((DerivedInternalHom.Model.adjunction
                                (ULift.{max uR uA uM} R)).tensorIso P₀ K₀ hK₀).hom ≫
                            DerivedCategory.Q.map W₀)) ≫
                          ((ModuleCat.restrictScalars.{max uR uA uM, max uR uA uM,
                              max uR uA uM} f').mapDerivedCategoryFactors.app Z₀).inv ≫
                            (ModuleCat.restrictScalars.{max uR uA uM, max uR uA uM,
                                max uR uA uM} f').mapDerivedCategory.map
                              (_root_.Stacks.DerivedHom.BaseChange.homModelIso
                                ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                                  max uR uA uM} f').obj K₀) J (asIso (T.alphaB.app K₀))
                                (Iso.refl _)).inv) ≫
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
    q hq hK₀ eX eY adj₀ Z₀ P₀ W₀
  have : IsIso (T.alphaB.app K₀) :=
    _root_.Stacks.DerivedHom.BaseChange.isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB
      K₀ hK₀
  have := _root_.Stacks.DerivedHom.BaseChange.quasiIso_homComplexChangeOfRingsMap_of_kFlat.{max
    uR uA uM, max uR uA uM, max uR uA uM} f' K₀ J I q T.B T.alphaB hK₀
  have : IsIso (comparison.app X) :=
    CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM}
      f F comparison X hX
  rw [derivedHomBaseChange_eq_of_models_Q.{uR, uA, uM} f F comparison K M X hX φ Y ψ X₁ X₂ X₃
      e₁ e₂ e₃ K₀ J I q hK₀ eX eY,
    _root_.Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso
      f' T.B T.alphaB K₀ J I q hK₀]

end Stacks.DerivedHom.ExtensionOfScalars

end
