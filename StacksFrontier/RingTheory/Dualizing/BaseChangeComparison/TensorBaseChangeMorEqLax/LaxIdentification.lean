module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeMorEqLax.ScalarLiftComparisons

/-!
# The [stacks 068I] candidate is the lax monoidal structure map of derived base change

Let `f : R → A` be a ring homomorphism and `F` a model of derived extension of scalars along `f`.
The monoidality isomorphism of [stacks 068I], read in the tensor vocabulary of [stacks 0A63] by
`Dualizing.tensorBaseChangeMor`, is the lax monoidal structure map
`Dualizing.derivedTensorBaseChange` built from the change-of-rings isomorphism of [stacks 0E1W].

## Main results

* `Dualizing.unitSide_degreewise` -- the [stacks 0GMT] side of the keystone at a K-flat pair, at
  the chain map `rSTCI ≫ scalarLiftExtendUnitChain ≫ n ≫ q`, is the degreewise unit.
* `Dualizing.valuedTranspose_comp_eq_comparison_comp_Q_map` -- the valued [stacks 068I] transpose,
  read through the comparison factors of [stacks 0E1W], is an explicit localized chain map.
* `Dualizing.tensorBaseChangeMor_eq_derivedTensorBaseChange` -- **the identification**: the
  [stacks 068I] candidate is the lax monoidal structure map of derived base change.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

open CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

universe uR uA uM

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]




/-- Reassociating a five-fold composite along an equation of its middle part. -/
theorem reassoc_five {C : Type*} [Category C] {A₀ A B X Y Z W Y₁ Y₂ Y₃ : C} (p₁ : A₀ ⟶ A)
    (p₂ : A ⟶ B) (x : B ⟶ X) (st : X ⟶ Y) (ve : Y ⟶ Z) (ta : Z ⟶ W) (c : B ⟶ Y₁)
    (fi : Y₁ ⟶ Y₂) (vs : Y₂ ⟶ Y₃) (vS : Y₃ ⟶ Z) (h : x ≫ st ≫ ve = c ≫ fi ≫ vs ≫ vS) :
    p₁ ≫ p₂ ≫ x ≫ st ≫ ve ≫ ta = (p₁ ≫ p₂ ≫ c ≫ fi ≫ vs) ≫ vS ≫ ta := by
  simp only [Category.assoc, reassoc_of% h]

/-- Cancelling an isomorphism against its inverse inside a bracketed composite. -/
theorem hom_inv_comp_cancel {C : Type*} [Category C] {X Y Z W : C} (h : X ⟶ Y) [IsIso h]
    (a : X ⟶ Z) (b : Z ⟶ W) : h ≫ (inv h ≫ a) ≫ b = a ≫ b := by
  simp

/-- **Pulling a natural transformation and an isomorphism out of a transposed composite.**

Let `E : C ≌ D`, `U : A₀ ⥤ C`, `Sf : A₀ ⥤ A₁`, `V : A₁ ⥤ D` and `τinv : Sf ⋙ V ⟶ U ⋙ E.functor`.
If the morphism transposed across `E` is `z' ≫ V (Sf k) ≫ τinv_M` and `k ≫ g ≫ c = 𝟙`, then the
transposed composite followed by `U g ≫ U c` is the transposed composite at the source of `k`. -/
theorem transpose_comp_natTrans_comp_cancel {C D A₀ A₁ : Type*} [Category C] [Category D]
    [Category A₀] [Category A₁] (E : C ≌ D) (U : A₀ ⥤ C) (Sf : A₀ ⥤ A₁) (V : A₁ ⥤ D)
    (τinv : Sf ⋙ V ⟶ U ⋙ E.functor) {T : C} {Z : D} {P M M' : A₀}
    (t : T ⟶ E.inverse.obj Z) (z' : Z ⟶ V.obj (Sf.obj P)) (k : P ⟶ M) (g : M ⟶ M')
    (c : M' ⟶ P) (zτ : Z ⟶ E.functor.obj (U.obj M))
    (hzτ : zτ = z' ≫ V.map (Sf.map k) ≫ τinv.app M) (hk : k ≫ g ≫ c = 𝟙 P) :
    (t ≫ (E.inverse.map zτ ≫ E.unitIso.inv.app (U.obj M)) ≫ U.map g) ≫ U.map c =
      t ≫ E.inverse.map (z' ≫ τinv.app P) ≫ E.unitIso.inv.app (U.obj P) := by
  subst hzτ
  have hnat : V.map (Sf.map k) ≫ τinv.app M = τinv.app P ≫ E.functor.map (U.map k) :=
    τinv.naturality k
  have hu : E.inverse.map (E.functor.map (U.map k)) ≫ E.unitIso.inv.app (U.obj M) =
      E.unitIso.inv.app (U.obj P) ≫ U.map k :=
    E.unitIso.inv.naturality (U.map k)
  have hU : U.map k ≫ U.map g ≫ U.map c = 𝟙 _ := by
    rw [← U.map_comp, ← U.map_comp, hk, U.map_id]
  simp only [Category.assoc, Functor.map_comp, hnat, reassoc_of% hu, hU, Category.comp_id]

include hF in
/-- **The [stacks 0GMT] side of the keystone at a K-flat pair, at the unit chain map.** -/
theorem unitSide_degreewise
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
      max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse :=
      _root_.Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let W := (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
      (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)
    let M := F.obj W
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let X₃ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
        (tensorComplex.{uR, max uR uA uM} K L))
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q]
      (n : X₃ ⟶ J) [QuasiIso n],
    let eX := _root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max uR uA uM} R L
    let eY := _root_.Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift.{uR, uA, uM} f F
      comparison K L hK hL J n
    letI : IsIso (comparison.app (tensorComplex.{uR, max uR uA uM} K L)) :=
      CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
        comparison (tensorComplex.{uR, max uR uA uM} K L)
        (_root_.Stacks.DerivedHom.BaseChange.kFlat_tensorComplex.{uR, uA, uM} K L hK hL)
    ∀ (x : DerivedCategory.Q.obj ((((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⊗ K₀) ⟶ DerivedCategory.Q.obj I),
      x = DerivedCategory.Q.map
          ((restrictScalarsTensorComplexIso
              (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R) K L).hom ≫
            _root_.Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain.{uR, uA, uM} f
              (tensorComplex.{uR, max uR uA uM} K L) ≫
            (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
                max uR uA uM} f').map n ≫ q) →
      ((derivedTensor_comparison.{uR, max uR uA uM} R K L hL).inv ≫
              (E.inverse.map
                      ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensor.map
                (((_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR,
                        max uR uA uM} R K).hom, eX.hom) :
                  ((E.functor.obj (DerivedCategory.Q.obj K),
                        E.functor.obj (DerivedCategory.Q.obj L)) :
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{max uR uA uM}
                          (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
                            R).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
                      DerivedCategory.Q.obj K₀)) ≫
              ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso
                  (((ModuleCat.restrictScalars.{max uR uA uM}
                      (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
                        R).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) K₀
                  (_root_.Stacks.DerivedHom.BaseChange.kFlat_scalarLift.{uR,
                    max uR uA uM} R L hL)).hom ≫
                x ≫
                  (((ModuleCat.restrictScalars.{max uR uA uM}
                              f').mapDerivedCategoryFactors.app J ≪≫
                          @asIso _ _ _ _ (DerivedCategory.Q.map q)
                            ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2
                              inferInstance)).inv ≫
                    V.map eY.inv ≫ τ.inv.app M)) ≫
                  E.unitIso.inv.app (U.obj M)) ≫
            U.map (F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom)) ≫
          U.map (comparison.app (tensorComplex.{uR, max uR uA uM} K L)) =
        DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app (tensorComplex.{uR, max uR uA uM} K L)) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR,
              uA} f).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (tensorComplex.{uR, max uR uA uM} K L)) := by
  intro f' E S U V δ τ W M K₀ X₃ J I hJ hI q hq n hn eX eY x hx
  subst hx
  let N := tensorComplex.{uR, max uR uA uM} K L
  let eN := (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj N
  let sLQN := _root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uA, max uR uA uM} A eN
  let tKCI := _root_.Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uA, uM} f F
    comparison K L hK hL
  let fac := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors
  let c' := (restrictScalarsTensorComplexIso
      (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R) K L).hom ≫
    _root_.Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain.{uR, uA, uM} f N
  have hn : DerivedCategory.Q.map ((CochainComplex.restrictScalarsLarge.{max uR uA uM,
        max uR uA uM, max uR uA uM} f').map n) ≫ fac.inv.app J =
      fac.inv.app X₃ ≫ V.map (DerivedCategory.Q.map n) := fac.inv.naturality n
  have heY : DerivedCategory.Q.map n ≫ eY.inv = sLQN.inv ≫ S.functor.map tKCI.inv := by
    simp only [eY, _root_.Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift,
      _root_.Stacks.DerivedHom.BaseChange.tensorKFlatComparisonLiftIso, Iso.trans_inv,
      asIso_inv, IsIso.hom_inv_id_assoc, Functor.mapIso_inv]
    rfl
  have hx1 : DerivedCategory.Q.map ((restrictScalarsTensorComplexIso
              (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R) K L).hom ≫
            _root_.Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain.{uR, uA, uM} f N ≫
            (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
                max uR uA uM} f').map n ≫ q) ≫
        (fac.app J ≪≫ @asIso _ _ _ _ (DerivedCategory.Q.map q)
          ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance)).inv ≫
          V.map eY.inv =
      DerivedCategory.Q.map c' ≫ fac.inv.app X₃ ≫ V.map sLQN.inv ≫
        V.map (S.functor.map tKCI.inv) := by
    have e1 : DerivedCategory.Q.map ((restrictScalarsTensorComplexIso
              (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R) K L).hom ≫
            _root_.Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain.{uR, uA, uM} f N ≫
            (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
                max uR uA uM} f').map n ≫ q) =
        DerivedCategory.Q.map c' ≫ DerivedCategory.Q.map
          ((CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
                max uR uA uM} f').map n) ≫ DerivedCategory.Q.map q :=
      ((congrArg DerivedCategory.Q.map (Category.assoc _ _ _).symm).trans
        (DerivedCategory.Q.map_comp _ _)).trans
        (congrArg (fun z => DerivedCategory.Q.map c' ≫ z) (DerivedCategory.Q.map_comp _ _))
    have e2 : (fac.app J ≪≫ @asIso _ _ _ _ (DerivedCategory.Q.map q)
          ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance)).inv =
        inv (DerivedCategory.Q.map q) ≫ fac.inv.app J := rfl
    rw [e1, e2]
    have hn' : DerivedCategory.Q.map ((CochainComplex.restrictScalarsLarge.{max uR uA uM,
          max uR uA uM, max uR uA uM} f').map n) ≫ fac.inv.app J ≫ V.map eY.inv =
        fac.inv.app X₃ ≫ V.map sLQN.inv ≫ V.map (S.functor.map tKCI.inv) := by
      have h1 := congrArg (fun z => z ≫ V.map eY.inv) hn
      refine (Category.assoc _ _ _).symm.trans (h1.trans ((Category.assoc _ _ _).trans ?_))
      refine congrArg (fun z => fac.inv.app X₃ ≫ z) ?_
      exact (V.map_comp _ _).symm.trans ((congrArg V.map heY).trans (V.map_comp _ _))
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (fun z => DerivedCategory.Q.map c' ≫ z) ((Category.assoc _ _ _).trans
      ((congrArg (fun z => DerivedCategory.Q.map
          ((CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
            max uR uA uM} f').map n) ≫ z)
        (hom_inv_comp_cancel (DerivedCategory.Q.map q) (fac.inv.app J) (V.map eY.inv))).trans hn'))
  have hk : tKCI.inv ≫ F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom ≫
      comparison.app N = 𝟙 _ := tKCI.inv_hom_id
  let Tm := (DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensor.map
                (((_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR,
                        max uR uA uM} R K).hom, eX.hom) :
                  ((E.functor.obj (DerivedCategory.Q.obj K),
                        E.functor.obj (DerivedCategory.Q.obj L)) :
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                    (DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{max uR uA uM}
                          (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
                            R).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
                      DerivedCategory.Q.obj K₀))
  let Ti := ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensorIso
          (((ModuleCat.restrictScalars.{max uR uA uM}
              (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
                R).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) K₀
          (_root_.Stacks.DerivedHom.BaseChange.kFlat_scalarLift.{uR,
            max uR uA uM} R L hL)).hom
  refine (transpose_comp_natTrans_comp_cancel E U S.functor V τ.inv
      (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).inv
      (Tm ≫ Ti ≫ DerivedCategory.Q.map c' ≫ fac.inv.app X₃ ≫ V.map sLQN.inv)
      tKCI.inv (F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom)
      (comparison.app N) _ (reassoc_five _ _ _ _ _ _ _ _ _ _ hx1) hk).trans ?_
  refine (congrArg (fun z => (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).inv ≫ z)
    (_root_.Stacks.DerivedHom.BaseChange.inverse_map_comp_transportedIso_inv_comp_unitIso_inv.{uR,
      uA, uM} f (DerivedCategory.Q.obj eN) _)).trans ?_
  refine (_root_.Stacks.DerivedHom.BaseChange.cancel_presentation_glue E.inverse
    (derivedTensor_comparison.{uR, max uR uA uM} R K L hL)
    Tm Ti
    (DerivedCategory.Q.map (restrictScalarsTensorComplexIso
      (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R) K L).hom)
    (DerivedCategory.Q.map (_root_.Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain.{uR, uA,
      uM} f N))
    (DerivedCategory.Q.map c') (fac.inv.app X₃) (V.map sLQN.inv) _ _ _
    (DerivedCategory.Q.map_comp _ _)
    (_root_.Stacks.DerivedHom.BaseChange.scalarEquivalence_inverse_map_tensor_scalarLift.{uR,
      max uR uA uM} R K L hL)).trans ?_
  let resSym := (ModuleCat.restrictScalars.{max uR uA uM}
    (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let Z' := ((ModuleCat.restrictScalars.{max uR uA uM} f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (resSym.obj X₃)
  let liftR := (ModuleCat.restrictScalars.{max uR uA uM}
    (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let φ := ((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app N ≫
    ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (_root_.Stacks.DerivedHom.BaseChange.scalarLiftCounitInv.{uA, max uR uA uM} A eN)
  let SIF := _root_.Stacks.DerivedHom.BaseChange.scalarEquivalenceInverseFactors.{uA,
    max uR uA uM} A
  let facU := (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors
  exact _root_.Stacks.DerivedHom.BaseChange.transported_unit_chain_assembly E U S.functor
    S.inverse V δ.inv
    (_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max uR uA uM} R N).hom
    (DerivedCategory.Q.map (liftR.map φ))
    (DerivedCategory.Q.map
      (_root_.Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison.{uR, uA, uM} f X₃))
    (fac.inv.app X₃) sLQN.inv (S.unitIso.inv.app (DerivedCategory.Q.obj eN))
    (DerivedCategory.Q.map φ)
    (_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max uR uA uM} R Z').hom
    (facU.inv.app (resSym.obj X₃) ≫ U.map (SIF.inv.app X₃))
    (DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA}
      f).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app N))
    (facU.inv.app eN)
    (DerivedCategory.Q.map
      (_root_.Stacks.DerivedHom.BaseChange.scalarLiftCounitInv.{uA, max uR uA uM} A eN) ≫
        SIF.inv.app X₃)
    (DerivedCategory.Q.map
      (_root_.Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain.{uR, uA, uM} f N))
    (DerivedCategory.Q.map_comp _ _)
    (Stacks.DerivedHom.BaseChange.scalarEquivalence_functor_map_Q_map_comp_scalarLiftQObjIso.{uR,
      max uR uA uM} R φ).symm
    (Stacks.DerivedHom.BaseChange.unitIso_comp_inverse_map_chain_comp_scalarRestrictionIso_inv.{uR,
      uA, uM} f X₃)
    (_root_.Stacks.DerivedHom.BaseChange.unit_chain_naturality_step U _ _ _ _ _ _ _
      (DerivedCategory.Q.map_comp _ _)
      (facU.inv.naturality
        (_root_.Stacks.DerivedHom.BaseChange.scalarLiftCounitInv.{uA, max uR uA uM} A eN)))
    (_root_.Stacks.DerivedHom.BaseChange.scalarLift_unit_cancel S sLQN (SIF.app X₃) _
      (_root_.Stacks.DerivedHom.BaseChange.scalarEquivalence_unitIso_hom_app_Q_comp.{uA,
        max uR uA uM} A eN))

include hF in
/-- **The valued [stacks 068I] transpose, read through the comparison factors of [stacks 0E1W], is
the comparison at `K` followed by an explicit localized chain map.** -/
theorem valuedTranspose_comp_eq_comparison_comp_Q_map
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
      max uR uA uM} A
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
      (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)
    let M := F.obj W
    let liftA := (ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let _Kt := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let eK := (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K
    let eL := (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L
    let N := tensorComplex.{uR, max uR uA uM} K L
    let X₃ := liftA.obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj N)
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      [J.IsKInjective] (n : X₃ ⟶ J) [QuasiIso n],
    letI : IsIso (T.alphaB.app K₀) :=
      _root_.Stacks.DerivedHom.BaseChange.isIso_extendScalarsCounit_app_of_kFlat f'
        T.B T.alphaB K₀
        (_root_.Stacks.DerivedHom.BaseChange.kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    let eX := _root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max uR uA uM} R L
    let eY := _root_.Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift.{uR, uA, uM} f F
      comparison K L hK hL J n
    letI : IsIso (comparison.app N) :=
      CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
        comparison N
        (_root_.Stacks.DerivedHom.BaseChange.kFlat_tensorComplex.{uR, uA, uM} K L hK hL)
    letI : IsIso (comparison.app L) :=
      CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
        comparison L hL
    ∀ (hFL : IsKFlat.{uA, max uR uA uM} eL) (e : tensorComplex.{uA, max uR uA uM} eK eL ≅
        (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj N),
    let trV : F.obj (DerivedCategory.Q.obj K) ⟶
        dA.hom.obj (Opposite.op (F.obj (DerivedCategory.Q.obj L)), M) :=
      (dA.homEquiv (F.obj (DerivedCategory.Q.obj K)) (F.obj (DerivedCategory.Q.obj L))
            (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
              N))).symm
          (dA.tensor.map
                ((CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
                    ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
                      DerivedCategory (ModuleCat.{max uR uA uM} A) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
                    (DerivedCategory.Q.obj eK, DerivedCategory.Q.obj eL))) ≫
              (derivedTensor_comparison.{uA, max uR uA uM} A eK eL hFL).hom ≫
                DerivedCategory.Q.map e.hom) ≫
        dA.hom.map (𝟙 (Opposite.op (F.obj (DerivedCategory.Q.obj L))),
          (_root_.Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uA, uM} f F
            comparison K L hK hL).inv)
    let eFv :=
      ((T.B.map (_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR,
                max uR uA uM} R L).hom ≫
            (T.alphaB.app K₀ ≫ DerivedCategory.Q.map
              (extendScalarsLiftChainIso.{uR, uA, uM} f L).hom)) ≫
          (_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uA,
            max uR uA uM} A eL).inv) ≫
        S.functor.map (@CategoryTheory.inv _ _ _ _ (comparison.app L)
          (CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
            comparison L hL))
    let lamK := extendScalarsLiftChainIso.{uR, uA, uM} f K
    let lamL := extendScalarsLiftChainIso.{uR, uA, uM} f L
    let g₀ := (MonoidalCategory.tensorIso lamK lamL).hom ≫
      (restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A)
        eK eL).hom ≫ liftA.map e.hom ≫ n
    let t₀ := Stacks.HomComplex.TensorHomMap.Phi (ULift.{max uR uA uM} A) _ _ ≫
      Stacks.HomComplex.TensorHomMap.postcomp (ULift.{max uR uA uM} A) _ _ J g₀
    let m₀ := _root_.Stacks.DerivedHom.BaseChange.scalarLiftCounitInv.{uA, max uR uA uM} A eK ≫
      ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (lamK.inv ≫ t₀)
    trV ≫ S.inverse.map (HA.map (CategoryTheory.Prod.mkHom eFv.op (𝟙 (S.functor.obj M))) ≫
        HA.map (CategoryTheory.Prod.mkHom (T.B.map eX.inv).op eY.hom) ≫
          (_root_.Stacks.DerivedHom.BaseChange.homModelIso
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J (asIso (T.alphaB.app K₀))
            (Iso.refl (DerivedCategory.Q.obj J))).hom) ≫
        (_root_.Stacks.DerivedHom.BaseChange.scalarEquivalenceInverseFactors.{uA,
          max uR uA uM} A).hom.app (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J) =
      comparison.app K ≫ DerivedCategory.Q.map m₀ := by
  intro f' S T HA dA W M liftA _Kt K₀ eK eL N X₃ J hJ n hn eX eY hFL e trV eFv lamK lamL g₀ t₀ m₀
  refine (Category.assoc _ _ _).trans ?_
  refine (StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_symm_tensor_map_mkHom_assoc dA
    (comparison.app K) (comparison.app L) _ _).trans ?_
  refine congrArg (fun z => comparison.app K ≫ z) ?_
  let tKCI := _root_.Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uA, uM} f F
    comparison K L hK hL
  let sLQL := _root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uA, max uR uA uM} A eL
  let sLQN := _root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uA, max uR uA uM} A
    ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj N)
  have : IsIso (T.alphaB.app K₀) :=
    _root_.Stacks.DerivedHom.BaseChange.isIso_extendScalarsCounit_app_of_kFlat f'
      T.B T.alphaB K₀
      (_root_.Stacks.DerivedHom.BaseChange.kFlat_scalarLift.{uR, max uR uA uM} R L hL)
  have : IsIso (comparison.app L) :=
    CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
      comparison L hL
  have hα : CategoryTheory.inv (T.alphaB.app K₀) ≫ T.B.map eX.inv ≫ eFv ≫
      S.functor.map (comparison.app L) =
      DerivedCategory.Q.map lamL.hom ≫ sLQL.inv :=
    _root_.Stacks.DerivedHom.BaseChange.inv_comp_map_comp_eFv_cancel T.B S.functor
      (T.alphaB.app K₀) inferInstance eX (DerivedCategory.Q.map lamL.hom) sLQL.inv
      (comparison.app L)
      (CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
        comparison L hL)
  have hχ : S.functor.map tKCI.inv ≫ eY.hom = sLQN.hom ≫ DerivedCategory.Q.map n :=
    _root_.Stacks.DerivedHom.BaseChange.map_inv_comp_map_hom_cancel S.functor tKCI sLQN.hom
      (DerivedCategory.Q.map n)
  refine (congrArg (fun z => _ ≫ z)
    (_root_.Stacks.DerivedHom.BaseChange.hom_transport_combine S.inverse S.functor HA
      (comparison.app L) tKCI.inv eFv (T.B.map eX.inv) eY.hom
      (CategoryTheory.inv (T.alphaB.app K₀))
      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.Model.homComplexIso
        ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj K₀)
        J).hom
      ((_root_.Stacks.DerivedHom.BaseChange.scalarEquivalenceInverseFactors.{uA,
          max uR uA uM} A).hom.app (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J))
      _ _ hα hχ)).trans ?_
  refine (_root_.Stacks.DerivedHom.BaseChange.homEquiv_symm_derivedTensor_comparison_comp_model.{uA,
    max uR uA uM} A eK eL ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj N) hFL e.hom
    ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj K₀) J
    lamL.hom n).trans ?_
  refine congrArg (fun z => DerivedCategory.Q.map
    (_root_.Stacks.DerivedHom.BaseChange.scalarLiftCounitInv.{uA, max uR uA uM} A eK ≫
      ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map z)) ?_
  have hnat := Stacks.HomComplex.TensorHomMap.Phi_natural_mixed (ULift.{max uR uA uM} A)
    _ _ _ _ lamK.hom lamL.hom
  have hpp := StacksDraft.ScalarTransport.postcomp_precomp (ULift.{max uR uA uM} A) lamL.hom
    ((restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A)
      eK eL).hom ≫ liftA.map e.hom ≫ n)
  simp only [t₀, g₀, MonoidalCategory.tensorIso_hom, Stacks.HomComplex.TensorHomMap.postcomp_comp]
  rw [reassoc_of% hnat]
  exact _root_.Stacks.DerivedHom.BaseChange.eq_inv_hom_comp_of_eq lamK
    (congrArg (fun z => Stacks.HomComplex.TensorHomMap.Phi (ULift.{max uR uA uM} A) _ _ ≫ z) hpp)

include hF in
/-- **The [stacks 068I] identification at a pair of K-flat complexes.** -/
theorem tensorBaseChangeMor_eq_derivedTensorBaseChange_of_kFlat
    (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
      max uR uA uM + 1} f)
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) := by
  let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  obtain ⟨J, n, hn, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective
    (((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
        (tensorComplex.{uR, max uR uA uM} K L)))
  obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective
    ((CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj J)
  refine tensorBaseChangeMor_eq_of_unit_chain_prefix.{uR, uA, uM} f F comparison D K L hK hL
    J I q n ?_
  intro hFL e he trV eFv w t hw ha m hm
  refine unitSide_degreewise.{uR, uA, uM} f F comparison K L hK hL J I q n
    (DerivedCategory.Q.map m) ?_
  have hK' : CochainComplex.KFlat K := (isKFlat_iff_kFlat.{uR, max uR uA uM} K).mp hK
  have hm₀ := valuedTranspose_comp_eq_comparison_comp_Q_map.{uR, uA, uM} f F comparison K L hK hL
    J n hFL e
  let : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
  let : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
  have hpre := _root_.Stacks.DerivedHom.BaseChange.prefix_eq_scalarLiftQObjIso_comp_Q_map.{uR, uA,
    uM} f F comparison K hK' _ _ trV _ _ _ rfl hm₀
  have hQw := (cancel_epi (_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR,
    max uR uA uM} R K).hom).1 (ha.symm.trans (Eq.trans (by
      simp only [Functor.map_comp, Category.assoc]
      rfl) hpre))
  let liftR := (ModuleCat.restrictScalars.{max uR uA uM}
    (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let resf := (ModuleCat.restrictScalars.{max uR uA uM} f).mapHomologicalComplex (ComplexShape.up ℤ)
  let resSym := (ModuleCat.restrictScalars.{max uR uA uM}
    (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let res' := CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f'
  let η' := ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
    (ComplexShape.up ℤ)).unit
  let lamK := extendScalarsLiftChainIso.{uR, uA, uM} f K
  let lamL := extendScalarsLiftChainIso.{uR, uA, uM} f L
  let liftA := (ModuleCat.restrictScalars.{max uR uA uM}
    (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let eK := (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K
  let eL := (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L
  let g₀ := (MonoidalCategory.tensorIso lamK lamL).hom ≫
    (restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A)
      eK eL).hom ≫ liftA.map e.hom ≫ n
  let t₀ := Stacks.HomComplex.TensorHomMap.Phi (ULift.{max uR uA uM} A) _ _ ≫
    Stacks.HomComplex.TensorHomMap.postcomp (ULift.{max uR uA uM} A) _ _ J g₀
  have hA2 := _root_.Stacks.DerivedHom.BaseChange.lifted_unit_generic liftR res' (resSym ⋙ resf)
    (η'.app _) lamK t₀
    (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app K ≫
      resf.map (_root_.Stacks.DerivedHom.BaseChange.scalarLiftCounitInv.{uA, max uR uA uM} A eK))
    (_root_.Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison.{uR, uA, uM} f
      (liftA.obj eK))
    (_root_.Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison.{uR, uA, uM} f _)
    (_root_.Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain_eq.{uR, uA, uM} f K)
    (_root_.Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison_naturality.{uR, uA, uM}
      f (lamK.inv ≫ t₀))
  have hQw₀ : DerivedCategory.Q.map w =
      DerivedCategory.Q.map (η'.app (liftR.obj K) ≫ res'.map t₀) := by
    refine hQw.trans (congrArg DerivedCategory.Q.map (Eq.trans ?_ hA2))
    refine congrArg (· ≫ _) ?_
    refine congrArg liftR.map ?_
    refine congrArg (_ ≫ ·) ?_
    exact resf.map_comp _ _
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
    (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
      (ULift.{max uR uA uM} A)) ℤ)
  have := T.isLeftDerivedB
  have hisoK : IsIso (T.alphaB.app (liftR.obj K)) :=
    _root_.Stacks.DerivedHom.BaseChange.isIso_extendScalarsCounit_app_of_kFlat f'
      T.B T.alphaB _
      (_root_.Stacks.DerivedHom.BaseChange.kFlat_scalarLift.{uR, max uR uA uM} R K hK)
  have hK₀ := _root_.Stacks.DerivedHom.BaseChange.kFlat_scalarLift.{uR, max uR uA uM} R L hL
  have hU' := fun t' w' hw' => Stacks.DerivedHom.BaseChangeIso.Q_map_uncurry_eq_of_unit_comp f'
    T.B T.alphaB (hB := T.isLeftDerivedB) (liftR.obj K) (liftR.obj L) hK₀ J (hiso := hisoK) t' w'
    hw'
  have hU : DerivedCategory.Q.map (DerivedInternalHom.Model.uncurry t) =
      DerivedCategory.Q.map (DerivedInternalHom.Model.uncurry t₀) := by
    refine (hU' t w hw).trans (Eq.trans ?_ (hU' t₀ _ rfl).symm)
    congr 6
  have hcan : transportedMonoidalInvTail.{uR, uA, uM} f K L e ≫ g₀ = n :=
    _root_.Stacks.DerivedHom.BaseChange.three_iso_cancel _ _ _ n
  have h1 : DerivedCategory.Q.map (transportedMonoidalInvTail.{uR, uA, uM} f K L e ≫
      DerivedInternalHom.Model.uncurry t) = DerivedCategory.Q.map n := by
    refine (DerivedCategory.Q.map_comp _ _).trans ?_
    refine (congrArg (DerivedCategory.Q.map (transportedMonoidalInvTail.{uR, uA, uM} f K L e) ≫ ·)
      hU).trans ?_
    refine (DerivedCategory.Q.map_comp _ _).symm.trans ?_
    refine congrArg DerivedCategory.Q.map ?_
    refine (congrArg (transportedMonoidalInvTail.{uR, uA, uM} f K L e ≫ ·)
      (DerivedInternalHom.Model.uncurry_Phi_postcomp g₀)).trans hcan
  have h2 := _root_.Stacks.DerivedHom.BaseChange.map_congr_of_factors DerivedCategory.Q
    DerivedCategory.Q res' (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors _ _ h1
  rw [hm]
  exact _root_.Stacks.DerivedHom.BaseChange.map_comp_congr_middle DerivedCategory.Q _ _ _ _ q h2

include hF in
/-- **The [stacks 068I] candidate is the lax monoidal structure map of derived base change.**
For every left derived model `F` of extension of scalars along `f : R → A`, every total left
derived model `D` and every pair of objects of `D(R)`, the monoidality isomorphism of
[stacks 068I] read in the vocabulary of [stacks 0A63] by `Dualizing.tensorBaseChangeMor` is
`Dualizing.derivedTensorBaseChange`, the lax monoidal structure map built from the
change-of-rings isomorphism of [stacks 0E1W].

Both are natural, so it suffices to check at pairs of K-flat complexes
(`Dualizing.tensorBaseChangeMor_eq_of_kFlat`), which is
`Dualizing.tensorBaseChangeMor_eq_derivedTensorBaseChange_of_kFlat`. -/
theorem tensorBaseChangeMor_eq_derivedTensorBaseChange
    (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
      max uR uA uM + 1} f)
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y :=
  tensorBaseChangeMor_eq_of_kFlat.{uR, uA, uM} f F comparison D
    (fun K L hK hL => tensorBaseChangeMor_eq_derivedTensorBaseChange_of_kFlat.{uR, uA, uM} f F
      comparison D K L hK hL) X Y

end Dualizing

end
