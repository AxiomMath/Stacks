module

public import StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionComponent

/-!
# Transporting the component formula for the scalar-restriction comparison

`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q` and
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_inv_app_Q` evaluate the scalar-restriction
comparison `δ` at the class `DerivedCategory.Q.obj X` of a cochain complex.  This file moves the
two formulas to an arbitrary object along an isomorphism to such a class, and computes the
components of the transported restriction comparison `τ` in terms of those of `δ`.

## Main results

* `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_of_iso` and
  `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_inv_app_of_iso` — the components of `δ` at an
  arbitrary object, conjugated from the components at a class by naturality.
* `Stacks.DerivedHom.BaseChange.scalarRestrictionTransportedIso_hom_app` — the components of the
  transported restriction comparison `τ`, in terms of the components of `δ`.
* `Stacks.DerivedHom.BaseChange.scalarRestrictionTransportedIso_inv_app` — the same for the
  inverse components of `τ`.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

open CategoryTheory

namespace Stacks.DerivedHom.BaseChange

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

/-- Every object of a derived category is isomorphic to the class of a cochain complex: the
essential surjectivity of `DerivedCategory.Q`. -/
public noncomputable def isoQObjPreimage {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (Y : DerivedCategory C) :
    Y ≅ DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage Y) :=
  (DerivedCategory.Q.objObjPreimageIso Y).symm

/-- The component of a natural transformation at an object, read off from its component at any
isomorphic object. -/
public theorem natTrans_app_eq_of_iso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    α.app X = F.map e.hom ≫ α.app Y ≫ G.map e.inv := by
  rw [← Category.assoc, α.naturality, Category.assoc, ← G.map_comp, e.hom_inv_id, G.map_id,
    Category.comp_id]

/-- The components of the transported restriction comparison `τ`, at abstract equivalences and an
abstract restriction comparison: the scalar unit, the comparison at the scalar lift, and the scalar
counit. -/
private theorem transportedIso_hom_app
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (E : C ≌ C') (S : D ≌ D') (U : D ⥤ C) (V : D' ⥤ C')
    (δ : S.inverse ⋙ U ≅ V ⋙ E.inverse) (Y : D) :
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    τ.hom.app Y =
      E.functor.map (U.map (S.unitIso.hom.app Y) ≫ δ.hom.app (S.functor.obj Y)) ≫
        E.counitIso.hom.app (V.obj (S.functor.obj Y)) := by
  dsimp only
  simp [Iso.compInverseIso_hom_app, Iso.inverseCompIso_inv_app]

/-- The inverse components of the transported restriction comparison `τ`, at the same abstract
data: the scalar counit read backwards, then the comparison and the scalar unit read backwards
under the equivalence. -/
private theorem transportedIso_inv_app
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (E : C ≌ C') (S : D ≌ D') (U : D ⥤ C) (V : D' ⥤ C')
    (δ : S.inverse ⋙ U ≅ V ⋙ E.inverse) (Y : D) :
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    τ.inv.app Y =
      E.counitIso.inv.app (V.obj (S.functor.obj Y)) ≫
        E.functor.map (δ.inv.app (S.functor.obj Y) ≫ U.map (S.unitIso.inv.app Y)) := by
  intro τ
  exact (Iso.inv_eq_inv (Iso.app τ Y)
      (E.functor.mapIso (U.mapIso (Iso.app S.unitIso Y) ≪≫ Iso.app δ (S.functor.obj Y)) ≪≫
        Iso.app E.counitIso (V.obj (S.functor.obj Y)))).2
    (transportedIso_hom_app E S U V δ Y)

/-- **The components of the scalar-restriction comparison at an arbitrary object.**

Given an isomorphism `e` from `Y` to the class of a cochain complex `X`, the component of
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso` at `Y` is its component at that class,
conjugated by `e`. -/
public theorem scalarRestrictionIso_hom_app_of_iso
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)))
    (X : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
    (e : Y ≅ DerivedCategory.Q.obj X) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM,uR,uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM,uR,uA} f).isLeftAdjoint
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
    (scalarRestrictionIso.{uR, uA, uM} f).hom.app Y =
      U.map (S.inverse.map e.hom) ≫
        (scalarRestrictionIso.{uR, uA, uM} f).hom.app (DerivedCategory.Q.obj X) ≫
          E.inverse.map (V.map e.inv) :=
  natTrans_app_eq_of_iso (scalarRestrictionIso.{uR, uA, uM} f).hom e

/-- **The components of the inverse scalar-restriction comparison at an arbitrary object.**
The conjugate, by an isomorphism `e : Y ≅ DerivedCategory.Q.obj X`, of
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_inv_app_Q`. -/
public theorem scalarRestrictionIso_inv_app_of_iso
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)))
    (X : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
    (e : Y ≅ DerivedCategory.Q.obj X) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM,uR,uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM,uR,uA} f).isLeftAdjoint
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
    (scalarRestrictionIso.{uR, uA, uM} f).inv.app Y =
      (V ⋙ E.inverse).map e.hom ≫
        (scalarRestrictionIso.{uR, uA, uM} f).inv.app (DerivedCategory.Q.obj X) ≫
          (S.inverse ⋙ U).map e.inv :=
  natTrans_app_eq_of_iso (scalarRestrictionIso.{uR, uA, uM} f).inv e

/-- **The components of the transported restriction comparison `τ`.**

`τ` is built from the scalar-restriction comparison `δ` by conjugating with the two scalar-lift
equivalences.  Its component at `M` is the unit of the scalar lift over `A`, restricted along `f`;
the component of `δ` at the scalar lift of `M`; and the counit of the scalar lift over `R`. -/
public theorem scalarRestrictionTransportedIso_hom_app
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (M : DerivedCategory (ModuleCat.{max uR uA uM} A)) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM,uR,uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM,uR,uA} f).isLeftAdjoint
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
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    τ.hom.app M =
      E.functor.map (U.map (S.unitIso.hom.app M) ≫ δ.hom.app (S.functor.obj M)) ≫
        E.counitIso.hom.app (V.obj (S.functor.obj M)) :=
  transportedIso_hom_app _ _ _ _ (scalarRestrictionIso.{uR, uA, uM} f) M

/-- **The inverse components of the transported restriction comparison `τ`.**

The inverse component at `M` is the counit of the scalar lift over `R` read backwards, then the
component of `δ` and the unit of the scalar lift over `A`, both read backwards. -/
public theorem scalarRestrictionTransportedIso_inv_app
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (M : DerivedCategory (ModuleCat.{max uR uA uM} A)) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM,uR,uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM,uR,uA} f).isLeftAdjoint
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
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    τ.inv.app M =
      E.counitIso.inv.app (V.obj (S.functor.obj M)) ≫
        E.functor.map (δ.inv.app (S.functor.obj M) ≫ U.map (S.unitIso.inv.app M)) :=
  transportedIso_inv_app _ _ _ _ (scalarRestrictionIso.{uR, uA, uM} f) M

end Stacks.DerivedHom.BaseChange
