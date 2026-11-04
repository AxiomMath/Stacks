module

public import StacksFrontier.Homology.Tor.BaseChangeTensorMonoidalTransport
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ScalarLiftExtendComparisonValue
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeValuedPrefixTransported
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ScalarLiftExtendComparison
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeMonoidalChainLevel
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeTransposeKFlat

/-!
# The keystone at a K-flat pair, in one vocabulary and with no existential data

`Dualizing.tensorBaseChangeMor_eq_of_valued_prefix_transported` reduces the [stacks 068I]
identification at a pair of K-flat complexes to one equation between localized chain maps, but
its hypothesis still quantifies over the chain map `c₀` of
`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` together with the equation `hc₀`
characterizing it -- data that lemma supplies, but data all the same, and data spelled in a
vocabulary different from the one the transported monoidality comparison is written in.

`Stacks.DerivedHom.BaseChange.eq_extendScalarsLiftChainIso` removes it: that characterizing
equation has a unique solution, namely
`CochainComplex.DerivedTensor.extendScalarsLiftChainIso`, the explicit comparison of "lift
scalars, then extend" with "extend along `f`, then lift scalars".  Substituting it, the keystone's
hypothesis quantifies only over the chain isomorphism `e` of total complexes with its
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso` property, and over the chain map `w`
presenting the prefix with its transpose `t`.

So the equation the [stacks 068I] identification at a K-flat pair reduces to names exactly two
non-bookkeeping morphisms, and names each of them on both sides: the standard tensor base-change
isomorphism `e` of total complexes over `f`, and the scalar-lift comparison
`CochainComplex.DerivedTensor.extendScalarsLiftChainIso`.  Everything else in it is a specified
counit, a presentation isomorphism, a localized degreewise unit, or one of the two chosen
quasi-isomorphisms `q` and `n`.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is that the
equation the other hypothesis reduces to carries no existentially supplied chain map.

## Main results

* `Dualizing.tensorBaseChangeMor_eq_of_valued_prefix_explicit` -- the [stacks 068I]
  identification at a pair of K-flat complexes, from one equation naming the standard tensor
  base-change isomorphism and the explicit scalar-lift comparison, each on both sides.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/



@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.MonoidalCategory StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars
open CochainComplex.ExtendScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

/-- **Replacing the first factor of a four-factor composite.**

The slot is presented as a function `p` of the term being replaced, and the equation `hz` comes
first, so that the type of that term is known before `p` is elaborated; the remaining factors and
the right-hand side are left to unification. -/
private alias compCongrHeadT := Dualizing.comp_congr_head

/-- **Replacing the third factor of a four-factor composite.**

As `Dualizing.compCongrHeadT`, with the two factors before the slot given explicitly so that the
composite is parsed at the association the slot sits in. -/
private alias compCongrSlotT := Dualizing.comp_congr_slot

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **The keystone at a K-flat pair, in one vocabulary and with no existential data.**

`Dualizing.tensorBaseChangeMor_eq_of_valued_prefix_transported` with the chain map of
`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` replaced by the explicit
comparison `CochainComplex.DerivedTensor.extendScalarsLiftChainIso` it is equal to, by
`Stacks.DerivedHom.BaseChange.eq_extendScalarsLiftChainIso`.

The hypothesis names exactly two non-bookkeeping morphisms, each on both sides of the equation:
the standard tensor base-change isomorphism `e` of total complexes over `f`, and the explicit
scalar-lift comparison. -/
theorem tensorBaseChangeMor_eq_of_valued_prefix_explicit
    (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
      max uR uA uM + 1} f)
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
    let adj := derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,
      max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse :=
      _root_.Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
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
    let YP := ((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let _ZZ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj YP
    ∀ (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ)
      (I : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (q : (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
        f').obj J ⟶ I) [QuasiIso q]
      (n : X₃ ⟶ J) [QuasiIso n],
    letI : IsIso (T.alphaB.app K₀) :=
      _root_.Stacks.DerivedHom.BaseChange.isIso_extendScalarsCounit_app_of_kFlat f'
        T.B T.alphaB K₀
        (_root_.Stacks.DerivedHom.BaseChange.kFlat_scalarLift.{uR, max uR uA uM} R L hL)
    let eX := _root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max uR uA uM} R L
    let eY := _root_.Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift.{uR, uA, uM} f F
      comparison K L hK hL J n
    letI : IsIso (comparison.app (tensorComplex.{uR, max uR uA uM} K L)) :=
      CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
        comparison (tensorComplex.{uR, max uR uA uM} K L)
        (_root_.Stacks.DerivedHom.BaseChange.kFlat_tensorComplex.{uR, uA, uM} K L hK hL)
    letI : IsIso (comparison.app L) :=
      CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
        comparison L hL
    (∀ (hFL : IsKFlat.{uA, max uR uA uM}
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L))
      (e : tensorComplex.{uA, max uR uA uM}
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) ≅
        (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
          (tensorComplex.{uR, max uR uA uM} K L))
      (_he : IsTensorBaseChangeIso.{uR, uA, max uR uA uM} f K L e)
      ,
    let trV : F.obj (DerivedCategory.Q.obj K) ⟶
        dA.hom.obj (Opposite.op (F.obj (DerivedCategory.Q.obj L)), M) :=
      (dA.homEquiv (F.obj (DerivedCategory.Q.obj K)) (F.obj (DerivedCategory.Q.obj L))
            (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
              (tensorComplex.{uR, max uR uA uM} K L)))).symm
          (dA.tensor.map
                ((CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
                    ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
                      DerivedCategory (ModuleCat.{max uR uA uM} A) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
                    (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                        max uR uA uM} f).obj K),
                      DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                        max uR uA uM} f).obj L)))) ≫
              (derivedTensor_comparison.{uA, max uR uA uM} A
                  ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
                  ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFL).hom ≫
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
            max uR uA uM} A YP).inv) ≫
        S.functor.map (inv (comparison.app L))
      ∀ (w : ((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K ⟶
        (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj
          (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J))
      (t : (CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj
          (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⟶
        CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
          ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
            max uR uA uM} f').obj K₀) J)
      (_hw : w = ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
          (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
            max uR uA uM} f').map t)
      (_ha : E.functor.map (adj.unit.app (DerivedCategory.Q.obj K) ≫ U.map trV) ≫
              (E.functor.map (δ.hom.app (HA.obj
                      (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                        S.functor.obj M))) ≫
                  E.counitIso.hom.app (V.obj (HA.obj
                    (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                      S.functor.obj M)))) ≫
                V.map (HA.map (CategoryTheory.Prod.mkHom eFv.op (𝟙 (S.functor.obj M)))) ≫
                  (_root_.Stacks.DerivedHom.BaseChange.homRestrictTarget f' T.B).map
                      (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
                    V.map (_root_.Stacks.DerivedHom.BaseChange.homModelIso
                        ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                          max uR uA uM} f').obj K₀) J (asIso (T.alphaB.app K₀))
                        (Iso.refl (DerivedCategory.Q.obj J))).hom ≫
                      ((ModuleCat.restrictScalars.{max uR uA uM}
                            f').mapDerivedCategoryFactors.app
                        (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
                          ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                            max uR uA uM} f').obj K₀) J)).hom =
          (_root_.Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max uR uA uM} R K).hom ≫
            DerivedCategory.Q.map w),
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
                DerivedCategory.Q.map
                    (((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM}
                            f').mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
                        ((((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⊗ K₀) ≫
                      (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
                          max uR uA uM} f').map
                          (CochainComplex.DerivedTensor.transportedMonoidalInv.{uR, uA,
                            uM} f K L e ≫
                            DerivedInternalHom.Model.uncurry t) ≫
                        q) ≫
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
              (ComplexShape.up ℤ)).obj (tensorComplex.{uR, max uR uA uM} K L))) →
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) := by
  intro f' adj E S U V T d1 t1 HA dA W M K0 X3 YP ZZ J I hJ hI q hq n hn eX eY hunit
  have := hJ
  have := hI
  have := hq
  have := hn
  refine tensorBaseChangeMor_eq_of_valued_prefix_transported.{uR, uA, uM} f F comparison D K L
    hK hL J I q n ?_
  intro hFL e he c0 hc0 trV eFv w t hw ha
  have hc := _root_.Stacks.DerivedHom.BaseChange.eq_extendScalarsLiftChainIso.{uR, uA,
    uM} f L c0 hc0
  subst hc
  exact hunit hFL e he w t hw ha

end Dualizing

end
