module

public import StacksFrontier.Homology.Tor.BaseChangeTensorMonoidalTransport
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeMonoidalChainLevel

/-!
# The keystone at a K-flat pair, with both monoidality comparisons in one vocabulary

`Dualizing.tensorBaseChangeMor_eq_of_monoidal_chain_level` reduces the [stacks 068I]
identification at a pair of K-flat complexes to one equation whose [stacks 0GMT] side carries the
inverse of `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` over the *lifted* ring map, at
the pair of scalar lifts, and whose [stacks 068I] side -- through the hypothesis `ha` pinning the
prefix, and `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` -- carries the standard tensor
base-change isomorphism of total complexes over `f` itself, at *independent* ring universes.
Those are two different comparisons in two different vocabularies, and
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom`, which
would identify them, exists only where everything shares one universe.

`CochainComplex.DerivedTensor.extendScalarsMonoidalIso_inv_eq_transport` closes that gap: it
expresses the lifted monoidality isomorphism's inverse as
`CochainComplex.DerivedTensor.transportedMonoidalInv`, built from the standard comparison over
`f` and the two scalar-lift comparisons.  This file substitutes that value into the keystone.

So the remaining content of the [stacks 068I] identification at a K-flat pair is an equation in
which **only one** monoidality comparison occurs, the one over `f` at independent universes, and
it occurs on both sides: on the [stacks 0GMT] side through
`CochainComplex.DerivedTensor.transportedMonoidalInv`, and on the [stacks 068I] side through the
hypothesis `_ha`.  The chain isomorphism is the same one on both sides -- it is quantified over
once, together with its `CochainComplex.DerivedTensor.IsTensorBaseChangeIso` property -- and the
quantifier costs nothing, because `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` produces such an
isomorphism at a K-flat pair and `CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq` makes
any two of them equal.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is that the
keystone's two sides no longer carry two different monoidality comparisons.

## Main results

* `Dualizing.tensorBaseChangeMor_eq_of_transported_monoidal` -- the [stacks 068I] identification
  at a pair of K-flat complexes, from one equation in which the only monoidality comparison is
  the standard one over `f`, carried on the [stacks 0GMT] side by
  `CochainComplex.DerivedTensor.transportedMonoidalInv`.

## Implementation notes

The transported inverse is substituted under its own name
`CochainComplex.DerivedTensor.transportedMonoidalInv` rather than written out.  Composing the
five nested comparisons it is built from with the uncurried transpose of the prefix exceeds the
elaboration budget of this declaration when the composite is written out, because unifying the
target of the fifth comparison with the source of that transpose unfolds all five; the declared
signature of the named definition makes the same unification immediate.

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

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **The keystone at a K-flat pair, with both monoidality comparisons in one vocabulary.**

`Dualizing.tensorBaseChangeMor_eq_of_monoidal_chain_level` with the inverse of
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` over the lifted ring map replaced, by
`CochainComplex.DerivedTensor.extendScalarsMonoidalIso_inv_eq_transport`, by
`CochainComplex.DerivedTensor.transportedMonoidalInv` at a chain isomorphism `ee` of total
complexes over `f` satisfying `CochainComplex.DerivedTensor.IsTensorBaseChangeIso`.

The extra data `ee` and `_hee` cost nothing:
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` produces such an isomorphism at a K-flat pair, and
that is how they are supplied here.  What is gained is that the comparison on the [stacks 0GMT]
side of the equation is now the same comparison, at the same universes, as the one the
hypothesis `_ha` carries on the [stacks 068I] side. -/
theorem tensorBaseChangeMor_eq_of_transported_monoidal
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
    let adj' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse :=
      _root_.Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp adj').leftAdjointUniq ((adj.comp S.toAdjunction).ofNatIsoRight δ)
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
    (∀ (ee : tensorComplex.{uA, max uR uM}
          ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
          ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L) ≅
        (extensionOfScalarsCochain.{uR, uA, uM} f).obj (tensorComplex.{uR, max uA uM} K L))
      (_hee : IsTensorBaseChangeIso.{uR, uA, uM} f K L ee)
      (w : ((ModuleCat.restrictScalars.{max uR uA uM}
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
      (_ha : E.functor.map (adj.unit.app (DerivedCategory.Q.obj K) ≫
                U.map ((dA.homEquiv (F.obj (DerivedCategory.Q.obj K))
                    (F.obj (DerivedCategory.Q.obj L)) M).symm
                  (tensorBaseChangeMor.{uR, uA, uM} f F comparison D
                    (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)))) ≫
              (E.functor.map (δ.hom.app (HA.obj
                      (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                        S.functor.obj M))) ≫
                  E.counitIso.hom.app (V.obj (HA.obj
                    (Opposite.op (S.functor.obj (F.obj (DerivedCategory.Q.obj L))),
                      S.functor.obj M)))) ≫
                V.map (HA.map (CategoryTheory.Prod.mkHom
                      (eF.hom.app (DerivedCategory.Q.obj L)).op (𝟙 (S.functor.obj M)))) ≫
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
                          (transportedMonoidalInv.{uR, uA, uM} f K L ee ≫
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
  intro f' adj E S U V T adj' d1 t1 eF HA dA W M K0 X3 J I hJ hI q hq n hn eX eY hunit
  have := hJ
  have := hI
  have := hq
  have := hn
  refine tensorBaseChangeMor_eq_of_monoidal_chain_level.{uR, uA, uM} f F comparison D K L hK hL
    J I q n ?_
  intro w t hw ha
  obtain ⟨hFL, ee, hee, _⟩ :=
    tensorBaseChangeMor_comp_eq_q_obj.{uR, uA, uM} f D F comparison K L hK hL
  rw [extendScalarsMonoidalIso_inv_eq_transport.{uR, uA, uM} f K L hee]
  exact hunit ee hee w t hw ha

end Dualizing

end
