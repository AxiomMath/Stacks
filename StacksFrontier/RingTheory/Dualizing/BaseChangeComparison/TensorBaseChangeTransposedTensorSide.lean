module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangePrefixExists
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorUnitSideTranspose

/-!
# The keystone at a K-flat pair, with the [stacks 0GMT] side valued

`Dualizing.tensorBaseChangeMor_eq_of_uncurried_tensor_side` reduces the [stacks 068I]
identification at a pair of K-flat complexes to a single equation whose [stacks 0GMT] side is
`E.counitIso.inv.app (E K ⊗ᴸ E L) ≫ E.functor.map (unit.app W)`.  That side is not computable as it
stands: the inverse counit of the scalar equivalence is read at an object which is not presented
as the class of a complex, and every evaluation lemma for those counits needs its argument so
presented.

`Stacks.DerivedHom.BaseChange.counitIso_inv_comp_functor_map_unit_tensor_eq_iff` transposes that
composite back across the scalar equivalence, where
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsAdjunction_unit_app_tensor_kFlat` values the
unit of [stacks 0GMT] at `Q K ⊗ᴸ_R Q L` outright.  This file performs the substitution, giving the
keystone at a K-flat pair in the shape where the [stacks 0GMT] side is fully evaluated.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `Dualizing.tensorBaseChangeMor_eq_of_transposed_tensor_side` -- the [stacks 068I] identification
  at a K-flat pair from one equation in which no counit and no unit of either scalar equivalence
  occurs.
* `Dualizing.tensorBaseChangeMor_eq_of_degreewise_unit` -- the same conjugated by the canonical
  presentation of the derived tensor product and pushed along the degreewise comparison, so that
  the [stacks 0GMT] side is the localization of the degreewise unit of extension of scalars and
  nothing else.
* `Dualizing.tensorBaseChangeMor_eq_iff_degreewise_unit` -- **the same as an equivalence**, with
  no K-injective resolution, no chain map presenting the prefix and no quasi-isomorphism among
  its data: the [stacks 068I] identification at a K-flat pair holds exactly when the transpose
  of the [stacks 068I] side is the canonical tensor comparison conjugating the degreewise unit of
  extension of scalars.

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
/-- **The [stacks 068I] identification at a K-flat pair, from the transposed [stacks 0GMT]
side.**

`Dualizing.tensorBaseChangeMor_eq_of_uncurried_tensor_side` with its one hypothesis transposed
back across the scalar equivalence by
`Stacks.DerivedHom.BaseChange.counitIso_inv_comp_functor_map_unit_tensor_eq_iff`, so that the
[stacks 0GMT] side is the *value* of the unit of [stacks 0GMT] at `Q K ⊗ᴸ_R Q L` rather than the
inverse counit of the scalar equivalence at an object which is not a class.

The remaining obligation is therefore: for every chain map `w` presenting the [stacks 068I]
prefix, the transpose across the scalar equivalence of the [stacks 068I] side -- the derived
tensor bifunctor at the two scalar-lift presentations, the K-flat representation of the derived
tensor product, the localized uncurrying of `w` followed by the chain-level map of
[stacks 0E1W], and the tail -- is the canonical tensor comparison conjugating the degreewise unit
of extension of scalars.

Every factor of the right-hand side is either the canonical tensor comparison of [stacks 0A63], a
localized chain map, or the degreewise comparison of the chosen model; no counit and no unit of
either scalar equivalence occurs in it.

The quantifier over `w` costs nothing, for the reason recorded in
`Dualizing.tensorBaseChangeMor_eq_of_uncurried_tensor_side`: `_ha` determines `w` up to homotopy
and the conclusion depends on `w` only through its localization. -/
theorem tensorBaseChangeMor_eq_of_transposed_tensor_side
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
    (∀ (w : ((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K ⟶
        (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj
          (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J))
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
      E.inverse.map ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).tensor.map
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
                DerivedCategory.Q.map (DerivedInternalHom.Model.uncurry
                    (w ≫ _root_.Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f' K₀ J I
                      q)) ≫
                  (((ModuleCat.restrictScalars.{max uR uA uM}
                              f').mapDerivedCategoryFactors.app J ≪≫
                          @asIso _ _ _ _ (DerivedCategory.Q.map q)
                            ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2
                              inferInstance)).inv ≫
                    V.map eY.inv ≫ τ.inv.app M)) ≫
          E.unitIso.inv.app (U.obj M) =
        (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom ≫
            (DerivedCategory.Q.map
                (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
                  (ComplexShape.up ℤ)).unit.app (tensorComplex.{uR, max uR uA uM} K L)) ≫
              (ModuleCat.restrictScalars.{max uR uA uM, uR,
                  uA} f).mapDerivedCategoryFactors.inv.app
                  (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj (tensorComplex.{uR, max uR uA uM} K L)) ≫
                (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
                  (CategoryTheory.inv
                    (comparison.app (tensorComplex.{uR, max uR uA uM} K L)))) ≫
            (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
              (F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).inv)) →
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) := by
  intro f' adj E S U V T adj' δ τ eF HA dA W M K₀ X₃ J I _ _ q _ n _ eX eY hrhs
  refine tensorBaseChangeMor_eq_of_uncurried_tensor_side.{uR, uA, uM} f F comparison D K L hK hL
    J I q n (fun w ha => ?_)
  exact (_root_.Stacks.DerivedHom.BaseChange.counitIso_inv_comp_functor_map_unit_tensor_eq_iff.{uR,
    uA, uM} f F comparison K L hK hL _).mpr (hrhs w ha)

/-- **Conjugating an equation by three isomorphisms.**

An equation whose right-hand side is an isomorphism, two factors, the inverse of a second
isomorphism and the inverse of a third, read with the two factors alone on one side. -/
private theorem eq_comp_comp_inv_iff {C : Type*} [Category C] {W W' Y₀ Y₁ Y₂ Y₃ : C}
    (i : W ≅ W') (k : Y₂ ≅ Y₁) (j : Y₃ ≅ Y₂)
    {X : W ⟶ Y₃} {h₁ : W' ⟶ Y₀} {h₂ : Y₀ ⟶ Y₁} :
    X = i.hom ≫ (h₁ ≫ h₂ ≫ k.inv) ≫ j.inv ↔
      (i.inv ≫ X ≫ j.hom) ≫ k.hom = h₁ ≫ h₂ := by
  constructor
  · rintro rfl
    simp
  · intro h
    rw [← Category.assoc h₁ h₂ k.inv, ← h]
    simp

include hF in
/-- **The keystone at a K-flat pair, as an equation between two localized chain maps.**

`Dualizing.tensorBaseChangeMor_eq_of_transposed_tensor_side` conjugated by the canonical
presentation `CochainComplex.DerivedTensor.derivedTensor_comparison` of the derived tensor
product and pushed along the degreewise comparison of the chosen model.

What is left is: for every chain map `w` presenting the [stacks 068I] prefix, the [stacks 068I]
side -- transposed across the scalar equivalence, read between the presentation of the derived
tensor product and the comparison of the chosen model -- is the localization of the degreewise
unit of the extension--restriction adjunction along `f` at the total tensor complex, followed by
the factorization of derived restriction.

**Both sides are now explicit.**  The right-hand side is a localized chain map and one component
of `CategoryTheory.Functor.mapDerivedCategoryFactors`; the left-hand side is the derived tensor
bifunctor at two presentations, the K-flat representation of the derived tensor product, a
localized chain map, the presentations of `J` and of the lifted tensor product, and the
transported restriction comparison -- all of them either localized chain maps or comparisons
between two presentations of one object.  No counit or unit of either scalar equivalence and no
unit or counit of [stacks 0GMT] occurs on either side.

The conjugation is by isomorphisms only: the presentation of the derived tensor product is an
isomorphism, and the degreewise comparison is invertible at the total tensor complex because that
complex is K-flat. -/
theorem tensorBaseChangeMor_eq_of_degreewise_unit
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
    (∀ (w : ((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K ⟶
        (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM} f').obj
          (CochainComplex.HomComplexR (ULift.{max uR uA uM} A)
            ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
              max uR uA uM} f').obj K₀) J))
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
                DerivedCategory.Q.map (DerivedInternalHom.Model.uncurry
                    (w ≫ _root_.Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f' K₀ J I
                      q)) ≫
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
  intro f' adj E S U V T adj' δ τ eF HA dA W M K₀ X₃ J I _ _ q _ n _ eX eY hunit
  have : IsIso (comparison.app (tensorComplex.{uR, max uR uA uM} K L)) :=
    CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
      comparison (tensorComplex.{uR, max uR uA uM} K L)
      (_root_.Stacks.DerivedHom.BaseChange.kFlat_tensorComplex.{uR, uA, uM} K L hK hL)
  refine tensorBaseChangeMor_eq_of_transposed_tensor_side.{uR, uA, uM} f F comparison D K L hK hL
    J I q n (fun w ha => ?_)
  exact (eq_comp_comp_inv_iff (derivedTensor_comparison.{uR, max uR uA uM} R K L hL)
    (U.mapIso (asIso (comparison.app (tensorComplex.{uR, max uR uA uM} K L))))
    (U.mapIso (F.mapIso (derivedTensor_comparison.{uR, max uR uA uM} R K L hL)))).mpr
      (hunit w ha)

include hF in
/-- **The keystone at a K-flat pair, as an iff whose [stacks 0GMT] side is the degreewise
unit.**

`Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftEvaluation` at the classes of two K-flat
complexes, with its right-hand equation transposed back across the scalar equivalence by
`Stacks.DerivedHom.BaseChange.counitIso_inv_comp_functor_map_unit_tensor_eq_iff`.

The [stacks 068I] identification at the pair holds exactly when the transpose across the scalar
equivalence of the [stacks 068I] side -- the derived tensor bifunctor applied to the transposed
unit of [stacks 0GMT] carried through the prefix `v ≫ p`, paired with the presentation `lam`,
followed by the pairing morphism `c` and the tail `rho` -- is the canonical tensor comparison of
[stacks 0A63] conjugating the degreewise unit of extension of scalars along `f` at the total
tensor complex.  Neither side carries a counit of the scalar equivalence: the [stacks 0GMT] side
is a localized chain map between two comparisons.

Unlike `Dualizing.tensorBaseChangeMor_eq_of_degreewise_unit` this is an equivalence, and it needs
no K-injective resolutions, no chain map presenting the prefix and no quasi-isomorphisms: the data
is the same `P`, `P'`, `L'`, `M'`, `v`, `p`, `lam`, `rho`, `c` and presentation hypothesis `_hb`
that `Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftEvaluation` takes, and
`Dualizing.exists_scalarLiftEvaluationPresentation` supplies all of it. -/
theorem tensorBaseChangeMor_eq_iff_degreewise_unit
    (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
      max uR uA uM + 1} f)
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    letI : IsIso (comparison.app (tensorComplex.{uR, max uR uA uM} K L)) :=
      CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM} f F
        comparison (tensorComplex.{uR, max uR uA uM} K L)
        (_root_.Stacks.DerivedHom.BaseChange.kFlat_tensorComplex.{uR, uA, uM} K L hK hL)
    let X := DerivedCategory.Q.obj K
    let Y := DerivedCategory.Q.obj L
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let dR := derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R
    let dA := derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A
    let W := dR.tensor.obj (X, Y)
    let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
    let TR := DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)
    ∀ (P P' L' M' : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)))
      (v : E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) ⟶ P)
      (p : P ⟶ P') (lam : E.functor.obj Y ⟶ L')
      (rho : M' ⟶ E.functor.obj (U.obj (F.obj W))) (c : TR.obj (P', L') ⟶ M')
      (_hb : dR.homEquiv (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))) Y
            (U.obj (F.obj W))
            ((_root_.Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA,
              uM} f F comparison).inv.app (Opposite.op Y, F.obj W)) =
          E.inverse.map
              (TR.map
                  ((v, 𝟙 (E.functor.obj Y)) :
                    ((E.functor.obj (U.obj (dA.hom.obj (Opposite.op (F.obj Y), F.obj W))),
                        E.functor.obj Y) :
                      DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
                      (P, E.functor.obj Y)) ≫
                DerivedInternalHom.Model.homEquiv P (E.functor.obj Y)
                  (E.functor.obj (U.obj (F.obj W)))
                  (p ≫ (DerivedInternalHom.Model.homEquiv P' L' M').symm c ≫
                    HR.map ((lam.op, rho) :
                      ((Opposite.op L', M') :
                        (DerivedCategory (ModuleCat.{max uR uA uM}
                          (ULift.{max uR uA uM} R)))ᵒᵖ ×
                          DerivedCategory (ModuleCat.{max uR uA uM}
                            (ULift.{max uR uA uM} R))) ⟶
                        (Opposite.op (E.functor.obj Y),
                          E.functor.obj (U.obj (F.obj W)))))) ≫
            E.unitIso.inv.app (U.obj (F.obj W))),
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
          derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      E.inverse.map (TR.map ((E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
                comparison).unit.app X ≫
                U.map ((dA.homEquiv (F.obj X) (F.obj Y) (F.obj W)).symm
                  (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y))) ≫ v ≫ p, lam) :
            ((E.functor.obj X, E.functor.obj Y) :
              DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) ×
                DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))) ⟶
              (P', L')) ≫ c ≫ rho) ≫
          E.unitIso.inv.app (U.obj (F.obj W)) =
        (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom ≫
          (DerivedCategory.Q.map
              (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).unit.app (tensorComplex.{uR, max uR uA uM} K L)) ≫
            (ModuleCat.restrictScalars.{max uR uA uM, uR,
                uA} f).mapDerivedCategoryFactors.inv.app
                (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj (tensorComplex.{uR, max uR uA uM} K L)) ≫
              (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
                (CategoryTheory.inv
                  (comparison.app (tensorComplex.{uR, max uR uA uM} K L)))) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
            (F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).inv) := by
  intro X Y E U dR dA W HR TR P P' L' M' v p lam rho c hb
  refine (tensorBaseChangeMor_eq_iff_scalarLiftEvaluation.{uR, uA, uM} f F comparison D X Y
    P P' L' M' v p lam rho c hb).trans (eq_comm.trans ?_)
  exact _root_.Stacks.DerivedHom.BaseChange.counitIso_inv_comp_functor_map_unit_tensor_eq_iff.{uR,
    uA, uM} f F comparison K L hK hL _

end Dualizing

end
