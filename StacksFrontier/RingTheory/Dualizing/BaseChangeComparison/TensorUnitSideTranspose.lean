module

public import StacksFrontier.CategoryTheory.Equivalence.InverseMapTranspose
public import StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionTransport
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.UnitTensorKFlatValue

/-!
# The [stacks 0GMT] side of the keystone, transposed back and valued

The keystone's residual equation `hrhs` of
`Dualizing.tensorBaseChangeMor_eq_of_prefix_chain_map` has, on the [stacks 0GMT] side, the
composite `E.counitIso.inv.app (E K ⊗ᴸ E L) ≫ E.functor.map (unit.app W)`: the inverse counit of
the scalar equivalence at the fixed-universe tensor product of the two lifted classes, followed
by the scalar lift of the unit of [stacks 0GMT] at `W = Q K ⊗ᴸ_R Q L`.

That shape was produced by `Dualizing.eq_derivedTensorBaseChange_iff_scalarLift`, which
transposed the obligation out of `D(R)` and into `D(ULift R)` with
`CategoryTheory.Equivalence.inverse_map_comp_comp_unitIso_inv_eq_iff`, because the chain-level
value of the *other* side lives there.  The price is that the inverse counit is read at
`E K ⊗ᴸ E L`, an object which is not presented as the class of a complex, and no value for it is
available: the evaluation lemmas for the counits of the scalar equivalence all need their
argument presented as a class.

This file transposes that one composite back.  The gain is that the unit of [stacks 0GMT] at `W`
*is* valued -- by
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsAdjunction_unit_app_tensor_kFlat`, at a
K-flat pair, as the canonical tensor comparison conjugating the degreewise unit of extension of
scalars -- so after the transposition the [stacks 0GMT] side carries no counit, no unit of the
scalar equivalence and no [stacks 0GMT] unit: only the canonical tensor comparison, a localized
chain map, and the degreewise comparison of the chosen model.

What stays on the other side is `E.inverse` of the [stacks 068I] side.  That is the trade: the
equation is read in `D(R)`, where the [stacks 0GMT] side is computed and the [stacks 068I] side
is not, rather than in `D(ULift R)`, where the [stacks 068I] side is computed and the
[stacks 0GMT] side is not.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `Stacks.DerivedHom.BaseChange.counitIso_inv_comp_functor_map_unit_tensor_eq_iff` -- the
  [stacks 0GMT] side of the keystone's residual equation equals a given morphism exactly when the
  transpose of that morphism is the value of the unit of [stacks 0GMT] at `W`.
* `Stacks.DerivedHom.BaseChange.inverse_map_comp_transportedIso_inv_comp_unitIso_inv` -- the
  transported restriction comparison `τ` transposes away: the transpose of anything followed by
  its inverse component is the transpose alone, followed by the inverse component of `δ` and the
  inverse unit of the scalar lift over `A`.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **The [stacks 0GMT] side of the keystone's residual equation, transposed and valued.**

For a K-flat pair `K`, `L` and any morphism `rhs` out of the fixed-universe tensor product of the
two lifted classes, the [stacks 0GMT] side of the keystone's residual equation is `rhs` exactly
when the transpose of `rhs` across the scalar equivalence is the value of the unit of
[stacks 0GMT] at `W = Q K ⊗ᴸ_R Q L`: the canonical tensor comparison, then the degreewise unit of
extension of scalars read through `CategoryTheory.Functor.mapDerivedCategoryFactors` and back
along the degreewise comparison of the chosen model, then the restriction of `F` applied to the
inverse tensor comparison.

The left-hand side is the shape the keystone's `hrhs` has, with its uncomputable inverse counit at
an object that is not a class; the right-hand side has no counit, no unit of the scalar
equivalence and no [stacks 0GMT] unit in it. -/
public theorem counitIso_inv_comp_functor_map_unit_tensor_eq_iff
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    letI : IsIso (comparison.app (tensorComplex.{uR, max uR uA uM} K L)) :=
      isIso_comparison_app_of_kFlat.{uR, uA, uM} f F comparison
        (tensorComplex.{uR, max uR uA uM} K L)
        (kFlat_tensorComplex.{uR, uA, uM} K L hK hL)
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let W := (derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)
    ∀ (rhs : (DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).obj
          (E.functor.obj (DerivedCategory.Q.obj K),
            E.functor.obj (DerivedCategory.Q.obj L)) ⟶ E.functor.obj (U.obj (F.obj W))),
    (E.counitIso.inv.app ((DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)).obj
              (E.functor.obj (DerivedCategory.Q.obj K),
                E.functor.obj (DerivedCategory.Q.obj L))) ≫
          E.functor.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F
            comparison).unit.app W) =
        rhs) ↔
      E.inverse.map rhs ≫ E.unitIso.inv.app (U.obj (F.obj W)) =
        (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom ≫
          (DerivedCategory.Q.map
              (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).unit.app (tensorComplex.{uR, max uR uA uM} K L)) ≫
            (ModuleCat.restrictScalars.{max uR uA uM, uR,
                uA} f).mapDerivedCategoryFactors.inv.app
                (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj (tensorComplex.{uR, max uR uA uM} K L)) ≫
              (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
                (inv (comparison.app (tensorComplex.{uR, max uR uA uM} K L)))) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
            (F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).inv) := by
  intro E U W rhs
  have : IsIso (comparison.app (tensorComplex.{uR, max uR uA uM} K L)) :=
    isIso_comparison_app_of_kFlat.{uR, uA, uM} f F comparison
      (tensorComplex.{uR, max uR uA uM} K L)
      (kFlat_tensorComplex.{uR, uA, uM} K L hK hL)
  refine eq_comm.trans ((E.inverse_map_comp_unitIso_inv_eq_iff rhs
    ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app W)).symm.trans ?_)
  rw [derivedExtensionScalarsAdjunction_unit_app_tensor_kFlat.{uR, uA, uM} f F comparison
    K L hK hL]

/-- **The transported restriction comparison, transposed away.**

The transpose across the scalar equivalence of any morphism into `V (S M)` followed by the inverse
component of the transported restriction comparison `τ` is the transpose of the morphism alone,
followed by the inverse component of `δ` and the restriction along `f` of the inverse unit of the
scalar lift over `A`. -/
public theorem inverse_map_comp_transportedIso_inv_comp_unitIso_inv
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (M : DerivedCategory (ModuleCat.{max uR uA uM} A)) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
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
    ∀ {Z : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))}
      (x : Z ⟶ V.obj (S.functor.obj M)),
    E.inverse.map (x ≫ τ.inv.app M) ≫ E.unitIso.inv.app (U.obj M) =
      E.inverse.map x ≫ δ.inv.app (S.functor.obj M) ≫ U.map (S.unitIso.inv.app M) := by
  intro f' E S U V δ τ Z x
  rw [E.inverse.map_comp, Category.assoc]
  exact congrArg (fun z => E.inverse.map x ≫ z)
    ((E.inverse_map_comp_unitIso_inv_eq_iff (τ.inv.app M)
      (δ.inv.app (S.functor.obj M) ≫ U.map (S.unitIso.inv.app M))).mpr
        (scalarRestrictionTransportedIso_inv_app.{uR, uA, uM} f M))

end Stacks.DerivedHom.BaseChange

end
