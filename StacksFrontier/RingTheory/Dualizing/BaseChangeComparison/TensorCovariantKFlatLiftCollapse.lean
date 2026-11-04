module

public import StacksFrontier.Homology.HomComplex.Evaluation.UncurryTranspose
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorCovariantKFlatLiftInverse

/-!
# The content factor of [stacks 0E1W] with its transpose cancelled

`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat_changeOfRingsMap`
writes the inverse component of the descended comparison of [stacks 0E1W] at the keystone's slot
with the chain-level map `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` appearing
*uncurried inside a fixed-universe transpose*: three of its factors are the inverse transpose of
the K-flat tensor comparison followed by the localized [stacks 0A63] uncurrying of that chain map,
and then the K-injective Hom comparison.

Those three are one factor.  By
`StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry` the transpose of the
localized chain map followed by the *inverse* Hom comparison is the K-flat comparison followed by
the localized uncurrying, so reading that identity backwards and cancelling the comparison against
its inverse leaves exactly `DerivedCategory.Q.map` of the chain map.

That step is available here because all three objects of the transpose --
`Q P`, `Q K₀`, `Q I` -- are localizations of complexes, with `K₀` K-flat and `I` K-injective:
`StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry` asks for exactly that, and
the obstruction recorded in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeTensorTranspose` concerns
the *outer* transpose of the keystone, whose three objects are not of that form.

**What is not done here.**  Nothing is registered and no caveat is lifted.  The [stacks 068I]
identification stays open, and the companion hypothesis `h` of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` is untouched; its frontier
remains `Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What changes is that the one
chain map the [stacks 0E1W] side of the keystone carries now occurs as a plain
`DerivedCategory.Q.map`, with no transpose and no uncurrying around it -- which is the form in
which it can be compared with `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, the one
chain map the [stacks 068I] side carries.

## Main results

* `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat_q_map` -- the
  inverse component of the descended comparison at the keystone's slot, with the chain-level map
  of [stacks 0E1W] localized and nothing else around it.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

/-- **The inverse component of the descended comparison of [stacks 0E1W] at the keystone's slot,
with the chain-level map localized and nothing around it.**

`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat_changeOfRingsMap`
with its three middle factors -- the inverse transpose of the K-flat tensor comparison followed by
the localized uncurrying of `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap`, and then
the K-injective Hom comparison -- replaced by the single factor they compose to,
`DerivedCategory.Q.map` of that chain map.

What remains in the value is: the two K-flat presentations `eX` and `eY` through the two
`Stacks.DerivedHom.BaseChange.homRestrictTarget`/`…homRestrictSource` functors, two
`Stacks.DerivedHom.BaseChange.homModelIso` representation isomorphisms, one component of
`CategoryTheory.Functor.mapDerivedCategoryFactors`, and the localization of the chain-level map of
[stacks 0E1W], uninverted. -/
theorem modelRestrictScalarsNatIso_inv_app_tensorKFlat_q_map
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
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let M := F.obj ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))
    let X₃ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
            (tensorComplex.{uR, max uR uA uM} K L))
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
    (modelRestrictScalarsNatIso f' T.B T.alphaB).inv.app
        (Opposite.op (E.functor.obj (DerivedCategory.Q.obj L)), S.functor.obj M) =
      (homRestrictTarget f' T.B).map (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
        ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.map
              (homModelIso ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                  max uR uA uM} f').obj K₀) J (asIso (T.alphaB.app K₀)) (Iso.refl _)).hom ≫
            ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app Z).hom ≫
              DerivedCategory.Q.map (homComplexChangeOfRingsMap f' K₀ J I q) ≫
                (homModelIso K₀ I (Iso.refl _)
                  ((ModuleCat.restrictScalars.{max uR uA uM}
                      f').mapDerivedCategoryFactors.app J ≪≫
                    @asIso _ _ _ _ (DerivedCategory.Q.map q)
                      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).inv) ≫
          (homRestrictSource f').map (CategoryTheory.Prod.mkHom eX.hom.op eY.inv) := by
  intro F comparison hF K L hK hL E S f' T M X₃ K₀ J I hJ hI q hq n hn eX eY Z
  have := hF
  have := hJ
  have := hI
  have := hq
  have := hn
  have hK₀ := kFlat_scalarLift.{uR, max uR uA uM} R L hL
  let := T.isLeftDerivedB
  let : IsIso (T.alphaB.app K₀) :=
    isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB K₀ hK₀
  let := quasiIso_homComplexChangeOfRingsMap_of_kFlat f' K₀ J I q T.B T.alphaB hK₀
  refine (modelRestrictScalarsNatIso_inv_app_tensorKFlat_changeOfRingsMap.{uR, uA, uM} f F
    comparison K L hK hL J I q n).trans ?_
  congr 4
  exact DerivedInternalHom.Model.homEquiv_symm_tensorIso_uncurry_comp_homIso_assoc
    ((CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM,
      max uR uA uM} f').obj Z) K₀ I hK₀ (homComplexChangeOfRingsMap f' K₀ J I q) _

end Stacks.DerivedHom.BaseChange

end
