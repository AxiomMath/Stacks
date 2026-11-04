module

public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorHom
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.KFlatKInjectiveJoin
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorCovariantKFlatLift

/-!
# The descended comparison of [stacks 0E1W], inverted, at the keystone's pair

This file values the inverse component of the change-of-rings comparison of [stacks 0E1W],
descended to `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso` at the scalar lift of the
ring map, at the pair `(Q L, F (Q K ⊗ᴸ_R Q L))` for K-flat complexes `K` and `L`. This factor
occurs in
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence`,
the value of the [stacks 0A63] transpose

`ψ_{Y, M} : (RHom_A(F Y, M))|_R ⊗ᴸ_R Y ⟶ M|_R`

of the inverse component, which is the remaining unknown of
`Dualizing.tensorBaseChangeMor_eq_of_kFlat_tensorTranspose`.

The transport `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_of_iso` carries
the representative comparison to that pair, along the presentations which
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_tensorKFlat` uses for the
forward component: the scalar lift `Stacks.DerivedHom.BaseChange.scalarLiftQObjIso` of `L`,
K-flat by `Stacks.DerivedHom.BaseChange.kFlat_scalarLift`, and the transport
`Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift` of the K-flat description of
`F (Q K ⊗ᴸ_R Q L)`. Composed with
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_changeOfRingsMap`, the
component becomes the two presentations, the two representation isomorphisms
`Stacks.DerivedHom.BaseChange.homModelIso`, two localization comparisons, and the canonical
chain-level map `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` of [stacks 0E1W],
uninverted, inside one fixed-universe transpose.

Both inputs are stated for two rings of one universe; they apply because `ULift R` and `ULift A`
both live in `max uR uA uM` together with their modules.

No tag is registered and no caveat is lifted. Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open: this values one
factor of the identification `hmu`, and says nothing about the comparison identity `h`, whose
frontier is `Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat` — the inverse
  component of the descended comparison at the keystone's slot, as the representative comparison
  conjugated by the two K-flat presentations.
* `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat_changeOfRingsMap` —
  **the same with the representative comparison at its floor**, mentioning only the chain-level
  map of [stacks 0E1W].

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 090Y](https://stacks.math.columbia.edu/tag/090Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

/-- **The inverse component of the descended comparison of [stacks 0E1W] at the keystone's
slot.**

The inverse component of the descended comparison
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso` at the scalar lift `f'` of the ring map,
at the contravariant object `E (Q L)` and the covariant object `S (F (Q K ⊗ᴸ_R Q L))`, is the
representative comparison at the scalar lift `K₀` of `L` and a K-injective resolution `J` of the
scalar lift of `A ⊗_R (K ⊗_R L)`, conjugated by the presentations `eX` and `eY` which
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_tensorKFlat` uses. -/
theorem modelRestrictScalarsNatIso_inv_app_tensorKFlat
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
    let eX := scalarLiftQObjIso.{uR, max uR uA uM} R L
    let eY := tensorKFlatKInjectiveLift.{uR, uA, uM} f F comparison K L hK hL J n
    (modelRestrictScalarsNatIso f' T.B T.alphaB).inv.app
        (Opposite.op (E.functor.obj (DerivedCategory.Q.obj L)), S.functor.obj M) =
      (homRestrictTarget f' T.B).map (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
        (derivedHomChangeOfRingsModelIso f' T.B T.alphaB K₀ J I q
            (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).inv ≫
          (homRestrictSource f').map (CategoryTheory.Prod.mkHom eX.hom.op eY.inv) := by
  intro F comparison hF K L hK hL E S f' T M X₃ K₀ J I hJ hI q hq n hn eX eY
  let := T.isLeftDerivedB
  exact modelRestrictScalarsNatIso_inv_app_of_iso f' T.B T.alphaB K₀ J I q
    (kFlat_scalarLift.{uR, max uR uA uM} R L hL) eX eY

/-- **The inverse component of the descended comparison at the keystone's slot, at its floor.**

`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat` with the
representative comparison replaced by its value
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_changeOfRingsMap`.

Every factor of the right-hand side is one of: the two K-flat presentations `eX` and `eY`, a
representation isomorphism `Stacks.DerivedHom.BaseChange.homModelIso`, a component of
`CategoryTheory.Functor.mapDerivedCategoryFactors`, the K-flat tensor comparison or the
K-injective representation of the fixed-universe derived internal Hom, or the canonical
chain-level map `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` of [stacks 0E1W],
uninverted and inside a single fixed-universe transpose. -/
theorem modelRestrictScalarsNatIso_inv_app_tensorKFlat_changeOfRingsMap
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
    let P := (CochainComplex.restrictScalarsLarge.{max uR uA uM, max uR uA uM, max uR uA uM}
      f').obj Z
    (modelRestrictScalarsNatIso f' T.B T.alphaB).inv.app
        (Opposite.op (E.functor.obj (DerivedCategory.Q.obj L)), S.functor.obj M) =
      (homRestrictTarget f' T.B).map (CategoryTheory.Prod.mkHom eX.inv.op eY.hom) ≫
        ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.map
              (homModelIso ((CochainComplex.extendScalarsLarge.{max uR uA uM, max uR uA uM,
                  max uR uA uM} f').obj K₀) J (asIso (T.alphaB.app K₀)) (Iso.refl _)).hom ≫
            ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app Z).hom ≫
              ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
                  (DerivedCategory.Q.obj K₀) (DerivedCategory.Q.obj I)).symm
                (((DerivedInternalHom.Model.adjunction
                      (ULift.{max uR uA uM} R)).tensorIso P K₀
                    (kFlat_scalarLift.{uR, max uR uA uM} R L hL)).hom ≫
                  DerivedCategory.Q.map
                    (DerivedInternalHom.Model.uncurry
                      (homComplexChangeOfRingsMap f' K₀ J I q)))) ≫
                ((DerivedInternalHom.Model.adjunction (ULift.{max uR uA uM} R)).homIso K₀ I).hom ≫
                  (homModelIso K₀ I (Iso.refl _)
                    ((ModuleCat.restrictScalars.{max uR uA uM}
                        f').mapDerivedCategoryFactors.app J ≪≫
                      @asIso _ _ _ _ (DerivedCategory.Q.map q)
                        ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).inv) ≫
          (homRestrictSource f').map (CategoryTheory.Prod.mkHom eX.hom.op eY.inv) := by
  intro F comparison hF K L hK hL E S f' T M X₃ K₀ J I hJ hI q hq n hn eX eY Z P
  let := T.isLeftDerivedB
  let : IsIso (T.alphaB.app K₀) :=
    isIso_extendScalarsCounit_app_of_kFlat f' T.B T.alphaB K₀
      (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
  let := quasiIso_homComplexChangeOfRingsMap_of_kFlat f' K₀ J I q T.B T.alphaB
    (kFlat_scalarLift.{uR, max uR uA uM} R L hL)
  refine (modelRestrictScalarsNatIso_inv_app_tensorKFlat.{uR, uA, uM} f F comparison K L hK hL
    J I q n).trans ?_
  rw [_root_.Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_changeOfRingsMap
    f' T.B T.alphaB K₀ J I q (kFlat_scalarLift.{uR, max uR uA uM} R L hL)]

end Stacks.DerivedHom.BaseChange

end
