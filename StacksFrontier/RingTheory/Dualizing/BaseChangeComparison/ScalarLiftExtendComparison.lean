module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ScalarLiftUnitChain
public import StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionTransportPrefix
public import StacksFrontier.CategoryTheory.Adjunction.UniqueCompTranspose
import all StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionComponent

/-!
# The comparison of [stacks 0E1W] against the degreewise comparison of the chosen model

The fourth factor of [stacks 0E1W],
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso`, compares the two composite left
adjoints `E.functor ⋙ T.B` and `F ⋙ S.functor`: lift scalars and then extend along the lifted
ring map, against extend along `f` and then lift scalars.  Its forward component at the class of
a complex `L` is a morphism out of `T.B (E.functor (Q L))`, and the only handle on such a
morphism is its transpose under the derived extension--restriction adjunction over the lifted
rings.

This file evaluates that component, read between the two scalar-lift presentations and followed
by the degreewise comparison `comparison` of the chosen model `F`, against the specified counit
`T.alphaB` of the canonical model over the lifted rings.  The answer is the chain map
`Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain`, exhibited by
`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` as a transpose; so the
comparison *is* the lifted degreewise comparison, and no component of [stacks 0E1W] survives in
the identity.

Neither side needs any K-flatness of `L`.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsAdjunction_unit_comp_scalarLiftTransport`
  -- the transposed unit of [stacks 0GMT] at a class, followed by the two bookkeeping factors
  over `A`, is a localized chain map.
* `Stacks.DerivedHom.BaseChange.scalarLiftExtendTransposeValue` -- the value of the whole left
  transpose: the scalar lift over `R` of that chain map, collapsed by
  `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q_comp_counit`.
* `Stacks.DerivedHom.BaseChange.liftedExtensionUnit_comp_alphaB_eq` -- the value of the right
  transpose: the unit of [stacks 0GMT] over the lifted rings followed by `T.alphaB` and the
  transpose of `Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain`.
* `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app_comp_comparison` -- **the
  valuation**: the two transposes agree, so the component of [stacks 0E1W] against the two
  presentations and `comparison` is `T.alphaB` followed by the transpose.
* `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app_comp_comparison_eq` -- the
  same with both presentations moved to the right-hand side, which is the form a consumer uses.
* `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app_of_kFlat` -- at a K-flat
  complex the degreewise comparison is invertible, so the component itself is valued and no
  `CategoryTheory.Adjunction.leftAdjointUniq` is left in it.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open Stacks.DerivedHom.ScalarTransportedInternalHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- **The transposed unit of [stacks 0GMT] at a class, with the bookkeeping over `A`.**

The unit of [stacks 0GMT] along `f` at the class of `L`, followed by the restriction along `f` of
the transpose under the scalar lift over `A` of the degreewise comparison of the chosen model
(read into the scalar-lift presentation), and then by the two factors that take the twice
restricted class back to a class of complexes, is the localization of a chain map: the degreewise
unit of the extension--restriction adjunction along `f`, followed by the restriction along `f` of
the inverse counit `Stacks.DerivedHom.BaseChange.scalarLiftCounitInv` of the equivalence of
complexes over `A`.

Only three facts are used: naturality of the unit of the scalar lift over `A`,
`Stacks.DerivedHom.BaseChange.scalarEquivalence_unitIso_hom_app_Q_comp`, and
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app`.  Nothing is
assumed of `L`. -/
public theorem derivedExtensionScalarsAdjunction_unit_comp_scalarLiftTransport :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ),
    let adj := derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison
    let S := scalarEquivalence.{uA, max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory
    let YP := ((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let ZZ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj YP
    let CZ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ZZ
    (adj.unit.app (DerivedCategory.Q.obj L) ≫
          U.map (S.toAdjunction.unit.app (F.obj (DerivedCategory.Q.obj L)) ≫
            S.inverse.map (S.functor.map (comparison.app L) ≫
              (scalarLiftQObjIso.{uA, max uR uA uM} A YP).hom))) ≫
        U.map ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app ZZ) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR,
            uA} f).mapDerivedCategoryFactors.hom.app CZ =
      DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app L ≫
          ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (scalarLiftCounitInv.{uA, max uR uA uM} A YP)) := by
  intro F comparison hF L adj S U YP ZZ CZ
  have := hF
  have t1 : S.toAdjunction.unit.app (F.obj (DerivedCategory.Q.obj L)) ≫
        S.inverse.map (S.functor.map (comparison.app L) ≫
            (scalarLiftQObjIso.{uA, max uR uA uM} A YP).hom) ≫
          (scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app ZZ =
      comparison.app L ≫
        DerivedCategory.Q.map (scalarLiftCounitInv.{uA, max uR uA uM} A YP) := by
    rw [CategoryTheory.Functor.map_comp,
      Category.assoc (S.inverse.map (S.functor.map (comparison.app L)))
        (S.inverse.map (scalarLiftQObjIso.{uA, max uR uA uM} A YP).hom)
        ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app ZZ),
      ← Category.assoc (S.toAdjunction.unit.app (F.obj (DerivedCategory.Q.obj L))),
      show S.toAdjunction.unit.app (F.obj (DerivedCategory.Q.obj L)) ≫
            S.inverse.map (S.functor.map (comparison.app L)) =
          comparison.app L ≫ S.toAdjunction.unit.app (DerivedCategory.Q.obj YP) from
        (S.unitIso.hom.naturality (comparison.app L)).symm,
      Category.assoc]
    exact congrArg (fun z => comparison.app L ≫ z)
      (scalarEquivalence_unitIso_hom_app_Q_comp.{uA, max uR uA uM} A YP)
  have t2 := derivedExtensionScalarsAdjunction_unit_app.{uR, uA, uM} f F comparison L
  have t3 : (ModuleCat.restrictScalars.{max uR uA uM, uR,
          uA} f).mapDerivedCategoryFactors.inv.app YP ≫
        U.map (DerivedCategory.Q.map (scalarLiftCounitInv.{uA, max uR uA uM} A YP)) =
      DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max uR uA uM, uR,
          uA} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (scalarLiftCounitInv.{uA, max uR uA uM} A YP)) ≫
        (ModuleCat.restrictScalars.{max uR uA uM, uR,
          uA} f).mapDerivedCategoryFactors.inv.app CZ :=
    ((ModuleCat.restrictScalars.{max uR uA uM, uR,
      uA} f).mapDerivedCategoryFactors.inv.naturality
        (scalarLiftCounitInv.{uA, max uR uA uM} A YP)).symm
  have e1 : U.map (S.toAdjunction.unit.app (F.obj (DerivedCategory.Q.obj L)) ≫
          S.inverse.map (S.functor.map (comparison.app L) ≫
            (scalarLiftQObjIso.{uA, max uR uA uM} A YP).hom)) ≫
        U.map ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app ZZ) =
      U.map (comparison.app L) ≫
        U.map (DerivedCategory.Q.map (scalarLiftCounitInv.{uA, max uR uA uM} A YP)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Category.assoc, t1]
  have e2 : (ModuleCat.restrictScalars.{max uR uA uM, uR,
          uA} f).mapDerivedCategoryFactors.inv.app YP ≫
        U.map (DerivedCategory.Q.map (scalarLiftCounitInv.{uA, max uR uA uM} A YP)) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR,
            uA} f).mapDerivedCategoryFactors.hom.app CZ =
      DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max uR uA uM, uR,
        uA} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (scalarLiftCounitInv.{uA, max uR uA uM} A YP)) := by
    rw [← Category.assoc, t3, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  rw [Category.assoc, ← Category.assoc (U.map
      (S.toAdjunction.unit.app (F.obj (DerivedCategory.Q.obj L)) ≫
        S.inverse.map (S.functor.map (comparison.app L) ≫
          (scalarLiftQObjIso.{uA, max uR uA uM} A YP).hom))), e1, Category.assoc,
    ← Category.assoc (adj.unit.app (DerivedCategory.Q.obj L)), t2, Category.assoc, e2,
    ← CategoryTheory.Functor.map_comp]

/-- **The left transpose of the comparison of [stacks 0E1W], valued.**

The scalar lift over `R` of the transposed unit of
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsAdjunction_unit_comp_scalarLiftTransport`,
followed by the comparison `δ` of [stacks 0E1W], the counit of the scalar lift over `R` and the
factorization of derived restriction along the lifted ring map, is the scalar-lift presentation
of `L` followed by the localization of
`Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain`.

This is `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q_comp_counit` with its
leading morphism taken to be the transposed unit: that theorem collapses the four bookkeeping
factors over the lift of `R` into one localized chain map, and the previous theorem identifies
what it is applied to, so
`CategoryTheory.Functor.map_comp_eq_comp_of_chain` assembles the two into the displayed value.

No K-flatness of `L` is used. -/
public theorem scalarLiftExtendTransposeValue :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ),
    let adj := derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison
    let E := scalarEquivalence.{uR, max uR uA uM} R
    let S := scalarEquivalence.{uA, max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let YP := ((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let ZZ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj YP
    E.functor.map ((adj.unit.app (DerivedCategory.Q.obj L) ≫
            U.map (S.toAdjunction.unit.app (F.obj (DerivedCategory.Q.obj L)) ≫
              S.inverse.map (S.functor.map (comparison.app L) ≫
                (scalarLiftQObjIso.{uA, max uR uA uM} A YP).hom))) ≫
          (scalarRestrictionIso.{uR, uA, uM} f).hom.app (DerivedCategory.Q.obj ZZ)) ≫
        E.counitIso.hom.app (V.obj (DerivedCategory.Q.obj ZZ)) ≫
          (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.hom.app ZZ =
      ((scalarLiftQObjIso.{uR, max uR uA uM} R L).hom ≫
          DerivedCategory.Q.map (scalarLiftExtendUnitChain.{uR, uA, uM} f L) :
        E.functor.obj (DerivedCategory.Q.obj L) ⟶
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj ZZ) := by
  intro f' F comparison hF L adj E S U V YP ZZ
  have := hF
  have hs7 := scalarRestrictionIso_hom_app_Q_comp_counit.{uR, uA, uM} f ZZ
    (DerivedCategory.Q.obj L) (adj.unit.app (DerivedCategory.Q.obj L) ≫
      U.map (S.toAdjunction.unit.app (F.obj (DerivedCategory.Q.obj L)) ≫
        S.inverse.map (S.functor.map (comparison.app L) ≫
          (scalarLiftQObjIso.{uA, max uR uA uM} A YP).hom)))
  have hs8 := derivedExtensionScalarsAdjunction_unit_comp_scalarLiftTransport.{uR, uA, uM}
    f F comparison L
  have hs9 := scalarEquivalence_functor_map_Q_map_comp_scalarLiftQObjIso.{uR, max uR uA uM} R
    (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app L ≫
      ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (scalarLiftCounitInv.{uA, max uR uA uM} A YP))
  have hfin : DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app L ≫
            ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (scalarLiftCounitInv.{uA, max uR uA uM} A YP))) ≫
        DerivedCategory.Q.map (scalarRestrictionChainComparison.{uR, uA, uM} f ZZ) =
      DerivedCategory.Q.map (scalarLiftExtendUnitChain.{uR, uA, uM} f L) :=
    (DerivedCategory.Q.map_comp _ _).symm
  exact CategoryTheory.Functor.map_comp_eq_comp_of_chain E.functor hs7 hs8 hs9 hfin

/-- **The right transpose: the unit of [stacks 0GMT] over the lifted rings, with `T.alphaB`.**

Over the lifted rings, the unit of [stacks 0GMT] at the class of the scalar lift of `L`, followed
by the derived restriction of `T.alphaB` composed with any chain map `c₀` whose transpose is
`Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain`, and then by the factorization of
derived restriction, is the localization of that chain map.

The hypothesis is exactly the conclusion of
`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison`, so the chain map `c₀` costs
nothing to supply.  The proof is
`CategoryTheory.Adjunction.unit_comp_map_comp_iso_hom_eq` with the two values being
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app` over the
lifted rings and naturality of the factorization of derived restriction. -/
public theorem liftedExtensionUnit_comp_alphaB_eq
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let T := canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let ZZ := ((ModuleCat.restrictScalars.{max uR uA uM}
          (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)
    ∀ (c₀ : ((ModuleCat.extendScalars.{max uR uA uM, max uR uA uM,
          max uR uA uM} f').mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀ ⟶ ZZ)
      (_hc₀ : ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app K₀ ≫
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).map c₀ =
        (scalarLiftExtendUnitChain.{uR, uA, uM} f L :
          K₀ ⟶ ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ZZ)),
    ((@derivedExtensionScalarsAdjunction _ _ _ _ f' _ _ T.B T.alphaB
                T.isLeftDerivedB).unit.app (DerivedCategory.Q.obj K₀) ≫
          (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.map
            (T.alphaB.app K₀ ≫ DerivedCategory.Q.map c₀)) ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.hom.app ZZ =
      (DerivedCategory.Q.map (scalarLiftExtendUnitChain.{uR, uA, uM} f L) :
        DerivedCategory.Q.obj K₀ ⟶
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj ZZ) := by
  intro f' T K₀ ZZ c₀ hc₀
  refine (Adjunction.unit_comp_map_comp_iso_hom_eq
      (@derivedExtensionScalarsAdjunction _ _ _ _ f' (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) T.B T.alphaB T.isLeftDerivedB)
      ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app ZZ)
      (@derivedExtensionScalarsAdjunction_unit_app _ _ _ _ f' (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) T.B T.alphaB T.isLeftDerivedB K₀)
      (((ModuleCat.restrictScalars.{max uR uA uM}
        f').mapDerivedCategoryFactors.inv.naturality c₀).symm)).trans ?_
  exact (CategoryTheory.Functor.map_comp _ _ _).symm.trans
    (congrArg (fun m => DerivedCategory.Q.map m) hc₀)

/-- **The valuation of the comparison of [stacks 0E1W] against `T.alphaB`.**

The forward component of
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso` at the class of `L`, read between
the scalar-lift presentation of `L` on the left and the degreewise comparison of the chosen model
followed by the scalar-lift presentation of `A ⊗_R L` on the right, is the specified counit
`T.alphaB` of the canonical model over the lifted rings, followed by the localization of the
chain map
`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` produces.

Both sides are morphisms out of `T.B (Q L')`, so both are determined by their transposes under
the derived extension--restriction adjunction over the lifted rings; the left-hand transpose is
`Stacks.DerivedHom.BaseChange.scalarLiftExtendTransposeValue` -- through
`CategoryTheory.Adjunction.unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app_iso_comp`,
which removes the comparison, `T.B` and the adjunction over the lifted rings from the right-hand
side -- and the right-hand transpose is
`Stacks.DerivedHom.BaseChange.liftedExtensionUnit_comp_alphaB_eq`.  Both are the localization of
`Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain`, so the two agree.

**No K-flatness of `L` is used**, on either side. -/
public theorem derivedExtensionScalarsLiftIso_hom_app_comp_comparison :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ),
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let adj := derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison
    let E := scalarEquivalence.{uR, max uR uA uM} R
    let S := scalarEquivalence.{uA, max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let adj' := @derivedExtensionScalarsAdjunction _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp adj').leftAdjointUniq ((adj.comp S.toAdjunction).ofNatIsoRight δ)
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let YP := ((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let ZZ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj YP
    ∀ (c₀ : ((ModuleCat.extendScalars.{max uR uA uM, max uR uA uM,
          max uR uA uM} f').mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀ ⟶ ZZ)
      (_hc₀ : ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app K₀ ≫
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).map c₀ =
        (scalarLiftExtendUnitChain.{uR, uA, uM} f L :
          K₀ ⟶ ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ZZ)),
    T.B.map (scalarLiftQObjIso.{uR, max uR uA uM} R L).inv ≫
          eF.hom.app (DerivedCategory.Q.obj L) ≫
            S.functor.map (comparison.app L) ≫
              (scalarLiftQObjIso.{uA, max uR uA uM} A YP).hom =
      T.alphaB.app K₀ ≫ DerivedCategory.Q.map c₀ := by
  intro F comparison hF L f' adj E S U V T adj' δ eF K₀ YP ZZ c₀ hc₀
  have := hF
  have := T.isLeftDerivedB
  have hA := Adjunction.unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app_iso_comp
    E S adj' adj δ (DerivedCategory.Q.obj L) (scalarLiftQObjIso.{uR, max uR uA uM} R L)
    (DerivedCategory.Q.obj ZZ) (S.functor.map (comparison.app L) ≫
      (scalarLiftQObjIso.{uA, max uR uA uM} A YP).hom) _ rfl
  exact Adjunction.eq_comp_of_transpose_value adj' E.functor
    (scalarLiftQObjIso.{uR, max uR uA uM} R L)
    ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app ZZ)
    hA (scalarLiftExtendTransposeValue.{uR, uA, uM} f F comparison L)
    (liftedExtensionUnit_comp_alphaB_eq.{uR, uA, uM} f L c₀ hc₀)

/-- **Moving a presentation of the source and a trailing isomorphism to the other side.**

If `Bf` of the inverse of `i`, followed by `a`, `b` and the isomorphism `j`, is `h`, then `a ≫ b`
is `Bf` of `i`, then `h`, then the inverse of `j`. -/
private theorem comp_eq_of_map_inv_comp_comp {C D : Type*} [Category* C] [Category* D]
    (Bf : C ⥤ D) {X Y : C} (i : X ≅ Y) {Z₁ Z₂ Z₃ : D}
    {a : Bf.obj X ⟶ Z₁} {b : Z₁ ⟶ Z₂} (j : Z₂ ≅ Z₃) {h : Bf.obj Y ⟶ Z₃}
    (e : Bf.map i.inv ≫ a ≫ b ≫ j.hom = h) :
    a ≫ b = (Bf.map i.hom ≫ h) ≫ j.inv := by
  rw [← e]
  simp

/-- **Cancelling a trailing isomorphism.** -/
private theorem eq_comp_iso_inv {C : Type*} [Category C] {X Y Z : C} (i : Y ≅ Z)
    {g : X ⟶ Y} {h : X ⟶ Z} (e : g ≫ i.hom = h) : g = h ≫ i.inv := by
  rw [← e, Category.assoc, i.hom_inv_id, Category.comp_id]

/-- **The component of [stacks 0E1W]'s fourth factor against the degreewise comparison.**

`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app_comp_comparison` with the
scalar-lift presentation of `L` moved to the right-hand side and the presentation of `A ⊗_R L`
cancelled: the component of
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso` at the class of `L`, followed by
the scalar lift of the degreewise comparison of the chosen model, is the scalar lift of the
presentation of `L`, the specified counit `T.alphaB` of the canonical model over the lifted rings,
and the localization of the chain map
`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` produces, read back through the
presentation of `A ⊗_R L`.

No K-flatness is used.  This is the form in which the component occurs: the comparison itself is
`CategoryTheory.Adjunction.leftAdjointUniq`, about which nothing is computable, and this removes
it in favour of `T.alphaB` and a localized chain map. -/
public theorem derivedExtensionScalarsLiftIso_hom_app_comp_comparison_eq :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ),
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let adj := derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison
    let E := scalarEquivalence.{uR, max uR uA uM} R
    let S := scalarEquivalence.{uA, max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let adj' := @derivedExtensionScalarsAdjunction _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp adj').leftAdjointUniq ((adj.comp S.toAdjunction).ofNatIsoRight δ)
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let YP := ((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let ZZ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj YP
    ∀ (c₀ : ((ModuleCat.extendScalars.{max uR uA uM, max uR uA uM,
          max uR uA uM} f').mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀ ⟶ ZZ)
      (_hc₀ : ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app K₀ ≫
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).map c₀ =
        (scalarLiftExtendUnitChain.{uR, uA, uM} f L :
          K₀ ⟶ ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ZZ)),
    eF.hom.app (DerivedCategory.Q.obj L) ≫ S.functor.map (comparison.app L) =
      (T.B.map (scalarLiftQObjIso.{uR, max uR uA uM} R L).hom ≫
          (T.alphaB.app K₀ ≫ DerivedCategory.Q.map c₀)) ≫
        (scalarLiftQObjIso.{uA, max uR uA uM} A YP).inv := by
  intro F comparison hF L f' adj E S U V T adj' δ eF K₀ YP ZZ c₀ hc₀
  have := hF
  exact comp_eq_of_map_inv_comp_comp T.B (scalarLiftQObjIso.{uR, max uR uA uM} R L)
    (scalarLiftQObjIso.{uA, max uR uA uM} A YP)
    (derivedExtensionScalarsLiftIso_hom_app_comp_comparison.{uR, uA, uM}
      f F comparison L c₀ hc₀)

/-- **The component of [stacks 0E1W]'s fourth factor at a K-flat class, valued.**

At a K-flat `L` the degreewise comparison `comparison.app L` is invertible, so
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app_comp_comparison_eq` solves
for the component itself: the forward component of
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso` at the class of a K-flat complex is
the scalar lift of the presentation of `L`, the specified counit `T.alphaB`, the localization of
the chain map of
`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison`, and the two inverted
presentations.

**Nothing of `CategoryTheory.Adjunction.leftAdjointUniq` is left.**  Every factor on the right is
either a specified counit, a localized chain map, or an isomorphism of presentations, so a
consumer carrying this component -- which is what the hypothesis `ha` of
`Dualizing.tensorBaseChangeMor_eq_of_prefix_chain_map` does, in the contravariant slot of the
internal Hom -- can replace it by data it can compute with. -/
public theorem derivedExtensionScalarsLiftIso_hom_app_of_kFlat
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hL : CochainComplex.KFlat.{uR, max uM uA} L) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))],
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let adj := derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison
    let E := scalarEquivalence.{uR, max uR uA uM} R
    let S := scalarEquivalence.{uA, max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let T := canonicalDerivedTensorChangeOfRings f'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
        (ULift.{max uR uA uM} A)) ℤ)
    let adj' := @derivedExtensionScalarsAdjunction _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp adj').leftAdjointUniq ((adj.comp S.toAdjunction).ofNatIsoRight δ)
    let K₀ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let YP := ((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L
    let ZZ := ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj YP
    letI : IsIso (comparison.app L) :=
      isIso_comparison_app_of_kFlat.{uR, uA, uM} f F comparison L hL
    ∀ (c₀ : ((ModuleCat.extendScalars.{max uR uA uM, max uR uA uM,
          max uR uA uM} f').mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀ ⟶ ZZ)
      (_hc₀ : ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app K₀ ≫
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).map c₀ =
        (scalarLiftExtendUnitChain.{uR, uA, uM} f L :
          K₀ ⟶ ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ZZ)),
    eF.hom.app (DerivedCategory.Q.obj L) =
      ((T.B.map (scalarLiftQObjIso.{uR, max uR uA uM} R L).hom ≫
              (T.alphaB.app K₀ ≫ DerivedCategory.Q.map c₀)) ≫
          (scalarLiftQObjIso.{uA, max uR uA uM} A YP).inv) ≫
        S.functor.map (inv (comparison.app L)) := by
  intro F comparison hF f' adj E S U V T adj' δ eF K₀ YP ZZ c₀ hc₀
  have := hF
  have : IsIso (comparison.app L) :=
    isIso_comparison_app_of_kFlat.{uR, uA, uM} f F comparison L hL
  refine eq_comp_iso_inv (S.functor.mapIso (asIso (comparison.app L))) ?_
  exact derivedExtensionScalarsLiftIso_hom_app_comp_comparison_eq.{uR, uA, uM}
    f F comparison L c₀ hc₀

end Stacks.DerivedHom.BaseChange

end
