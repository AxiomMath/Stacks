module

public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsTransportClass

/-!
# The keystone's [stacks 068I] prefix as a localized chain map

`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_comp_counit_comp_eq` collapses the whole
scalar-lift bookkeeping of the [stacks 068I] side of the keystone of Chapter 47 into one localized
chain map, leaving in front the scalar lift of a morphism of `D(R)`: the unit of [stacks 0GMT] at
the class of the K-flat complex `K`, then the restriction along `f` of a morphism out of
`F (Q K)`, then the factorization of derived restriction along `f`.

This file values that morphism.  At a K-flat `K` the comparison of the model `F` with degreewise
extension of scalars is invertible, so
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat`
solves the unit outright, and its trailing inverse comparison cancels against the presentation of
the morphism out of `F (Q K)`.  What is left is the degreewise unit of the extension--restriction
adjunction followed by the restriction of a chain map, localized -- and the scalar lift carries a
localized chain map to a localized chain map.

So the whole [stacks 068I] prefix is `Stacks.DerivedHom.BaseChange.scalarLiftQObjIso` at `K`
followed by `DerivedCategory.Q` of an explicit chain map, as soon as the one morphism out of
`F (Q K)` that the keystone supplies -- the [stacks 0A63] transpose over `A` of the [stacks 068I]
candidate, read through the comparison factors of [stacks 0E1W] -- is the comparison at `K`
followed by a localized chain map.  That hypothesis is the only content left in the prefix.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is that the
prefix of the other hypothesis is a localized chain map under one hypothesis about one morphism.

## Main results

* `Stacks.DerivedHom.BaseChange.functor_map_unit_comp_eq_scalarLift` -- the scalar lift of the
  [stacks 068I] prefix, followed by the scalar-lift presentation of the restricted target, is the
  scalar-lift presentation of `K` followed by the localization of the degreewise unit of the
  extension--restriction adjunction and the restriction of the given chain map.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
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
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **The keystone's [stacks 068I] prefix is a localized chain map.**

Let `K` be K-flat, `Y` a cochain complex of `A`-modules, and let `nmor : F (Q K) ⟶ Q Y` be the
comparison at `K` followed by the localization of a chain map `m`.  Then the unit of
[stacks 0GMT] at `Q K`, followed by the restriction along `f` of `nmor` and the factorization of
derived restriction along `f`, is -- after the scalar lift over `R` and the scalar-lift
presentation of the restriction of `Y` -- the scalar-lift presentation of `K` followed by the
localization of the lift of the degreewise unit composed with the restriction of `m`. -/
public theorem functor_map_unit_comp_eq_scalarLift
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max uM uA} K)
    (Y : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
    (nmor : F.obj (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj Y)
    (m : ((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ Y)
    (hm : nmor = comparison.app K ≫ DerivedCategory.Q.map m) :
    (scalarEquivalence.{uR, max uR uA uM} R).functor.map
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
              (DerivedCategory.Q.obj K) ≫
            (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map nmor ≫
              (ModuleCat.restrictScalars.{max uR uA uM, uR,
                uA} f).mapDerivedCategoryFactors.hom.app Y) ≫
        (scalarLiftQObjIso.{uR, max uR uA uM} R
          (((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Y)).hom =
      (scalarLiftQObjIso.{uR, max uR uA uM} R K).hom ≫
        DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).unit.app K ≫
              ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).map m)) := by
  have : IsIso (comparison.app K) :=
    isIso_comparison_app_of_kFlat.{uR, uA, uM} f F comparison K hK
  have hunit : (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
        (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K) ≫
        (ModuleCat.restrictScalars.{max uR uA uM, uR,
            uA} f).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
            (inv (comparison.app K)) :=
    derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat.{uR, uA, uM} f F comparison K hK
  have hcancel : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
        (inv (comparison.app K)) ≫
      (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map nmor =
      (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
        (DerivedCategory.Q.map m) := by
    rw [← CategoryTheory.Functor.map_comp, hm, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  have hnat : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
        (DerivedCategory.Q.map m) ≫
      (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors.hom.app Y =
      (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          (((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map m) :=
    (ModuleCat.restrictScalars.{max uR uA uM, uR,
      uA} f).mapDerivedCategoryFactors.hom.naturality m
  have hpre : (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
          (DerivedCategory.Q.obj K) ≫
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map nmor ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR,
            uA} f).mapDerivedCategoryFactors.hom.app Y =
      DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K ≫
          ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map m) := by
    simp only [hunit, Functor.map_comp, Category.assoc, reassoc_of% hcancel, hnat,
      Iso.inv_hom_id_app_assoc]
  rw [hpre]
  exact scalarEquivalence_functor_map_Q_map_comp_scalarLiftQObjIso.{uR, max uR uA uM} R _

include hF in
/-- **The whole [stacks 068I] prefix of the keystone's residual equation is a localized chain
map.**

The first entry of the pair the derived tensor bifunctor is applied to in
`Dualizing.tensorBaseChangeMor_eq_iff_exists_scalarLiftEvaluation` is: the scalar lift of the unit
of [stacks 0GMT] at `Q K` followed by the restriction along `f` of the [stacks 0A63] transpose
over `A` of the [stacks 068I] candidate; then the factor `v` of that reduction, which is the
comparison of [stacks 0E1W] followed by the counit of the scalar lift over `R`; then its factor
`p`.

Suppose `p` is the image under derived restriction along the lifted ring map of a morphism `ψ` to
the class of a cochain complex `Z`, followed by the factorization of that restriction -- which is
how the split presentation
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_tensorKFlat_split`
produces it.  Suppose further that the transpose, followed by `ψ` and the inverse scalar lift over
`A`, is the comparison at `K` followed by the localization of a chain map `m`.

Then the whole prefix is the scalar-lift presentation of `K` followed by `DerivedCategory.Q` of an
explicit chain map: the lift of the degreewise unit and the restriction of `m`, then
`Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison`.

This is the hypothesis `ha` of
`Stacks.DerivedHom.BaseChangeIso.tensor_map_comp_homEquiv_comp_eq_of_uncurry`, reduced to the one
hypothesis `_hm` about the transpose. -/
public theorem prefix_eq_scalarLiftQObjIso_comp_Q_map
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max uM uA} K)
    (Z : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    ∀ (N : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)))
      (t : F.obj (DerivedCategory.Q.obj K) ⟶
        (scalarEquivalence.{uA, max uR uA uM} A).inverse.obj N)
      (ψ : N ⟶ DerivedCategory.Q.obj Z)
      (p : (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.obj N ⟶
        DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{max uR uA uM}
          f').mapHomologicalComplex (ComplexShape.up ℤ)).obj Z))
      (m : ((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶
        ((ModuleCat.restrictScalars.{max uR uA uM}
          (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Z)
      (_hp : p = (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.map ψ ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.hom.app Z)
      (_hm : t ≫ (scalarEquivalence.{uA, max uR uA uM} A).inverse.map ψ ≫
          (scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app Z =
        comparison.app K ≫ DerivedCategory.Q.map m),
    (scalarEquivalence.{uR, max uR uA uM} R).functor.map
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
              (DerivedCategory.Q.obj K) ≫
            (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map t) ≫
        ((scalarEquivalence.{uR, max uR uA uM} R).functor.map
              ((scalarRestrictionIso.{uR, uA, uM} f).hom.app N) ≫
            (scalarEquivalence.{uR, max uR uA uM} R).counitIso.hom.app
              ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.obj N)) ≫ p =
      ((scalarLiftQObjIso.{uR, max uR uA uM} R K).hom ≫
        DerivedCategory.Q.map
          (((ModuleCat.restrictScalars.{max uR uA uM}
              (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
              (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
                  (ComplexShape.up ℤ)).unit.app K ≫
                ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map m) ≫
            scalarRestrictionChainComparison.{uR, uA, uM} f Z) :
        (scalarEquivalence.{uR, max uR uA uM} R).functor.obj (DerivedCategory.Q.obj K) ⟶
          DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{max uR uA uM}
            f').mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) := by
  intro f' N t ψ p m hp hm
  subst hp
  have hassoc : (scalarEquivalence.{uR, max uR uA uM} R).functor.map
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
              (DerivedCategory.Q.obj K) ≫
            (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map t) ≫
        ((scalarEquivalence.{uR, max uR uA uM} R).functor.map
              ((scalarRestrictionIso.{uR, uA, uM} f).hom.app N) ≫
            (scalarEquivalence.{uR, max uR uA uM} R).counitIso.hom.app
              ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.obj N)) ≫
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.map ψ ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.hom.app Z) =
      (scalarEquivalence.{uR, max uR uA uM} R).functor.map
            (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
                  (DerivedCategory.Q.obj K) ≫
                (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map t) ≫
              (scalarRestrictionIso.{uR, uA, uM} f).hom.app N) ≫
          (scalarEquivalence.{uR, max uR uA uM} R).counitIso.hom.app
              ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.obj N) ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.map ψ ≫
              (ModuleCat.restrictScalars.{max uR uA uM}
                f').mapDerivedCategoryFactors.hom.app Z := by
    simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [hassoc, scalarRestrictionIso_hom_comp_counit_comp_eq.{uR, uA, uM} f Z
    (DerivedCategory.Q.obj K) N
    ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
        (DerivedCategory.Q.obj K) ≫
      (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map t) ψ]
  have hinner : (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
              (DerivedCategory.Q.obj K) ≫
            (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map t) ≫
          (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
            ((scalarEquivalence.{uA, max uR uA uM} A).inverse.map ψ)) ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
            ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app Z) ≫
          (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.restrictScalars.{max uR uA uM}
              (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+*
                A).symm.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) =
      (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
            (DerivedCategory.Q.obj K) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
              (t ≫ (scalarEquivalence.{uA, max uR uA uM} A).inverse.map ψ ≫
                (scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app Z) ≫
            (ModuleCat.restrictScalars.{max uR uA uM, uR,
                uA} f).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.restrictScalars.{max uR uA uM}
                (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+*
                  A).symm.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) := by
    simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [hinner, ← Category.assoc,
    functor_map_unit_comp_eq_scalarLift.{uR, uA, uM} f F comparison K hK
      (((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z) _ m hm,
    Category.assoc, ← CategoryTheory.Functor.map_comp]

end Stacks.DerivedHom.BaseChange

end
