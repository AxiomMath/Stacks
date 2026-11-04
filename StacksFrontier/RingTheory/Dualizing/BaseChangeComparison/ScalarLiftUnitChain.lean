module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsTransportClass
public import StacksFrontier.Homology.HomComplex.RHom.ScalarTransportReconciliation
import all StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionComponent

/-!
# The scalar lift of the degreewise unit of extension of scalars

Two bookkeeping facts about the scalar lift of [stacks 0E1W] are collected here, both needed to
evaluate the comparison of derived extension of scalars with the scalar lift against the
degreewise comparison of the chosen model.

The first is that the composite the unit of the scalar equivalence contributes is a *localized
chain map*: `Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_counit_app`
values the inverse unit at a class, and cancelling against that value leaves the localization of
the inverse counit of the equivalence of complexes.

The second is the chain map the comparison turns out to be: the degreewise unit of extension of
scalars along `f`, read in the scalar-lift vocabulary, is the transpose of a chain map from
`A' ⊗_{R'} L'` to the scalar lift of `A ⊗_R L`.  Only its defining equation is recorded; it is
produced as a transpose, so no degreewise computation is involved.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `Stacks.DerivedHom.BaseChange.scalarEquivalence_unitIso_hom_app_Q_comp` -- the unit of the
  scalar equivalence at a class, followed by the scalar-lift presentation read backwards, is a
  localized chain map.
* `Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain` -- the chain map the scalar lift of the
  degreewise unit of extension of scalars collapses to.
* `Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` -- that chain map is a
  transpose.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open Stacks.DerivedHom.ScalarTransportedInternalHom

namespace Stacks.DerivedHom.BaseChange

attribute [local instance] HasDerivedCategory.standard

universe u v uR uA uM

section Unit

/-- **The inverse counit of the equivalence of complexes that the scalar lift localizes.**

Restricting a complex of `B`-modules along `ULift B ≃+* B` and then back along its inverse returns
the complex up to a canonical isomorphism, the counit of
`Stacks.DerivedHom.ScalarTransportedInternalHom.uliftComplexEquivalence`.  This is its inverse.

It is the chain map that the unit of the scalar equivalence localizes, by
`Stacks.DerivedHom.BaseChange.scalarEquivalence_unitIso_hom_app_Q_comp`. -/
public def scalarLiftCounitInv (B : Type u) [CommRing B]
    (Y : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    Y ⟶ ((ModuleCat.restrictScalars.{max u v}
        (ULift.ringEquiv : ULift.{v} B ≃+* B).symm.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((ModuleCat.restrictScalars.{max u v}
          (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Y) :=
  (uliftComplexEquivalence.{u, v} B).counitIso.inv.app Y

/-- **Right-cancelling an isomorphism, by hand.**  If `a ≫ b` and `b ≫ c` are both identities
then `a = c`. -/
private theorem eq_of_comp_id_of_comp_id {C : Type*} [Category C] {X Z : C}
    (a : X ⟶ Z) (b : Z ⟶ X) (c : X ⟶ Z) (h1 : a ≫ b = 𝟙 X) (h2 : b ≫ c = 𝟙 Z) : a = c := by
  rw [← Category.comp_id a, ← h2, ← Category.assoc, h1, Category.id_comp]

/-- **The scalar-lift bookkeeping composite of [stacks 0E1W] at a class is a localized chain
map.**  The unit of the scalar equivalence at the class of `Y`, followed by the scalar-lift
presentation of that class pushed back by the inverse of the lift and the inverse factorization of
the lift, is `DerivedCategory.Q` of the inverse counit of the equivalence of complexes that the
lift localizes.

`Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_counit_app` and
`…_counit_app_Q` value the *inverse* unit at a class as the same two factors followed by the
localized counit of the equivalence of complexes; this cancels the unit against that value. -/
public theorem scalarEquivalence_unitIso_hom_app_Q_comp (B : Type u) [CommRing B]
    (Y : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    (scalarEquivalence.{u, v} B).unitIso.hom.app (DerivedCategory.Q.obj Y) ≫
        (scalarEquivalence.{u, v} B).inverse.map (scalarLiftQObjIso.{u, v} B Y).hom ≫
          (scalarEquivalenceInverseFactors.{u, v} B).hom.app
            (((ModuleCat.restrictScalars.{max u v}
              (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj Y) =
      DerivedCategory.Q.map (scalarLiftCounitInv.{u, v} B Y) := by
  have hinv : (scalarEquivalence.{u, v} B).unitIso.inv.app (DerivedCategory.Q.obj Y) =
      (scalarEquivalence.{u, v} B).inverse.map (scalarLiftQObjIso.{u, v} B Y).hom ≫
        (scalarEquivalenceInverseFactors.{u, v} B).hom.app
            (((ModuleCat.restrictScalars.{max u v}
              (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj Y) ≫
          DerivedCategory.Q.map ((uliftComplexEquivalence.{u, v} B).counitIso.hom.app Y) :=
    (derivedScalarEquivalence_counit_app.{u, v} B _).symm.trans
      (derivedScalarEquivalence_counit_app_Q.{u, v} B Y)
  have key : ((scalarEquivalence.{u, v} B).unitIso.hom.app (DerivedCategory.Q.obj Y) ≫
        (scalarEquivalence.{u, v} B).inverse.map (scalarLiftQObjIso.{u, v} B Y).hom ≫
          (scalarEquivalenceInverseFactors.{u, v} B).hom.app
            (((ModuleCat.restrictScalars.{max u v}
              (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj Y)) ≫
      DerivedCategory.Q.map ((uliftComplexEquivalence.{u, v} B).counitIso.hom.app Y) = 𝟙 _ := by
    rw [Category.assoc, Category.assoc, ← hinv]
    exact (scalarEquivalence.{u, v} B).unitIso.hom_inv_id_app _
  have hcancel : DerivedCategory.Q.map ((uliftComplexEquivalence.{u, v} B).counitIso.hom.app Y) ≫
      DerivedCategory.Q.map ((uliftComplexEquivalence.{u, v} B).counitIso.inv.app Y) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  exact eq_of_comp_id_of_comp_id _ _ _ key hcancel

end Unit

section UnitChain

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- **The chain map the scalar lift of degreewise extension of scalars is the adjunct of.**

Over the lift of `R`, the degreewise unit `L ⟶ (A ⊗_R L)|_R` of the extension--restriction
adjunction along `f`, followed by the restriction along `f` of the inverse counit of the
equivalence of complexes of `A`-modules with complexes of modules over the lift of `A`, lifted to
the lift of `R`, and then the collapse
`Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison` of the two descriptions of the
twice-restricted complex.

This is a chain map from the scalar lift of `L` to the restriction along the lifted ring map `f'`
of the scalar lift of `A ⊗_R L`, and
`Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` exhibits it as the transpose of a
chain map `A' ⊗_{R'} L' ⟶ (A ⊗_R L)'`. -/
public def scalarLiftExtendUnitChain (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) :
    ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L ⟶
    ((ModuleCat.restrictScalars.{max uR uA uM}
        (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom.comp f).comp
          (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((ModuleCat.restrictScalars.{max uR uA uM}
          (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)) :=
  ((ModuleCat.restrictScalars.{max uR uA uM}
      (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
      (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app L ≫
        ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (scalarLiftCounitInv.{uA, max uR uA uM} A
            (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L))) ≫
    scalarRestrictionChainComparison.{uR, uA, uM} f
      (((ModuleCat.restrictScalars.{max uR uA uM}
          (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L))

/-- **The scalar lift of degreewise extension of scalars, as a chain map.**

The chain map `Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain` is the transpose, under the
degreewise extension--restriction adjunction along the lifted ring map `f'`, of a chain map from
`A' ⊗_{R'} L'` to the scalar lift of `A ⊗_R L` -- the degreewise comparison of "lift, then extend"
with "extend, then lift".

Only the defining equation is asserted; nothing is claimed about the chain map beyond it, and
nothing more is needed:
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app_comp_comparison` consumes
exactly this equation. -/
public theorem exists_scalarLiftExtendComparison
    (L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) :
    letI : (ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM}
        (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom.comp f).comp
          (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM}
        (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom.comp f).comp
          (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom)).isLeftAdjoint
    ∃ c₀ : ((ModuleCat.extendScalars.{max uR uA uM, max uR uA uM, max uR uA uM}
          (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom.comp f).comp
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((ModuleCat.restrictScalars.{max uR uA uM}
              (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) ⟶
        ((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L),
      ((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM}
              (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom.comp f).comp
                (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
                  R).toRingHom)).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
            (((ModuleCat.restrictScalars.{max uR uA uM}
                (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L) ≫
          ((ModuleCat.restrictScalars.{max uR uA uM}
              (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom.comp f).comp
                (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
                  R).toRingHom)).mapHomologicalComplex (ComplexShape.up ℤ)).map c₀ =
        scalarLiftExtendUnitChain.{uR, uA, uM} f L := by
  refine ⟨(((ModuleCat.extendRestrictScalarsAdj.{max uR uA uM}
      (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom.comp f).comp
        (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom)).mapHomologicalComplex
    (ComplexShape.up ℤ)).homEquiv _ _).symm (scalarLiftExtendUnitChain.{uR, uA, uM} f L), ?_⟩
  exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

end UnitChain

end Stacks.DerivedHom.BaseChange

end
