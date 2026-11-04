module

public import StacksFrontier.RingTheory.LocalCohomology.FreeUniverse.ConeNaturality
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Restriction

/-!
# The restriction map in coordinates, in a free module universe

`StacksFrontier/RingTheory/LocalCohomology/FreeUniverse/ConeHomology.lean` identifies the
degree-zero cohomology of derived sections on `U = Spec R \ V(I)` with the degree-one Čech
cocycles at a module universe `v` independent of the ring universe `u`. This file computes what
that identification does to the class of a module element `m`: the second map of the
localization triangle carries it to the cocycle all of whose coordinates are the constant
fraction `m / 1`.

It is `StacksFrontier/RingTheory/LocalCohomology/SectionsIso/Restriction.lean` with the constraint
`ModuleCat.{max u v}` removed — the small model of the Čech complex in place of the pinned one —
together with the two free-universe degree-zero identifications that the pinned file takes from
`StacksFrontier/RingTheory/LocalCohomology/CechModel.lean`.

## Main results

* `Stacks.LocalCohomology.cechTermOneEquiv_cechD_zero_free` — the degree-zero Čech differential
  sends `m` to the family of constant fractions, with the module universe free.
* `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKerFree_restriction` — **the restriction
  map sends `m` to the cocycle of constant fractions**, at a module universe independent of the
  ring universe. This is the second of the two remaining hypotheses of Stacks 0DWR at that
  universe.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive CochainComplex

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (M : ModuleCat.{v} R)

/-! ### The degree-zero differential, in a free module universe -/

/-- The identification of the degree-zero Čech term with the module carries `m` back to the
constant fraction `m / 1` on the empty index set. -/
theorem cechTermZeroEquivFree_symm_apply (m : M) :
    (cechTermZeroEquivFree f (M : Type v)).symm m =
      DirectSum.lof R (ExtendedAlternatingCech.Idx r 0)
        (fun s => Cech.cechMod f (M : Type v) s.1) default
        (LocalizedModule.mkLinearMap (Cech.cechSub f ∅) (M : Type v) m) := by
  refine (cechTermZeroEquivFree f (M : Type v)).injective ?_
  rw [LinearEquiv.apply_symm_apply, cechTermZeroEquivFree_lof,
    Stacks.CechBaseChange.cechModEmptyEquiv_mk]

/-- **The degree-zero Čech differential sends `m` to the family of constant fractions**, with the
module universe independent of the ring universe. -/
theorem cechTermOneEquiv_cechD_zero_free (m : M) (i : Fin r) :
    cechTermOneEquiv f M (Cech.cechD f (M : Type v) 0
        ((cechTermZeroEquivFree f (M : Type v)).symm m)) i =
      LocalizedModule.mkLinearMap (Cech.cechSub f {i}) (M : Type v) m := by
  have hdef : ((default : ExtendedAlternatingCech.Idx r 0) : Finset (Fin r)) = ∅ := rfl
  rw [cechTermZeroEquivFree_symm_apply, Cech.cechD_lof, cechTermOneEquiv_apply, map_sum]
  rw [Finset.sum_eq_single (⟨i, Finset.mem_compl.2 (Finset.notMem_empty i)⟩ :
      {x : Fin r // x ∈ ((default : ExtendedAlternatingCech.Idx r 0) : Finset (Fin r))ᶜ})]
  · rw [map_zsmul, cechComponent_lof_of_eq f M _ _
      (show insert i (∅ : Finset (Fin r)) = ({i} : Finset (Fin r)) from Finset.insert_empty)]
    rw [show Cech.cechSign ((default : ExtendedAlternatingCech.Idx r 0) : Finset (Fin r)) i = 1 by
      rw [Cech.cechSign, hdef]; simp]
    rw [one_zsmul, Cech.cechι_cechι]
    exact LinearMap.congr_fun (Cech.cechι_comp_mk f (M : Type v)
      (Finset.empty_subset ({i} : Finset (Fin r)))) m
  · intro j _ hj
    rw [map_zsmul, cechComponent_lof_of_ne f M _ _ ?_, zsmul_zero]
    intro he
    have he' : insert (j : Fin r) (∅ : Finset (Fin r)) = ({i} : Finset (Fin r)) := he
    rw [Finset.insert_empty] at he'
    exact hj (Subtype.ext (Finset.singleton_inj.1 he'))
  · intro h
    exact absurd (Finset.mem_attach _ _) h

/-- The degree-zero differential of the small Čech complex is `Cech.cechDShrink`. -/
theorem cechComplexShrink_d_zero_one :
    (Cech.cechComplexShrink.{v} f (M : Type v)).d 0 1 =
      ModuleCat.ofHom (Cech.cechDShrink.{v} f (M : Type v) 0) :=
  Cech.cechComplexShrink_d.{v} f (M : Type v) 0

/-- Transporting the degree-`0 → 1` differential of the integer-indexed small model to the
natural-number-indexed one. -/
theorem extendXIsoShrink_one_extend_d (m : M) :
    (HomologicalComplex.extendXIso (Cech.cechComplexShrink.{v} f (M : Type v))
          ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) (by simp)).hom
        ((Cech.extendedCechComplexShrink.{v} f (M : Type v)).d 0 1
          ((extendedCechXZeroIsoShrink.{v} f M).inv m)) =
      Cech.cechDShrink.{v} f (M : Type v) 0
        ((cechTermShrinkZeroEquiv.{v} f (M : Type v)).symm m) := by
  have hd := HomologicalComplex.extend_d_eq (Cech.cechComplexShrink.{v} f (M : Type v))
    ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) (j := 1) (j' := (1 : ℤ))
    (by simp) (by simp)
  have h0 : (HomologicalComplex.extendXIso (Cech.cechComplexShrink.{v} f (M : Type v))
        ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) (by simp)).hom
      ((extendedCechXZeroIsoShrink.{v} f M).inv m) =
      (cechTermShrinkZeroEquiv.{v} f (M : Type v)).symm m :=
    Iso.inv_hom_id_apply _ _
  rw [ConcreteCategory.congr_hom hd, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    Iso.inv_hom_id_apply, h0, cechComplexShrink_d_zero_one]
  rfl

/-! ### The augmentation and the class of a module element -/

/-- The inverse of the small augmentation in degree zero, precomposed with the identification of
the degree-zero term of a complex concentrated in degree zero, is the inverse of the degree-zero
identification of the small Čech complex. -/
theorem singleObjXSelf_inv_comp_inv_augmentationShrink
    [IsIso ((extendedCechAugmentationShrink.{v} f M).f 0)] :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
        inv ((extendedCechAugmentationShrink.{v} f M).f 0) =
      (extendedCechXZeroIsoShrink.{v} f M).inv := by
  rw [← cancel_mono ((extendedCechAugmentationShrink.{v} f M).f 0), Category.assoc,
    IsIso.inv_hom_id, Category.comp_id, extendedCechAugmentationShrink_f_zero,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable {M} in
/-- Mathlib's identification of the degree-`n` cohomology of a module placed in degree `n` with
the module itself, split into the comparison with cochain-complex cohomology and the computation
for a single complex. This is
`Stacks.LocalCohomology.singleFunctorCompHomologyFunctorIso_hom_app_apply` with the module
universe free. -/
theorem singleFunctorCompHomologyFunctorIso_hom_app_apply_free
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) 0).hom.app M x =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).hom
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).hom.app
          ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M) x) := by
  simp only [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.singleFunctorsPostcompQIso, SingleFunctors.evaluation, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.mapIso_hom, Iso.refl_hom, SingleFunctors.id_hom, NatTrans.id_app,
    HomologicalComplex.homologyFunctorSingleIso_hom_app, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply]
  simp only [CategoryTheory.Functor.map_id]
  rfl

variable {M} in
/-- The class of `m : M` in the degree-zero cohomology of `M` placed in degree zero, read in the
cohomology of the cochain complex, with the module universe free. -/
theorem homologyFunctorFactors_singleFunctorCompHomologyFunctorIso_inv_free (m : M) :
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).hom.app
        ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{v} R) 0).inv.app M m) =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).inv m := by
  have h := singleFunctorCompHomologyFunctorIso_hom_app_apply_free.{v}
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{v} R) 0).inv.app M m)
  have h2 : (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{v} R) 0).hom.app M
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{v} R) 0).inv.app M m) = m :=
    Iso.inv_hom_id_apply ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{v} R) 0).app M) m
  refine (HomologicalComplex.singleObjHomologySelfIso
    (ComplexShape.up ℤ) 0 M).toLinearEquiv.injective ?_
  show (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).hom _ =
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).hom
      ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).inv m)
  rw [← h, h2]
  exact (Iso.inv_hom_id_apply _ _).symm

/-! ### The restriction map in coordinates -/

/-- The second map of the localization triangle at a free module universe is the canonical
inclusion into the cone: the comparison of the two descriptions of a module placed in degree zero
is the identity. -/
theorem cechRestrictionShrink_app_eq :
    (cechRestrictionShrink.{v} f).app M = DerivedCategory.Q.map (cechConeInrShrink.{v} f M) :=
  Category.id_comp _

/-- The computation of the degree-zero cohomology of the small Čech cone, applied to an
element. -/
theorem cechComplementHomologyZeroIsoCyclesShrink_hom_apply
    [IsIso ((extendedCechAugmentationShrink.{v} f M).f 0)]
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
      ((cechComplementFunctorShrink.{v} f).obj M)) :
    (cechComplementHomologyZeroIsoCyclesShrink.{v} f M).hom x =
      Stacks.MappingCone.homologyCyclesProj (extendedCechAugmentationShrink.{v} f M) 0
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).hom.app
          (CochainComplex.mappingCone (extendedCechAugmentationShrink.{v} f M)) x) :=
  rfl

/-- **The class of `m` in the degree-one small Čech cycles is the boundary of `m / 1`.** -/
theorem iCycles_cechComplementHomologyZeroIsoCyclesShrink_restriction (m : M) :
    (Cech.extendedCechComplexShrink.{v} f (M : Type v)).iCycles 1
        ((cechComplementHomologyZeroIsoCyclesShrink.{v} f M).hom
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechRestrictionShrink.{v} f).app M)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso
            (ModuleCat.{v} R) 0).inv.app M m))) =
      (Cech.extendedCechComplexShrink.{v} f (M : Type v)).d 0 1
        ((extendedCechXZeroIsoShrink.{v} f M).inv m) := by
  have := isIso_extendedCechAugmentationShrink_f_zero.{v} f M
  set L := (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M with hL
  set c := (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 M).inv m with hc
  have hfacL : (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).hom.app L
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{v} R) 0).inv.app M m) =
      L.homologyπ 0 c :=
    (homologyFunctorFactors_singleFunctorCompHomologyFunctorIso_inv_free.{v} m).trans
      (ConcreteCategory.congr_hom
        (HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ (ComplexShape.up ℤ) 0 M).symm m)
  have hfacC : (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).hom.app
      (CochainComplex.mappingCone (extendedCechAugmentationShrink.{v} f M))
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
        ((cechRestrictionShrink.{v} f).app M)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{v} R) 0).inv.app M m)) =
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (extendedCechAugmentationShrink.{v} f M)) 0
        (L.homologyπ 0 c) := by
    rw [cechRestrictionShrink_app_eq, ← hfacL]
    exact ConcreteCategory.congr_hom
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).hom.naturality
        (CochainComplex.mappingCone.inr (extendedCechAugmentationShrink.{v} f M))) _
  have h6 : HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (extendedCechAugmentationShrink.{v} f M)) 0
        (L.homologyπ 0 c) =
      (CochainComplex.mappingCone (extendedCechAugmentationShrink.{v} f M)).homologyπ 0
        (HomologicalComplex.cyclesMap
          (CochainComplex.mappingCone.inr (extendedCechAugmentationShrink.{v} f M)) 0 c) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
      (CochainComplex.mappingCone.inr (extendedCechAugmentationShrink.{v} f M)) 0) c
  have h7 : Stacks.MappingCone.homologyCyclesProj
        (extendedCechAugmentationShrink.{v} f M) 0
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))
        ((CochainComplex.mappingCone (extendedCechAugmentationShrink.{v} f M)).homologyπ 0
          (HomologicalComplex.cyclesMap
            (CochainComplex.mappingCone.inr (extendedCechAugmentationShrink.{v} f M)) 0 c)) =
      Stacks.MappingCone.coneCyclesProj (extendedCechAugmentationShrink.{v} f M) 0
        (HomologicalComplex.cyclesMap
          (CochainComplex.mappingCone.inr (extendedCechAugmentationShrink.{v} f M)) 0 c) :=
    ConcreteCategory.congr_hom
      (Stacks.MappingCone.homologyπ_comp_homologyCyclesProj
        (extendedCechAugmentationShrink.{v} f M) 0
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))) _
  have h8 : (Cech.extendedCechComplexShrink.{v} f (M : Type v)).iCycles 1
        (Stacks.MappingCone.coneCyclesProj (extendedCechAugmentationShrink.{v} f M) 0
          (HomologicalComplex.cyclesMap
            (CochainComplex.mappingCone.inr (extendedCechAugmentationShrink.{v} f M)) 0 c)) =
      (Cech.extendedCechComplexShrink.{v} f (M : Type v)).d 0 1
        (inv ((extendedCechAugmentationShrink.{v} f M).f 0) (L.iCycles 0 c)) :=
    ConcreteCategory.congr_hom
      (Stacks.MappingCone.coneCyclesProj_comp_cyclesMap_inr_comp_iCycles
        (extendedCechAugmentationShrink.{v} f M) 0) c
  have h9 : L.iCycles 0 c =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv m :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles (C := ModuleCat.{v} R)
        (c := ComplexShape.up ℤ) (j := 0) (A := M)) m
  have h10 : inv ((extendedCechAugmentationShrink.{v} f M).f 0)
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv m) =
      (extendedCechXZeroIsoShrink.{v} f M).inv m :=
    ConcreteCategory.congr_hom (singleObjXSelf_inv_comp_inv_augmentationShrink.{v} f M) m
  rw [cechComplementHomologyZeroIsoCyclesShrink_hom_apply, hfacC, h6, h7, h8, h9, h10]

/-- **The restriction map sends `m` to the cocycle of constant fractions**, read in the small
model. -/
theorem cechComplementHomologyZeroEquivKerShrink_restriction (m : M) :
    (cechComplementHomologyZeroEquivKerShrink.{v} f M
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechRestrictionShrink.{v} f).app M)
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{v} R) 0).inv.app M m))).1 =
      Cech.cechDShrink.{v} f (M : Type v) 0
        ((cechTermShrinkZeroEquiv.{v} f (M : Type v)).symm m) := by
  have h1 : (cechComplementHomologyZeroEquivKerShrink.{v} f M
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechRestrictionShrink.{v} f).app M)
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{v} R) 0).inv.app M m))).1 =
      (Cech.cechComplexShrink.{v} f (M : Type v)).iCycles 1
        ((extendedCechCyclesOneIsoShrink.{v} f M).hom
          ((cechComplementHomologyZeroIsoCyclesShrink.{v} f M).hom
            ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
              ((cechRestrictionShrink.{v} f).app M)
                ((DerivedCategory.singleFunctorCompHomologyFunctorIso
                  (ModuleCat.{v} R) 0).inv.app M m)))) :=
    cechCyclesOneIsoKerShrink_hom_coe.{v} f M _
  have h2 : (Cech.cechComplexShrink.{v} f (M : Type v)).iCycles 1
        ((extendedCechCyclesOneIsoShrink.{v} f M).hom
          ((cechComplementHomologyZeroIsoCyclesShrink.{v} f M).hom
            ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
              ((cechRestrictionShrink.{v} f).app M)
                ((DerivedCategory.singleFunctorCompHomologyFunctorIso
                  (ModuleCat.{v} R) 0).inv.app M m)))) =
      (HomologicalComplex.extendXIso (Cech.cechComplexShrink.{v} f (M : Type v))
        ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) (by simp)).hom
          ((Cech.extendedCechComplexShrink.{v} f (M : Type v)).iCycles 1
            ((cechComplementHomologyZeroIsoCyclesShrink.{v} f M).hom
              ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
                ((cechRestrictionShrink.{v} f).app M)
                  ((DerivedCategory.singleFunctorCompHomologyFunctorIso
                    (ModuleCat.{v} R) 0).inv.app M m)))) :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.extendCyclesIso_hom_iCycles
        (Cech.cechComplexShrink.{v} f (M : Type v))
        ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) (by simp)) _
  rw [h1, h2, iCycles_cechComplementHomologyZeroIsoCyclesShrink_restriction,
    extendXIsoShrink_one_extend_d]

/-- The comparison of the small model with `Cech.cechComplex` carries the constant-fraction
cocycle of the small model to the constant-fraction cocycle of `Cech.cechComplex`. -/
theorem cechTermShrinkEquiv_cechDShrink_zero (m : M) :
    Cech.cechTermShrinkEquiv.{v} f (M : Type v) 1
        (Cech.cechDShrink.{v} f (M : Type v) 0
          ((cechTermShrinkZeroEquiv.{v} f (M : Type v)).symm m)) =
      Cech.cechD f (M : Type v) 0 ((cechTermZeroEquivFree f (M : Type v)).symm m) := by
  rw [Cech.cechTermShrinkEquiv_cechDShrink]
  congr 1
  refine (Cech.cechTermShrinkEquiv.{v} f (M : Type v) 0).symm.injective ?_
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- **The restriction map sends `m` to the cocycle of constant fractions**, at a module universe
independent of the ring universe. This is the second of the two hypotheses that remain for
Stacks 0DWR at an independent module universe. -/
theorem cechComplementHomologyZeroEquivKerFree_restriction (m : M) (i : Fin r) :
    cechTermOneEquiv f M (cechComplementHomologyZeroEquivKerFree.{v} f M
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechRestrictionShrink.{v} f).app M)
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{v} R) 0).inv.app M m))).1 i =
      LocalizedModule.mkLinearMap (Cech.cechSub f {i}) (M : Type v) m := by
  have h : (cechComplementHomologyZeroEquivKerFree.{v} f M
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechRestrictionShrink.{v} f).app M)
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{v} R) 0).inv.app M m))).1 =
      Cech.cechD f (M : Type v) 0 ((cechTermZeroEquivFree f (M : Type v)).symm m) := by
    rw [show (cechComplementHomologyZeroEquivKerFree.{v} f M
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechRestrictionShrink.{v} f).app M)
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{v} R) 0).inv.app M m))) =
      kerCechDShrinkOneEquivKer.{v} f M (cechComplementHomologyZeroEquivKerShrink.{v} f M
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechRestrictionShrink.{v} f).app M)
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{v} R) 0).inv.app M m))) from rfl]
    rw [kerCechDShrinkOneEquivKer_coe, cechComplementHomologyZeroEquivKerShrink_restriction,
      cechTermShrinkEquiv_cechDShrink_zero]
  rw [h, cechTermOneEquiv_cechD_zero_free]

end Stacks.LocalCohomology

end
