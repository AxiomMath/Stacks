module

public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.CechHomology

/-!
# The restriction map of the affine localization triangle is `m ↦ m / 1`

Let `R` be a commutative ring, `f : Fin r → R` a finite family and `M` an `R`-module. The second
map of the affine localization triangle of Stacks 0DWR is
`Stacks.LocalCohomology.cechRestriction`, the inclusion of `M` placed in degree zero into the cone
of the Čech augmentation. This file computes the degree-zero cohomology class of `m : M` under it,
through the comparison
`Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer : H⁰(RΓ(U, M̃|U)) ≃ₗ[R] ker d¹`: every
coordinate of the resulting cocycle is the constant fraction `m / 1`. That is the second of the two
hypotheses of `Stacks.LocalCohomology.localizationTriangleDataOfCechHomologyComparison`.

The computation is the one recorded in
`StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle/Data/MappingConeNaturality.lean`:
the
canonical inclusion `L ⟶ mappingCone φ` hits the second biproduct summand, on which the retraction
onto the cycles of the source is `d ∘ (φ.f 0)⁻¹`. Here `φ` is the Čech augmentation, whose inverse
in degree zero identifies `M` with the degree-zero Čech term `M_1`, and `d` is the degree-zero Čech
differential, which sends the constant fraction `m / 1` to the family `(m / 1)ᵢ` with sign `+1`
because the empty set has no element below `i`.

## Main results

* `Stacks.LocalCohomology.cechTermOneEquiv_cechD_zero` — the degree-zero Čech differential sends
  `m` to the family of constant fractions.
* `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer_restriction` — **the restriction map
  sends `m` to the cocycle all of whose coordinates are `m / 1`.**

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive CochainComplex

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (M : ModuleCat.{max u v} R)

/-! ### The degree-zero Čech differential -/

/-- The degree-zero differential of the Čech complex is the alternating sum of the transition
maps `Cech.cechD f M 0`. -/
theorem cechComplex_d_zero_one :
    (Cech.cechComplex f (M : Type _)).d 0 1 = ModuleCat.ofHom (Cech.cechD f (M : Type _) 0) :=
  CochainComplex.of_d (fun p => ModuleCat.of R (Cech.cechTerm f (M : Type _) p))
    (fun p => ModuleCat.ofHom (Cech.cechD f (M : Type _) p)) 0

/-- The identification of the degree-zero Čech term with the module carries `m` back to the
constant fraction `m / 1` on the empty index set. -/
theorem cechTermZeroEquiv_symm_apply (m : M) :
    (cechTermZeroEquiv f M).symm m =
      DirectSum.lof R (ExtendedAlternatingCech.Idx r 0)
        (fun s => Cech.cechMod f (M : Type _) s.1) default
        (LocalizedModule.mkLinearMap (Cech.cechSub f ∅) (M : Type _) m) := by
  refine (cechTermZeroEquiv f M).injective ?_
  rw [LinearEquiv.apply_symm_apply, cechTermZeroEquiv_lof,
    Stacks.CechBaseChange.cechModEmptyEquiv_mk]

/-- **The degree-zero Čech differential sends `m` to the family of constant fractions.** Only the
index `i` contributes to the coordinate at `{i}` of the differential, its sign is `+1` because the
empty set has no element below `i`, and the transition map carries `m / 1` to `m / 1`. -/
theorem cechTermOneEquiv_cechD_zero (m : M) (i : Fin r) :
    cechTermOneEquiv f M (Cech.cechD f (M : Type _) 0
        ((cechTermZeroEquiv f M).symm m)) i =
      LocalizedModule.mkLinearMap (Cech.cechSub f {i}) (M : Type _) m := by
  have hdef : ((default : ExtendedAlternatingCech.Idx r 0) : Finset (Fin r)) = ∅ := rfl
  rw [cechTermZeroEquiv_symm_apply, Cech.cechD_lof, cechTermOneEquiv_apply, map_sum]
  rw [Finset.sum_eq_single (⟨i, Finset.mem_compl.2 (Finset.notMem_empty i)⟩ :
      {x : Fin r // x ∈ ((default : ExtendedAlternatingCech.Idx r 0) : Finset (Fin r))ᶜ})]
  · rw [map_zsmul, cechComponent_lof_of_eq f M _ _
      (show insert i (∅ : Finset (Fin r)) = ({i} : Finset (Fin r)) from Finset.insert_empty)]
    rw [show Cech.cechSign ((default : ExtendedAlternatingCech.Idx r 0) : Finset (Fin r)) i = 1 by
      rw [Cech.cechSign, hdef]; simp]
    rw [one_zsmul, Cech.cechι_cechι]
    exact LinearMap.congr_fun (Cech.cechι_comp_mk f (M : Type _)
      (Finset.empty_subset ({i} : Finset (Fin r)))) m
  · intro j _ hj
    rw [map_zsmul, cechComponent_lof_of_ne f M _ _ ?_, zsmul_zero]
    intro he
    have he' : insert (j : Fin r) (∅ : Finset (Fin r)) = ({i} : Finset (Fin r)) := he
    rw [Finset.insert_empty] at he'
    exact hj (Subtype.ext (Finset.singleton_inj.1 he'))
  · intro h
    exact absurd (Finset.mem_attach _ _) h

/-- Transporting the degree-`0 → 1` differential of the integer-indexed Čech complex to the
natural-number-indexed one: the two reindexing isomorphisms cancel, and the degree-zero
identification of the integer-indexed complex is the reindexing followed by the identification of
the degree-zero Čech term with the module. -/
theorem extendXIso_one_extend_d (m : M) :
    (HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
          ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) (by simp)).hom
        ((extendedCechComplex f M).d 0 1 ((cechAugIso f M).inv m)) =
      Cech.cechD f (M : Type _) 0 ((cechTermZeroEquiv f M).symm m) := by
  have hd := HomologicalComplex.extend_d_eq (Cech.cechComplex f (M : Type _))
    ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) (j := 1) (j' := (1 : ℤ))
    (by simp) (by simp)
  have h0 : (HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
        ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) (by simp)).hom
      ((cechAugIso f M).inv m) = (cechTermZeroEquiv f M).symm m := by
    change (HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
        ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) (by simp)).hom
      ((HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
        ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) (by simp)).inv
          ((cechTermZeroEquiv f M).symm m)) = _
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
        ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) (by simp)).inv_hom_id _
  rw [ConcreteCategory.congr_hom hd ((cechAugIso f M).inv m)]
  change (HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
      ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) (by simp)).hom
    ((HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
      ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) (by simp)).inv
        ((Cech.cechComplex f (M : Type _)).d 0 1
          ((HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
            ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) (by simp)).hom
              ((cechAugIso f M).inv m)))) = _
  refine Eq.trans (ConcreteCategory.congr_hom
    (HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
      ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) (by simp)).inv_hom_id _) ?_
  rw [h0, cechComplex_d_zero_one]
  rfl

/-! ### The augmentation and the class of a module element -/

/-- The inverse of the augmentation in degree zero, precomposed with the identification of the
degree-zero term of a complex concentrated in degree zero, is the inverse of the degree-zero
identification of the Čech complex. -/
theorem singleObjXSelf_inv_comp_inv_augmentation
    [IsIso ((extendedCechAugmentation f M).f 0)] :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
        inv ((extendedCechAugmentation f M).f 0) = (cechAugIso f M).inv := by
  rw [← cancel_mono ((extendedCechAugmentation f M).f 0), Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, extendedCechAugmentation_f_zero, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

variable {M} in
/-- Mathlib's identification of the degree-`n` cohomology of a module placed in degree `n` with
the module itself, split into the comparison with cochain-complex cohomology and the computation
for a single complex. -/
theorem singleFunctorCompHomologyFunctorIso_hom_app_apply
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} R) 0).hom.app M x =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).hom
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
          ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M) x) := by
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
cohomology of the cochain complex. -/
theorem homologyFunctorFactors_singleFunctorCompHomologyFunctorIso_inv (m : M) :
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
        ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{max u v} R) 0).inv.app M m) =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).inv m := by
  have h := singleFunctorCompHomologyFunctorIso_hom_app_apply
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max u v} R) 0).inv.app M m)
  have h2 : (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max u v} R) 0).hom.app M
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} R) 0).inv.app M m) = m :=
    ConcreteCategory.congr_hom
      (((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} R) 0).app M).inv_hom_id) m
  refine (HomologicalComplex.singleObjHomologySelfIso
    (ComplexShape.up ℤ) 0 M).toLinearEquiv.injective ?_
  change (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).hom _ =
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).hom
      ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).inv m)
  rw [← h, h2]
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).inv_hom_id m).symm

/-! ### The restriction map in coordinates -/

/-- The second map of the localization triangle is the canonical inclusion into the cone: the
comparison of the two descriptions of a module placed in degree zero is the identity. -/
theorem cechRestriction_app_eq :
    (cechRestriction.{v} f).app M = DerivedCategory.Q.map (cechConeInr.{v} f M) :=
  Category.id_comp _

/-- The computation of the degree-zero cohomology of the Čech cone, applied to an element. -/
theorem cechComplementHomologyZeroIsoCycles_hom_apply
    [IsIso ((extendedCechAugmentation f M).f 0)]
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
      ((cechComplementFunctor.{v} f).obj M)) :
    (cechComplementHomologyZeroIsoCycles.{v} f M).hom x =
      Stacks.MappingCone.homologyCyclesProj (extendedCechAugmentation f M) 0
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
          (CochainComplex.mappingCone (extendedCechAugmentation f M)) x) :=
  rfl

/-- **The class of `m` in the degree-one Čech cycles is the boundary of `m / 1`.** The restriction
map is the canonical inclusion of `M⟦0⟧` into the cone, on whose image the retraction onto the
cycles of the Čech complex is the differential applied to the preimage of `m` under the
augmentation, and that preimage is the constant fraction `m / 1`. -/
theorem iCycles_cechComplementHomologyZeroIsoCycles_restriction (m : M) :
    (extendedCechComplex f M).iCycles 1 ((cechComplementHomologyZeroIsoCycles.{v} f M).hom
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          ((cechRestriction.{v} f).app M)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso
            (ModuleCat.{max u v} R) 0).inv.app M m))) =
      (extendedCechComplex f M).d 0 1 ((cechAugIso f M).inv m) := by
  have := isIso_extendedCechAugmentation_f_zero f M
  set L := (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M with hL
  set c := (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 M).inv m with hc
  have hfacL : (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app L
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} R) 0).inv.app M m) =
      L.homologyπ 0 c :=
    (homologyFunctorFactors_singleFunctorCompHomologyFunctorIso_inv m).trans
      (ConcreteCategory.congr_hom
        (HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ (ComplexShape.up ℤ) 0 M).symm m)
  have hfacC : (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
      (CochainComplex.mappingCone (extendedCechAugmentation f M))
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
        ((cechRestriction.{v} f).app M)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{max u v} R) 0).inv.app M m)) =
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) 0
        (L.homologyπ 0 c) := by
    rw [cechRestriction_app_eq, ← hfacL]
    exact ConcreteCategory.congr_hom
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.naturality
        (CochainComplex.mappingCone.inr (extendedCechAugmentation f M))) _
  have h6 : HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) 0 (L.homologyπ 0 c) =
      (CochainComplex.mappingCone (extendedCechAugmentation f M)).homologyπ 0
        (HomologicalComplex.cyclesMap
          (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) 0 c) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
      (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) 0) c
  have h7 : Stacks.MappingCone.homologyCyclesProj (extendedCechAugmentation f M) 0
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))
        ((CochainComplex.mappingCone (extendedCechAugmentation f M)).homologyπ 0
          (HomologicalComplex.cyclesMap
            (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) 0 c)) =
      Stacks.MappingCone.coneCyclesProj (extendedCechAugmentation f M) 0
        (HomologicalComplex.cyclesMap
          (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) 0 c) :=
    ConcreteCategory.congr_hom
      (Stacks.MappingCone.homologyπ_comp_homologyCyclesProj (extendedCechAugmentation f M) 0
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega))) _
  have h8 : (extendedCechComplex f M).iCycles 1
        (Stacks.MappingCone.coneCyclesProj (extendedCechAugmentation f M) 0
          (HomologicalComplex.cyclesMap
            (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) 0 c)) =
      (extendedCechComplex f M).d 0 1
        (inv ((extendedCechAugmentation f M).f 0) (L.iCycles 0 c)) :=
    ConcreteCategory.congr_hom
      (Stacks.MappingCone.coneCyclesProj_comp_cyclesMap_inr_comp_iCycles
        (extendedCechAugmentation f M) 0) c
  have h9 : L.iCycles 0 c =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv m :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles (C := ModuleCat.{max u v} R)
        (c := ComplexShape.up ℤ) (j := 0) (A := M)) m
  have h10 : inv ((extendedCechAugmentation f M).f 0)
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv m) =
      (cechAugIso f M).inv m :=
    ConcreteCategory.congr_hom (singleObjXSelf_inv_comp_inv_augmentation f M) m
  rw [cechComplementHomologyZeroIsoCycles_hom_apply, hfacC, h6, h7, h8, h9, h10]

/-- **The restriction map sends `m` to the cocycle of constant fractions.** This is the second of
the two hypotheses of
`Stacks.LocalCohomology.localizationTriangleDataOfCechHomologyComparison`. -/
theorem cechComplementHomologyZeroEquivKer_restriction (m : M) (i : Fin r) :
    cechTermOneEquiv f M (cechComplementHomologyZeroEquivKer.{v} f M
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          ((cechRestriction.{v} f).app M)
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{max u v} R) 0).inv.app M m))).1 i =
      LocalizedModule.mkLinearMap (Cech.cechSub f {i}) (M : Type _) m := by
  have h1 : (cechComplementHomologyZeroEquivKer.{v} f M
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          ((cechRestriction.{v} f).app M)
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{max u v} R) 0).inv.app M m))).1 =
      (Cech.cechComplex f (M : Type _)).iCycles 1
        ((extendedCechCyclesOneIso.{v} f M).hom
          ((cechComplementHomologyZeroIsoCycles.{v} f M).hom
            ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
              ((cechRestriction.{v} f).app M)
                ((DerivedCategory.singleFunctorCompHomologyFunctorIso
                  (ModuleCat.{max u v} R) 0).inv.app M m)))) :=
    cechCyclesOneIsoKer_hom_coe f M _
  have h2 : (Cech.cechComplex f (M : Type _)).iCycles 1
        ((extendedCechCyclesOneIso.{v} f M).hom
          ((cechComplementHomologyZeroIsoCycles.{v} f M).hom
            ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
              ((cechRestriction.{v} f).app M)
                ((DerivedCategory.singleFunctorCompHomologyFunctorIso
                  (ModuleCat.{max u v} R) 0).inv.app M m)))) =
      (HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
        ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) (by simp)).hom
          ((extendedCechComplex f M).iCycles 1
            ((cechComplementHomologyZeroIsoCycles.{v} f M).hom
              ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
                ((cechRestriction.{v} f).app M)
                  ((DerivedCategory.singleFunctorCompHomologyFunctorIso
                    (ModuleCat.{max u v} R) 0).inv.app M m)))) :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.extendCyclesIso_hom_iCycles (Cech.cechComplex f (M : Type _))
        ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) (by simp)) _
  rw [h1, h2, iCycles_cechComplementHomologyZeroIsoCycles_restriction,
    extendXIso_one_extend_d, cechTermOneEquiv_cechD_zero]

end Stacks.LocalCohomology

end
