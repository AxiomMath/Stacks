module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Data.MappingConeNaturality
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Restriction
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Reduction
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero

/-!
# The degree-zero Čech comparison is natural and sends `m` to `m / 1`

Let `R` be a commutative ring, `f : Fin r → R` a finite family and `M` an `R`-module.
`Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer` identifies the degree-zero cohomology
of the cone of the Čech augmentation with the degree-one Čech cocycles. This file proves the two
properties of that identification which
`Stacks.LocalCohomology.localizationTriangleDataOfCechHomologyComparison` consumes: it is natural
in `M`, and it carries the class coming from `M` in degree zero to the cocycle all of whose
coordinates are the constant fraction `m / 1`.

Both come from one computation. The comparison is the composite of three isomorphisms — the
mapping-cone comparison of `StacksFrontier/RingTheory/LocalCohomology/MappingConeH0/Basic.lean`, the
reindexing of the Čech complex from `ℕ` to `ℤ`, and the description of the degree-one cycles as a
kernel of linear maps — and each of the last two is determined by its composite with the inclusion
`HomologicalComplex.iCycles` of the cycles into the degree-one term. So the whole comparison,
followed by the inclusion of the cocycles into `C¹`, is the mapping-cone retraction
`Stacks.MappingCone.homologyCyclesProj` followed by `iCycles` and the reindexing isomorphism; this
is `Stacks.LocalCohomology.cechComplementHomologyZeroIsoKer_hom_comp_subtype`. Naturality and the
value on the image of `M` are then the corresponding statements about the retraction, proved in
`StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle/Data/MappingConeNaturality.lean`,
together with the degree-zero description of the augmentation.

The formula `m ↦ m / 1` comes out as follows. The retraction carries the class of an element of
the target of the augmentation to the differential applied to its preimage, so the class of `m` is
carried to `d⁰(a₀⁻¹ m)` where `a₀ : C⁰ ≅ M` is the augmentation in degree zero; that is, to `d⁰`
applied to the constant fraction `m / 1` in the single summand `C⁰ = M_1` of degree zero. By the
formula for the Čech differential this is the family `(m / 1)_i`, the sign being `+1` because no
element of the empty set precedes the inserted index.

## Main definitions

* `Stacks.LocalCohomology.extendXOneIso` — the degree-one reindexing isomorphism.

## Main results

* `Stacks.LocalCohomology.cechComplementHomologyZeroIsoKer_hom_comp_subtype` — the comparison,
  followed by the inclusion of the cocycles into `C¹`, is the mapping-cone retraction followed by
  the inclusion of the cycles.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive CochainComplex

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.LocalCohomology.isIso_extendedCechAugmentation_f_zero

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-! ### The comparison, followed by the inclusion of the cocycles -/

section Comparison

variable (M : ModuleCat.{max u v} R)

/-- Degree one of the `ℕ`-indexed complex sits in degree one of the `ℤ`-indexed one. -/
theorem embeddingUpNat_f_one : ComplexShape.embeddingUpNat.f 1 = 1 := by simp

/-- The reindexing isomorphism in degree one. -/
def extendXOneIso :
    (extendedCechComplex f M).X 1 ≅ (Cech.cechComplex f (M : Type _)).X 1 :=
  HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
    ComplexShape.embeddingUpNat embeddingUpNat_f_one

/-- The target of the Čech augmentation, a module placed in degree zero, vanishes in degree
`-1`. -/
theorem isZero_singleObj_X_neg_one :
    IsZero (((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M).X (0 - 1)) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ (by omega)

/-- The degree-zero cohomology of the Čech cone, compared with the degree-one cycles: the
comparison of derived-category and complex-level cohomology, followed by the mapping-cone
retraction. -/
theorem cechComplementHomologyZeroIsoCycles_hom :
    (cechComplementHomologyZeroIsoCycles.{v} f M).hom =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
          (CochainComplex.mappingCone (extendedCechAugmentation f M)) ≫
        Stacks.MappingCone.homologyCyclesProj (extendedCechAugmentation f M) 0
          (isZero_singleObj_X_neg_one M) :=
  rfl

/-- The description of the degree-one cycles as a kernel of linear maps is the inclusion of the
cycles: both read a cycle as an element of the degree-one Čech term.

The inclusion of the kernel is spelled here as the subtype inclusion of
`LinearMap.ker (Cech.cechD f M 1)`. -/
theorem cechCyclesOneIsoKer_hom_comp_kerSubtype :
    (cechCyclesOneIsoKer f M).hom ≫
        ModuleCat.ofHom (LinearMap.ker (Cech.cechD f (M : Type _) 1)).subtype =
      (Cech.cechComplex f (M : Type _)).iCycles 1 :=
  ModuleCat.hom_ext (LinearMap.ext fun x => by
    show (HomologicalComplex.sc' (Cech.cechComplex f (M : Type _)) 0 1 2
        ).moduleCatLeftHomologyData.i
        ((HomologicalComplex.sc' (Cech.cechComplex f (M : Type _)) 0 1 2).moduleCatCyclesIso.hom
          (((Cech.cechComplex f (M : Type _)).cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom x)) = _
    rw [ShortComplex.moduleCatCyclesIso_hom_i_apply]
    exact ConcreteCategory.congr_hom
      ((Cech.cechComplex f (M : Type _)).cyclesIsoSc'_hom_iCycles 0 1 2 (by simp) (by simp)) x)

set_option backward.isDefEq.respectTransparency false in
/-- **What the degree-zero comparison is.** The identification of the degree-zero cohomology of the
Čech cone with the degree-one Čech cocycles, followed by the inclusion of the cocycles into the
degree-one Čech term, is the mapping-cone retraction followed by the inclusion of the cycles and
the reindexing isomorphism. This is the form in which the comparison is computed: everything else
about it follows from the corresponding statements for the retraction. -/
theorem cechComplementHomologyZeroIsoKer_hom_comp_subtype :
    (cechComplementHomologyZeroIsoKer.{v} f M).hom ≫
        ModuleCat.ofHom (LinearMap.ker (Cech.cechD f (M : Type _) 1)).subtype =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
          (CochainComplex.mappingCone (extendedCechAugmentation f M)) ≫
        Stacks.MappingCone.homologyCyclesProj (extendedCechAugmentation f M) 0
            (isZero_singleObj_X_neg_one M) ≫
          (extendedCechComplex f M).iCycles 1 ≫ (extendXOneIso f M).hom := by
  rw [cechComplementHomologyZeroIsoKer, Iso.trans_hom, Iso.trans_hom, Category.assoc,
    Category.assoc, cechCyclesOneIsoKer_hom_comp_kerSubtype, extendedCechCyclesOneIso,
    HomologicalComplex.extendCyclesIso_hom_iCycles, cechComplementHomologyZeroIsoCycles_hom,
    Category.assoc]
  rfl

end Comparison

/-! ### Naturality -/

section Naturality

variable {M N : ModuleCat.{max u v} R} (g : M ⟶ N)

set_option backward.isDefEq.respectTransparency false in
/-- The induced map of integer-indexed Čech complexes acts on the degree-one cycles through the
induced map of degree-one Čech terms: the cycles sit inside the degree-one term, and the
reindexing isomorphism identifies the two descriptions of that term. -/
theorem cyclesMap_extendedCechComplexMap_comp_iCycles_comp_extendXOneIso :
    HomologicalComplex.cyclesMap (extendedCechComplexMap f g) 1 ≫
        (extendedCechComplex f N).iCycles 1 ≫ (extendXOneIso f N).hom =
      (extendedCechComplex f M).iCycles 1 ≫ (extendXOneIso f M).hom ≫
        ModuleCat.ofHom (cechTermMap f g 1) := by
  rw [HomologicalComplex.cyclesMap_i_assoc, extendXOneIso, extendXOneIso, extendedCechComplexMap,
    HomologicalComplex.extendMap_f _ _ embeddingUpNat_f_one]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, cechComplexMap_f]

set_option backward.isDefEq.respectTransparency false in
/-- **The degree-zero comparison is natural, as a square of morphisms of modules.** Both sides
are the mapping-cone retraction followed by the inclusion of the cycles, and the retraction is
natural for the morphism of cones induced by the naturality square of the Čech augmentation. -/
theorem cechComplementHomologyZeroIsoKer_hom_comp_subtype_naturality :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          (DerivedCategory.Q.map (CochainComplex.mappingCone.map
            (extendedCechAugmentation f M) (extendedCechAugmentation f N)
            (extendedCechComplexMap f g)
            ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map g)
            (extendedCechAugmentation_naturality f g).symm)) ≫
        (cechComplementHomologyZeroIsoKer.{v} f N).hom ≫
          ModuleCat.ofHom (LinearMap.ker (Cech.cechD f (N : Type _) 1)).subtype =
      ((cechComplementHomologyZeroIsoKer.{v} f M).hom ≫
          ModuleCat.ofHom (LinearMap.ker (Cech.cechD f (M : Type _) 1)).subtype) ≫
        ModuleCat.ofHom (cechTermMap f g 1) := by
  rw [cechComplementHomologyZeroIsoKer_hom_comp_subtype,
    cechComplementHomologyZeroIsoKer_hom_comp_subtype]
  rw [reassoc_of% (DerivedCategory.homologyFunctorFactors_hom_naturality
    (CochainComplex.mappingCone.map (extendedCechAugmentation f M)
      (extendedCechAugmentation f N) (extendedCechComplexMap f g)
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map g)
      (extendedCechAugmentation_naturality f g).symm) (n := 0))]
  rw [reassoc_of% (Stacks.MappingCone.homologyCyclesProj_naturality
    (extendedCechAugmentation_naturality f g).symm 0 (isZero_singleObj_X_neg_one M)
    (isZero_singleObj_X_neg_one N))]
  simp only [Category.assoc]
  congr 2
  exact cyclesMap_extendedCechComplexMap_comp_iCycles_comp_extendXOneIso f g

end Naturality

/-! ### The value on the image of the module -/

section Restriction

variable (M : ModuleCat.{max u v} R)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison of derived-category cohomology with complex-level cohomology undoes the
identification of the degree-`n` cohomology of a module placed in degree `n` with the module. -/
theorem singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctorFactors_hom_app :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} R) 0).inv.app M ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
          ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M) =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).inv := by
  have h : (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} R) 0).inv.app M =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).inv ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).inv.app
          ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M) := by
    simp [DerivedCategory.singleFunctorCompHomologyFunctorIso, SingleFunctors.evaluation,
      DerivedCategory.singleFunctorsPostcompQIso]
  rw [h, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- The second map of the localization triangle is the inclusion of the module into the cone: the
comparison of the two descriptions of a module placed in degree zero is the identity. -/
theorem cechRestriction_app_inr :
    (cechRestriction.{v} f).app M =
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) :=
  Category.id_comp _

/-- The inverse of the augmentation in degree zero, read through the identification of the
degree-zero term of the single complex with the module, is the inverse of the degree-zero Čech
identification.

This is the unconditional form: the augmentation is invertible in degree zero by
`Stacks.LocalCohomology.isIso_extendedCechAugmentation_f_zero`, a local instance here, so no
invertibility hypothesis is carried. -/
theorem singleObjXSelf_inv_comp_inv_augmentation' :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
        inv ((extendedCechAugmentation f M).f 0) = (cechAugIso f M).inv := by
  have h0 : (extendedCechAugmentation f M).f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom = (cechAugIso f M).hom := by
    rw [extendedCechAugmentation_f_zero, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← cancel_mono (cechAugIso f M).hom, Iso.inv_hom_id, ← h0]
  simp

/-- The degree-zero Čech identification, composed with the degree-zero reindexing, is the
identification of the degree-zero term of the `ℕ`-indexed Čech complex with the module. -/
theorem cechAugIso_inv_comp_extendXZeroIso_hom :
    (cechAugIso f M).inv ≫ (extendXZeroIso f M).hom = (cechZeroIso f M).inv := by
  rw [show (cechAugIso f M) = extendXZeroIso f M ≪≫ cechZeroIso f M from rfl, Iso.trans_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- **The retraction on a class coming from the module.** The class of `m` in the degree-zero
cohomology of the Čech cone is carried by the mapping-cone retraction to the degree-zero Čech
differential applied to the preimage of `m` under the degree-zero identification. -/
theorem singleObjHomologySelfIso_inv_comp_homologyMap_inr :
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).inv ≫
        HomologicalComplex.homologyMap
            (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) 0 ≫
          Stacks.MappingCone.homologyCyclesProj (extendedCechAugmentation f M) 0
              (isZero_singleObj_X_neg_one M) ≫
            (extendedCechComplex f M).iCycles 1 ≫ (extendXOneIso f M).hom =
      (cechZeroIso f M).inv ≫ (Cech.cechComplex f (M : Type _)).d 0 1 := by
  have h : ((HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0).obj M
        ).homologyπ 0 ≫
        HomologicalComplex.homologyMap
            (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) 0 ≫
          Stacks.MappingCone.homologyCyclesProj (extendedCechAugmentation f M) 0
              (isZero_singleObj_X_neg_one M) ≫
            (extendedCechComplex f M).iCycles 1 ≫ (extendXOneIso f M).hom =
      ((HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0).obj M
        ).iCycles 0 ≫
        inv ((extendedCechAugmentation f M).f 0) ≫ (extendedCechComplex f M).d 0 1 ≫
          (extendXOneIso f M).hom :=
    (reassoc_of% (Stacks.MappingCone.homologyπ_homologyMap_inr_comp_homologyCyclesProj
      (extendedCechAugmentation f M) 0 (isZero_singleObj_X_neg_one M)))
        (extendXOneIso f M).hom
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ (ComplexShape.up ℤ) 0 M,
    Category.assoc, h, HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc,
    ← Category.assoc, singleObjXSelf_inv_comp_inv_augmentation' f M,
    HomologicalComplex.extend_d_eq _ _ ComplexShape.embeddingUpNat_f_zero embeddingUpNat_f_one,
    extendXOneIso]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc,
    show (HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
        ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero).hom =
          (extendXZeroIso f M).hom from rfl,
    cechAugIso_inv_comp_extendXZeroIso_hom f M]

set_option backward.isDefEq.respectTransparency false in
/-- **The degree-zero comparison on the image of the module.** The class of `m` in the degree-zero
cohomology of derived sections on `U` is carried, by the comparison with the degree-one Čech
cocycles, to the degree-zero Čech differential applied to the constant fraction `m / 1`. -/
theorem cechRestriction_comp_cechComplementHomologyZeroIsoKer_hom_comp_subtype :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} R) 0).inv.app M ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
            ((cechRestriction.{v} f).app M) ≫
          (cechComplementHomologyZeroIsoKer.{v} f M).hom ≫
            ModuleCat.ofHom (LinearMap.ker (Cech.cechD f (M : Type _) 1)).subtype =
      (cechZeroIso f M).inv ≫ (Cech.cechComplex f (M : Type _)).d 0 1 := by
  rw [cechRestriction_app_inr, cechComplementHomologyZeroIsoKer_hom_comp_subtype,
    reassoc_of% (DerivedCategory.homologyFunctorFactors_hom_naturality
      (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) (n := 0)),
    reassoc_of% (singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctorFactors_hom_app
      (R := R) M)]
  exact singleObjHomologySelfIso_inv_comp_homologyMap_inr f M

/-- **The degree-zero Čech differential on a constant fraction.** Each coordinate of
`d⁰(m / 1)` is the constant fraction `m / 1`: only the index inserted into the empty set
contributes, and its sign is `+1`.

The argument is spelled as the summand inclusion `DirectSum.lof` at the empty index, the form in
which `Stacks.LocalCohomology.cechTermZeroEquiv_symm_apply` presents it. -/
theorem cechComponentOne_cechD_zero_lof (m : M) (i : Fin r) :
    cechComponentOne f M i (Cech.cechD f (M : Type _) 0
        (DirectSum.lof R (ExtendedAlternatingCech.Idx r 0)
          (fun s => Cech.cechMod f (M : Type _) s.1) default
          (LocalizedModule.mkLinearMap (Cech.cechSub f (∅ : Finset (Fin r))) (M : Type _) m))) =
      LocalizedModule.mkLinearMap (Cech.cechSub f ({i} : Finset (Fin r))) (M : Type _) m := by
  have hd : ((default : ExtendedAlternatingCech.Idx r 0) : Finset (Fin r)) = ∅ := rfl
  rw [Cech.cechD_lof, map_sum]
  simp only [map_zsmul]
  refine (Finset.sum_eq_single_of_mem ⟨i, by simp [hd]⟩
    (Finset.mem_attach _ _) (fun j _ hj => ?_)).trans ?_
  · rw [cechComponent_lof_of_ne f M _ _ (fun he => hj (Subtype.ext ?_)), zsmul_zero]
    have he' : insert j.1 (∅ : Finset (Fin r)) = {i} := he
    simpa using he'
  · rw [show Cech.cechSign ((default : ExtendedAlternatingCech.Idx r 0) : Finset (Fin r)) i = 1 from
      by simp [Cech.cechSign, hd], one_smul]
    exact (cechComponent_lof_of_eq f M _ ⟨{i}, Finset.card_singleton i⟩ rfl _).trans
      ((Cech.cechι_cechι f (M : Type _) _ _ _).trans (Cech.cechι_mk f (M : Type _) _ m))

end Restriction

end Stacks.LocalCohomology

end
