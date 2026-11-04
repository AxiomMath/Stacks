module

public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Data.MappingConeNaturality
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Reduction
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Restriction
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The low-degree sequence of local cohomology, unconditionally

Let `I` be a finitely generated ideal of a commutative ring `A` and let `U = Spec A \ V(I)`.
`StacksFrontier/RingTheory/LocalCohomology/LowDegree/ExactSequence.lean` proves the exactness
statements of the low-degree sequence
`0 ⟶ H⁰_I(M) ⟶ M ⟶ Γ(U, F) ⟶ H¹_I(M) ⟶ 0`
relative to a `Stacks.LocalCohomology.LocalizationTriangleData`, and
`StacksFrontier/RingTheory/LocalCohomology/SectionsIso/Reduction.lean` reduces the existence of such
data to two statements about the degree-zero cohomology of the Čech cone alone. This file proves
those two statements, produces the data unconditionally, and assembles the four-term exact
sequence.

Both statements concern `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer`, the
identification of `H⁰` of the cone of the Čech augmentation with the degree-one Čech cocycles. That
identification is a composite of three isomorphisms, and each of the two statements is obtained by
chaining the corresponding property of the three factors: the comparison of the cohomology of a
mapping cone with the cycles of its source
(`Stacks.MappingCone.homologyIsoCycles_hom_naturality`,
`Stacks.MappingCone.coneCyclesProj_comp_cyclesMap_inr_comp_iCycles`), the reindexing of the Čech
complex from natural-number to integer degrees
(`HomologicalComplex.extendCyclesIso_hom_naturality`), and the description of the degree-one cycles
as a kernel of linear maps. In both cases the composite is pinned down by composing with the
inclusion of the cocycles into the degree-one Čech term, which is a monomorphism.

## Main definitions

* `Stacks.LocalCohomology.localizationTriangleData` — **the affine localization triangle data of
  Stacks 0DWR, for an arbitrary finitely generated ideal, with no auxiliary hypothesis**.

## Main results

* `Stacks.LocalCohomology.exact_lowDegreeSequence` — **Stacks 0BK0, part (2): the four-term
  sequence `0 ⟶ H⁰_I(M) ⟶ M ⟶ Γ(U, F) ⟶ H¹_I(M) ⟶ 0` is exact.**

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite AlgebraicGeometry CochainComplex

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-! ### The inclusion of the degree-one cocycles -/

/-- The inclusion of the degree-one Čech cocycles into the degree-one term of the Čech complex,
as a morphism of `R`-modules whose target is spelled as that term of the complex. -/
def kerCechDOneSubtype (M : ModuleCat.{max u v} R) :
    ModuleCat.of R (LinearMap.ker (Cech.cechD f (M : Type _) 1)) ⟶
      (Cech.cechComplex f (M : Type _)).X 1 :=
  ModuleCat.ofHom (LinearMap.ker (Cech.cechD f (M : Type _) 1)).subtype

/-- The inclusion of the cocycles is the coercion of a subtype. -/
@[simp] theorem kerCechDOneSubtype_apply (M : ModuleCat.{max u v} R)
    (x : LinearMap.ker (Cech.cechD f (M : Type _) 1)) :
    kerCechDOneSubtype f M x = x.1 :=
  rfl

/-- The inclusion of the degree-one cocycles is a monomorphism. -/
instance mono_kerCechDOneSubtype (M : ModuleCat.{max u v} R) :
    Mono (kerCechDOneSubtype f M) :=
  (ModuleCat.mono_iff_injective _).2 Subtype.val_injective

/-- The degree-zero comparison, split into its three factors. -/
theorem cechComplementHomologyZeroIsoKer_hom (M : ModuleCat.{max u v} R) :
    (cechComplementHomologyZeroIsoKer.{v} f M).hom =
      (cechComplementHomologyZeroIsoCycles.{v} f M).hom ≫
        (extendedCechCyclesOneIso.{v} f M).hom ≫ (cechCyclesOneIsoKer f M).hom :=
  rfl

/-- **What the identification of the degree-one cycles with a kernel does.** Composed with the
inclusion of the cocycles into the degree-one Čech term it is the inclusion of the cycles: the
kernel is the one supplied by the explicit left homology data of the short complex in degrees
`0, 1, 2`, whose inclusion into the middle term is exactly that subtype. -/
@[reassoc]
theorem cechCyclesOneIsoKer_hom_comp_subtype (M : ModuleCat.{max u v} R) :
    (cechCyclesOneIsoKer f M).hom ≫ kerCechDOneSubtype f M =
      (Cech.cechComplex f (M : Type _)).iCycles 1 := by
  have hsub : ∀ h : ((Cech.cechComplex f (M : Type _)).sc' 0 1 2).moduleCatLeftHomologyData.K =
        ModuleCat.of R (LinearMap.ker (Cech.cechD f (M : Type _) 1)),
      eqToHom h ≫ kerCechDOneSubtype f M =
        ((Cech.cechComplex f (M : Type _)).sc' 0 1 2).moduleCatLeftHomologyData.i :=
    fun _ => rfl
  rw [cechCyclesOneIsoKer]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [hsub]
  exact (congrArg (((Cech.cechComplex f (M : Type _)).cyclesIsoSc' 0 1 2
        (by simp) (by simp)).hom ≫ ·)
      (ShortComplex.moduleCatCyclesIso_hom_i
        ((Cech.cechComplex f (M : Type _)).sc' 0 1 2))).trans
    (HomologicalComplex.cyclesIsoSc'_hom_iCycles (Cech.cechComplex f (M : Type _)) 0 1 2
      (by simp) (by simp))

/-! ### Naturality of the degree-zero comparison -/

/-- The module `M` placed in degree zero has no other nonzero terms. -/
private theorem isZero_single_X (M : ModuleCat.{max u v} R) {i : ℤ} (h : i ≠ 0) :
    IsZero (((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M).X i) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M _ h

section Naturality

variable {M N : ModuleCat.{max u v} R}

/-- A module map acts on the degree-one cocycles by its action on the degree-one Čech term. -/
theorem kerCechDOneMap_comp_subtype (g : M ⟶ N) :
    ModuleCat.ofHom (kerCechDOneMap f g) ≫ kerCechDOneSubtype f N =
      kerCechDOneSubtype f M ≫ (cechComplexMap f g).f 1 :=
  ModuleCat.hom_ext (LinearMap.ext fun x => kerCechDOneMap_coe f g x)

/-- **The comparison of `H⁰` of the Čech cone with the degree-one cycles is natural in the
module.** This is the naturality of `Stacks.MappingCone.homologyIsoCycles` in the square expressing
that the Čech augmentation is a natural transformation, together with the fact that the homology
functor on the derived category is induced by the one on cochain complexes. -/
theorem cechComplementHomologyZeroIsoCycles_hom_naturality (g : M ⟶ N) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
        ((cechComplementFunctor.{v} f).map g) ≫
        (cechComplementHomologyZeroIsoCycles.{v} f N).hom =
      (cechComplementHomologyZeroIsoCycles.{v} f M).hom ≫
        HomologicalComplex.cyclesMap (extendedCechComplexMap f g) 1 := by
  have := isIso_extendedCechAugmentation_f_zero f M
  have := isIso_extendedCechAugmentation_f_zero f N
  have hfac := (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.naturality
    ((cechConeFunctor.{v} f).map g)
  have hcone := Stacks.MappingCone.homologyIsoCycles_hom_naturality
    (extendedCechAugmentation_naturality f g).symm 0
    (isZero_single_X M (by omega))
    (isZero_single_X M (by omega))
    (isZero_single_X N (by omega))
    (isZero_single_X N (by omega))
  exact ((reassoc_of% hfac) _).trans
    (congrArg ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.app
      ((cechConeFunctor.{v} f).obj M) ≫ ·) hcone)

/-- **The degree-zero comparison with the degree-one cocycles is natural in the module.** All
three factors are: the cone comparison in the augmentation square, the reindexing of the Čech
complex, and the description of the cycles as a kernel. -/
theorem cechComplementHomologyZeroIsoKer_hom_naturality (g : M ⟶ N) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
        ((cechComplementFunctor.{v} f).map g) ≫
        (cechComplementHomologyZeroIsoKer.{v} f N).hom =
      (cechComplementHomologyZeroIsoKer.{v} f M).hom ≫
        ModuleCat.ofHom (kerCechDOneMap f g) := by
  have h1 := cechComplementHomologyZeroIsoCycles_hom_naturality f g
  have h2 := HomologicalComplex.extendCyclesIso_hom_naturality (cechComplexMap f g)
    ComplexShape.embeddingUpNat (j := 1) (j' := 1) (by simp)
  rw [← cancel_mono (kerCechDOneSubtype f N), cechComplementHomologyZeroIsoKer_hom,
    cechComplementHomologyZeroIsoKer_hom]
  simp only [Category.assoc]
  rw [cechCyclesOneIsoKer_hom_comp_subtype, kerCechDOneMap_comp_subtype,
    cechCyclesOneIsoKer_hom_comp_subtype_assoc, reassoc_of% h1,
    show extendedCechComplexMap f g =
      HomologicalComplex.extendMap (cechComplexMap f g) ComplexShape.embeddingUpNat from rfl,
    extendedCechCyclesOneIso, extendedCechCyclesOneIso, reassoc_of% h2,
    HomologicalComplex.cyclesMap_i]

end Naturality

/-! ### The value of the degree-zero comparison on the image of the module -/

variable (M : ModuleCat.{max u v} R)

/-- The canonical comparison `H⁰(M⟦0⟧) ≅ M` of the derived category comes from the homology of the
single cochain complex: by definition the embedding of modules in the derived category is the
single cochain complex followed by the localization functor. -/
theorem singleFunctorCompHomologyFunctorIso_inv_app :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} R) 0).inv.app M =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).inv ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).inv.app
          ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M) := by
  simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.singleFunctorsPostcompQIso]
  rfl

/-- The restriction map of the localization triangle is the canonical inclusion of the module,
placed in degree zero, into the cone of the Čech augmentation. -/
theorem cechRestriction_app :
    (cechRestriction.{v} f).app M =
      (singleIsoQ.{v} (R := R) M).hom ≫ DerivedCategory.Q.map (cechConeInr.{v} f M) :=
  rfl

/-- The comparison of the two descriptions of a module placed in degree zero is the identity. -/
theorem singleIsoQ_hom : (singleIsoQ.{v} (R := R) M).hom = 𝟙 _ := rfl

/-- The inverse of the augmentation in degree zero, read through the identification of the
degree-zero term of the single complex with the module, is the inverse of the degree-zero
identification of the Čech complex. -/
@[reassoc]
theorem singleObjXSelf_inv_comp_inv_extendedCechAugmentation_f_zero
    [IsIso ((extendedCechAugmentation f M).f 0)] :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
        inv ((extendedCechAugmentation f M).f 0) = (extendedCechXZeroIso f M).inv := by
  rw [← cancel_mono ((extendedCechAugmentation f M).f 0), Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, extendedCechAugmentation_f_zero, cechAugIso, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- **The restriction map, read on the degree-one cycles of the integer-indexed Čech complex.**
The canonical inclusion of the module into the cone lands in the second biproduct summand, on
which the retraction `Stacks.MappingCone.coneCyclesProj` is the boundary of the preimage under the
augmentation. -/
@[reassoc]
theorem restriction_comp_cechComplementHomologyZeroIsoCycles_hom_comp_iCycles :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} R) 0).inv.app M ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          ((cechRestriction.{v} f).app M) ≫ (cechComplementHomologyZeroIsoCycles.{v} f M).hom ≫
        (extendedCechComplex f M).iCycles 1 =
      (extendedCechXZeroIso f M).inv ≫ (extendedCechComplex f M).d 0 1 := by
  have := isIso_extendedCechAugmentation_f_zero f M
  have hfacHom := (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).hom.naturality
    (CochainComplex.mappingCone.inr (extendedCechAugmentation f M))
  have hinr := Stacks.MappingCone.coneCyclesProj_comp_cyclesMap_inr_comp_iCycles
    (extendedCechAugmentation f M) 0
  have hmid : (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).inv.app
        ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          (DerivedCategory.Q.map
            (CochainComplex.mappingCone.inr (extendedCechAugmentation f M))) ≫
        (cechComplementHomologyZeroIsoCycles.{v} f M).hom ≫
          (extendedCechComplex f M).iCycles 1 =
      HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) 0 ≫
        (Stacks.MappingCone.homologyIsoCycles (extendedCechAugmentation f M) 0
            (isZero_single_X M (by omega))
            (isZero_single_X M (by omega))).hom ≫
          (extendedCechComplex f M).iCycles 1 :=
    (congrArg ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) 0).inv.app
        ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M) ≫ ·)
      ((reassoc_of% hfacHom)
        ((Stacks.MappingCone.homologyIsoCycles (extendedCechAugmentation f M) 0
            (isZero_single_X M (by omega))
            (isZero_single_X M (by omega))).hom ≫ (extendedCechComplex f M).iCycles 1))).trans
      (by
        simp only [Iso.inv_hom_id_app_assoc, HomologicalComplex.homologyFunctor_map]
        rfl)
  have hstep : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).inv ≫
        HomologicalComplex.homologyMap
            (CochainComplex.mappingCone.inr (extendedCechAugmentation f M)) 0 ≫
          (Stacks.MappingCone.homologyIsoCycles (extendedCechAugmentation f M) 0
              (isZero_single_X M (by omega))
              (isZero_single_X M (by omega))).hom ≫
            (extendedCechComplex f M).iCycles 1 =
      (extendedCechXZeroIso f M).inv ≫ (extendedCechComplex f M).d 0 1 := by
    rw [show (Stacks.MappingCone.homologyIsoCycles (extendedCechAugmentation f M) 0
          (isZero_single_X M (by omega))
          (isZero_single_X M (by omega))).hom =
        Stacks.MappingCone.homologyCyclesProj (extendedCechAugmentation f M) 0
          (isZero_single_X M (by omega)) from rfl,
      ← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ, Category.assoc,
      HomologicalComplex.homologyπ_naturality_assoc,
      reassoc_of% (Stacks.MappingCone.homologyπ_comp_homologyCyclesProj
        (extendedCechAugmentation f M) 0
        (isZero_single_X M (by omega)))]
    exact (congrArg ((HomologicalComplex.singleObjCyclesSelfIso
          (ComplexShape.up ℤ) 0 M).inv ≫ ·) hinr).trans
      ((HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc (ComplexShape.up ℤ) 0 M
          (inv ((extendedCechAugmentation f M).f 0) ≫ (extendedCechComplex f M).d 0 1)).trans
        (singleObjXSelf_inv_comp_inv_extendedCechAugmentation_f_zero_assoc f M
          ((extendedCechComplex f M).d 0 1)))
  rw [singleFunctorCompHomologyFunctorIso_inv_app, cechRestriction_app, singleIsoQ_hom,
    Category.id_comp]
  exact (congrArg ((HomologicalComplex.singleObjHomologySelfIso
    (ComplexShape.up ℤ) 0 M).inv ≫ ·) hmid).trans hstep

/-- **The restriction map, read on the degree-one Čech cocycles.** Composing with the inclusion of
the cocycles into the degree-one Čech term, the class of `m` goes to the degree-zero Čech
differential of `m` placed in the summand indexed by the empty set. -/
theorem restriction_comp_cechComplementHomologyZeroIsoKer_hom_comp_subtype :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} R) 0).inv.app M ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          ((cechRestriction.{v} f).app M) ≫ (cechComplementHomologyZeroIsoKer.{v} f M).hom ≫
        kerCechDOneSubtype f M =
      (cechZeroIso f M).inv ≫ (Cech.cechComplex f (M : Type _)).d 0 1 := by
  have hz : (extendedCechXZeroIso f M).inv =
      (cechZeroIso f M).inv ≫
        (HomologicalComplex.extendXIso (Cech.cechComplex f (M : Type _))
          ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero).inv := rfl
  rw [cechComplementHomologyZeroIsoKer_hom]
  simp only [Category.assoc]
  rw [cechCyclesOneIsoKer_hom_comp_subtype, extendedCechCyclesOneIso,
    HomologicalComplex.extendCyclesIso_hom_iCycles]
  refine (restriction_comp_cechComplementHomologyZeroIsoCycles_hom_comp_iCycles_assoc.{v}
    f M _).trans ?_
  rw [hz, HomologicalComplex.extend_d_eq (Cech.cechComplex f (M : Type _))
    ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero
    (show ComplexShape.embeddingUpNat.f 1 = 1 by simp)]
  simp

/-! ### The degree-zero Čech differential on a constant fraction -/

/-- **The degree-zero Čech differential of a constant fraction.** The `i`-th coordinate of
`d⁰ (m / 1)` is the constant fraction `m / 1` in `M_{f_i}`: only the index `i` contributes to that
coordinate, the sign attached to inserting `i` into the empty set is `+1`, and the transition map
from `M_∅` carries `m / 1` to `m / 1`. -/
theorem cechComponentOne_cechD_zero (m : M) (i : Fin r) :
    cechComponentOne f M i (Cech.cechD f (M : Type _) 0 ((cechTermZeroEquiv f M).symm m)) =
      LocalizedModule.mkLinearMap (Cech.cechSub f {i}) (M : Type _) m := by
  rw [cechTermZeroEquiv_symm_apply, Cech.cechD_lof, map_sum]
  refine (Finset.sum_eq_single_of_mem
    ⟨i, Finset.mem_compl.2 (Finset.notMem_empty i)⟩ (Finset.mem_attach _ _) fun j _ hj => ?_).trans
    ?_
  · rw [map_zsmul, cechComponent_lof_of_ne f M _ _ ?_, zsmul_zero]
    refine fun he => hj (Subtype.ext ?_)
    have he' : insert j.1 (∅ : Finset (Fin r)) = {i} := he
    exact Finset.mem_singleton.1 (he' ▸ Finset.mem_insert_self j.1 ∅)
  · rw [map_zsmul, cechComponent_lof_of_eq f M _ _
      (show insert i (∅ : Finset (Fin r)) = {i} by simp), Cech.cechι_cechι,
      Cech.cechι_mk f (M : Type _) (Finset.empty_subset ({i} : Finset (Fin r))) m]
    simp [Cech.cechSign,
      show ((default : ExtendedAlternatingCech.Idx r 0) : Finset (Fin r)) = ∅ from rfl]

/-! ### The localization triangle data, unconditionally -/

section Existence

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

/-- **The affine localization triangle of Stacks 0DWR, for any finitely generated ideal.** The
Čech construction needs a finite generating family for `I`, which finite generation supplies; a
choice is made, so the resulting data depends on that choice, but its existence does not. Both
remaining hypotheses of
`Stacks.LocalCohomology.localizationTriangleDataOfCechHomologyComparison` are now theorems:
`Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer_naturality` and
`Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer_restriction`. -/
def localizationTriangleData : LocalizationTriangleData.{u, max u v} A I hI :=
  localizationTriangleDataOfCechHomologyComparison
    (Submodule.fg_iff_exists_fin_generating_family.mp hI).choose_spec.choose I hI
    (Submodule.fg_iff_exists_fin_generating_family.mp hI).choose_spec.choose_spec
    (fun g z => cechComplementHomologyZeroEquivKer_naturality.{v} _ g z)
    (fun M m i => cechComplementHomologyZeroEquivKer_restriction.{v} _ M m i)

/-- **Stacks 0BK0, the low-degree sequence.** Let `I` be a finitely generated ideal of a
commutative ring `A`, let `U = Spec A \ V(I)`, let `M` be an `A`-module and let `F` be a sheaf of
modules on `U` identified with the restriction to `U` of the sheaf associated to `M`. Then the
four-term sequence
`0 ⟶ H⁰_I(M) ⟶ M ⟶ Γ(U, F) ⟶ H¹_I(M) ⟶ 0`
is exact: the map out of degree-zero local cohomology is injective, the sequence is exact at `M`
and at `Γ(U, F)`, and the connecting map onto `H¹_I(M)` is surjective.

Every ideal of a Noetherian ring is finitely generated, by `Ideal.fg_of_isNoetherianRing`, so
this covers the Noetherian hypothesis of the source; and it does not assume `M` finite or `F`
coherent, which the source does.

The same four-term sequence is the first half of clause (2) of Stacks 0DWR, which assumes only
that `I` is finitely generated. The second half of that clause, the comparison
`H^p(U, F) ≅ H^{p+1}_I(M)` in degrees `p ≥ 1`, `A`-linearly and for the same `F` and `M`, is
`Stacks.LocalCohomology.nonempty_complementSheafCohomology_iso_localCohomologyModule`, under the
same hypothesis `I.FG`. -/
@[stacks 0BK0 "low_degree_sequence",
  stacks 0DWR "low_degree_sequence",
  sga "2 II Corollary4" "(4.2)",
  ega "III 1.4.3" "(1.4.3.2), special case",
  sga "4 V 6.5" "(6.5.3), special case"]
theorem exact_lowDegreeSequence (M : ModuleCat.{max u v} A)
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) :
    Function.Injective (localCohomologyZeroToModule A I hI M).hom ∧
      Function.Exact (localCohomologyZeroToModule A I hI M)
        (restrictionToComplement (localizationTriangleData.{v} A I hI) M F e) ∧
      Function.Exact (restrictionToComplement (localizationTriangleData.{v} A I hI) M F e)
        (localizationBoundary (localizationTriangleData.{v} A I hI) M F e) ∧
      Function.Surjective (localizationBoundary (localizationTriangleData.{v} A I hI) M F e) :=
  ⟨localCohomologyZeroToModule_injective A I hI M,
    exact_localCohomologyZeroToModule_restrictionToComplement _ M F e,
    exact_restrictionToComplement_localizationBoundary _ M F e,
    localizationBoundary_surjective _ M F e⟩

end Existence

end Stacks.LocalCohomology

end
