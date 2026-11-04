module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.CechFunctor
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero

/-!
# The Čech augmentation as a natural transformation

The augmentation `C^•(f₁, …, f_r; M) ⟶ M⟦0⟧` of the extended alternating Čech complex is the
identity on `M` in degree zero and zero elsewhere. It is natural in `M`, both as a map of cochain
complexes and in the derived category.

## Main definitions

* `Stacks.LocalCohomology.cechAugmentation`: the augmentation as a natural transformation of
  functors into cochain complexes.
* `Stacks.LocalCohomology.cechAugmentationHom`: the augmentation as a natural transformation of
  functors into the derived category.

## Main results

* `Stacks.LocalCohomology.cechTermZeroEquiv_naturality`: the identification of the degree-zero
  term of the Čech complex with the module is natural.
* `Stacks.LocalCohomology.extendedCechAugmentation_naturality`: the augmentation is natural.
* `Stacks.LocalCohomology.cechAugmentationHom_app`: the derived-category transformation is, at
  each module, the map `Stacks.LocalCohomology.extendedCechAugmentationHom`.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) {M N : ModuleCat.{max u v} R}

/-! ### Naturality of the degree-zero identification -/

/-- The identification of the localization of `M` at the empty subset with `M` is natural. -/
theorem cechModEmptyEquiv_naturality (g : M ⟶ N)
    (x : Cech.cechMod f M (∅ : Finset (Fin r))) :
    Stacks.CechBaseChange.cechModEmptyEquiv f N (cechModMap f g ∅ x) =
      g (Stacks.CechBaseChange.cechModEmptyEquiv f M x) := by
  obtain ⟨m, rfl⟩ : ∃ m, x = LocalizedModule.mkLinearMap (Cech.cechSub f ∅) M m :=
    ⟨Stacks.CechBaseChange.cechModEmptyEquiv f M x, by
      rw [← Stacks.CechBaseChange.cechModEmptyEquiv_symm_apply, LinearEquiv.symm_apply_apply]⟩
  rw [cechModMap_mkLinearMap, Stacks.CechBaseChange.cechModEmptyEquiv_mk,
    Stacks.CechBaseChange.cechModEmptyEquiv_mk]

/-- On the summand indexed by the empty set, the identification of the degree-zero term of the
Čech complex with `M` is the identification of the localization at the empty subset. -/
theorem cechTermZeroEquiv_lof
    (x : Cech.cechMod f M (default : ExtendedAlternatingCech.Idx r 0).1) :
    cechTermZeroEquiv f M (DirectSum.lof R (ExtendedAlternatingCech.Idx r 0)
        (fun s => Cech.cechMod f M s.1) default x) =
      Stacks.CechBaseChange.cechModEmptyEquiv f M x := by
  simp [cechTermZeroEquiv]

/-- The identification of the degree-zero term of the Čech complex with the module is natural. -/
theorem cechTermZeroEquiv_naturality (g : M ⟶ N) (x : Cech.cechTerm f M 0) :
    cechTermZeroEquiv f N (cechTermMap f g 0 x) = g (cechTermZeroEquiv f M x) := by
  have h : (cechTermZeroEquiv f N).toLinearMap.comp (cechTermMap f g 0) =
      g.hom.comp (cechTermZeroEquiv f M).toLinearMap := by
    refine DirectSum.linearMap_ext R fun s => LinearMap.ext fun y => ?_
    obtain rfl : s = default := Subsingleton.elim _ _
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, cechTermMap_lof, cechTermZeroEquiv_lof,
      cechTermZeroEquiv_lof]
    exact cechModEmptyEquiv_naturality f g y
  exact LinearMap.congr_fun h x

/-- The reindexing isomorphism in degree zero. -/
def extendXZeroIso (M : ModuleCat.{max u v} R) :
    (extendedCechComplex f M).X 0 ≅ (Cech.cechComplex f M).X 0 :=
  HomologicalComplex.extendXIso (Cech.cechComplex f M) ComplexShape.embeddingUpNat
    ComplexShape.embeddingUpNat_f_zero

/-- The identification of the degree-zero term of the `ℕ`-indexed Čech complex with the
module. -/
def cechZeroIso (M : ModuleCat.{max u v} R) :
    (Cech.cechComplex f M).X 0 ≅ ModuleCat.of R M :=
  (cechTermZeroEquiv f M).toModuleIso

/-- The degree-zero identification of the integer-indexed Čech complex, split into the
reindexing isomorphism and the identification of the degree-zero Čech term. -/
theorem extendedCechXZeroIso_hom (M : ModuleCat.{max u v} R) :
    (extendedCechXZeroIso f M).hom = (extendXZeroIso f M).hom ≫ (cechZeroIso f M).hom :=
  rfl

/-- The degree-zero component of a map of complexes concentrated in degree zero. -/
theorem singleFunctor_map_f_zero {X Y : ModuleCat.{max u v} R} (φ : X ⟶ Y) :
    ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map φ).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ φ ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).inv :=
  HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 φ

/-- The identification of the degree-zero term of the integer-indexed Čech complex with the
module is natural. -/
theorem extendedCechXZeroIso_naturality (g : M ⟶ N) :
    (extendedCechComplexMap f g).f 0 ≫ (extendedCechXZeroIso f N).hom =
      (extendedCechXZeroIso f M).hom ≫ g := by
  have hmap : (extendedCechComplexMap f g).f 0 =
      (extendXZeroIso f M).hom ≫ (cechComplexMap f g).f 0 ≫ (extendXZeroIso f N).inv :=
    HomologicalComplex.extendMap_f _ _ ComplexShape.embeddingUpNat_f_zero
  have hzero : (cechComplexMap f g).f 0 ≫ (cechZeroIso f N).hom =
      (cechZeroIso f M).hom ≫ g :=
    ModuleCat.hom_ext (LinearMap.ext fun x => cechTermZeroEquiv_naturality f g x)
  simp only [extendedCechXZeroIso_hom, hmap, Category.assoc, Iso.inv_hom_id_assoc, hzero]

/-- The degree-zero identification, with target the module itself. -/
def cechAugIso (M : ModuleCat.{max u v} R) : (extendedCechComplex f M).X 0 ≅ M :=
  extendedCechXZeroIso f M

/-- The degree-zero identification with target the module is natural. -/
theorem cechAugIso_naturality (g : M ⟶ N) :
    (extendedCechComplexMap f g).f 0 ≫ (cechAugIso f N).hom =
      (cechAugIso f M).hom ≫ g :=
  extendedCechXZeroIso_naturality f g

/-! ### The augmentation as a natural transformation -/

/-- In degree zero the augmentation is the identification of the degree-zero term with the
module. -/
theorem extendedCechAugmentation_f_zero (M : ModuleCat.{max u v} R) :
    (extendedCechAugmentation f M).f 0 = (cechAugIso f M).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv := by
  rw [extendedCechAugmentation, HomologicalComplex.comp_f, bottomProjection,
    HomologicalComplex.mkHomToSingle_f, singleFunctor_map_f_zero]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc]
  rfl

/-- The augmentation of the Čech complex is natural in the module. -/
theorem extendedCechAugmentation_naturality (g : M ⟶ N) :
    extendedCechComplexMap f g ≫ extendedCechAugmentation f N =
      extendedCechAugmentation f M ≫
        (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map g := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, extendedCechAugmentation_f_zero,
    extendedCechAugmentation_f_zero, singleFunctor_map_f_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, cechAugIso_naturality, Category.assoc]

/-- The augmentation of the extended alternating Čech complex, as a natural transformation to the
functor placing a module in degree zero. -/
def cechAugmentation :
    extendedCechFunctor.{v} f ⟶ CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0 where
  app M := extendedCechAugmentation f M
  naturality _ _ g := extendedCechAugmentation_naturality f g

/-- The augmentation in the derived category, as a natural transformation. -/
def cechAugmentationHom :
    extendedCechObjectFunctor.{v} f ⟶ DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0 :=
  Functor.whiskerRight (cechAugmentation.{v} f) DerivedCategory.Q ≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).inv

/-- At each module the derived-category augmentation is the map of the Čech model. -/
@[simp] theorem cechAugmentationHom_app (M : ModuleCat.{max u v} R) :
    (cechAugmentationHom.{v} f).app M = extendedCechAugmentationHom f M := rfl

end Stacks.LocalCohomology

end
