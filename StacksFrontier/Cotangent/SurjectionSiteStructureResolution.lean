module

public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCoefficientChange
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex
public import StacksFrontier.Cotangent.SurjectionSiteZerothSymmetricPower

/-!
# The structure presheaf of `C_{B/A}` as a free resolution of `B` over `A`

Let `A` be a commutative ring, `B` an `A`-algebra, `κ = CommAlgCat.standardResolutionVarCardinal
A B` the cardinal bounding the standard resolution, and `U_•` the unconditional cosimplicial
point resolution `CommAlgCat.standardResolutionSmallCosimplicialObject A B` of the small model of
the polynomial site `C_{B/A}`. The tautological presheaf `𝒪` of that site sends an object
`(P, α)` to the polynomial `A`-algebra `P`; read as a presheaf of `A`-modules and evaluated on
`U_•`, its Moore complex

`⋯ ⟶ 𝒪(U_2) ⟶ 𝒪(U_1) ⟶ 𝒪(U_0)`

is a complex of free `A`-modules which resolves `B`: it is exact in positive degrees, and the
augmentation `𝒪 ⟶ B̲` identifies its degree-zero homology with `B`.

## Main definitions

* `CommAlgCat.overModuleFunctor` and `CommAlgCat.overModuleAugmentation`: an `A`-algebra over `B`
  read as an `A`-module, and its structure morphism read as an `A`-linear map to `B`.
* `CommAlgCat.smallPolynomialStructureModulePresheaf`: the tautological presheaf `𝒪` of the small
  model of `C_{B/A}`, with values in `A`-modules.
* `CommAlgCat.smallPolynomialModuleAugmentation`: the augmentation `𝒪 ⟶ B̲` of presheaves of
  `A`-modules.
* `CommAlgCat.smallPolynomialStructureModuleMooreComplex`: the Moore complex of `𝒪(U_•)`.
* `CommAlgCat.smallPolynomialStructureModuleMooreAugmentationHomologyZero` and
  `CommAlgCat.smallPolynomialStructureModuleMooreHomologyZeroIso`: the map `H_0 ⟶ B` induced by
  the augmentation, and the isomorphism it is.

## Main results

* `CommAlgCat.module_free_smallPolynomialStructureModuleMooreComplex_X`: every term of the Moore
  complex is a free `A`-module.
* `CommAlgCat.isZero_homology_smallPolynomialStructureModuleMooreComplex_succ`: the homology
  vanishes in every positive degree.
* `CommAlgCat.isIso_smallPolynomialStructureModuleMooreAugmentationHomologyZero`: the map
  `H_0 ⟶ B` induced by the augmentation is an isomorphism.

## References

* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### Objects over `B`, read as `A`-modules -/

/-- An `A`-algebra over `B`, read as an `A`-module: forget the structure morphism to `B`, then
the multiplication. -/
def overModuleFunctor : Over B ⥤ ModuleCat.{u} A :=
  Over.forget B ⋙ forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙
    forget₂ (AlgCat.{u} A) (ModuleCat.{u} A)

/-- **The augmentation of an `A`-algebra over `B`**, read as an `A`-linear map into `B`: the
structure morphism of the object of `Over B`. -/
def overModuleAugmentation :
    overModuleFunctor A B ⟶ (Functor.const (Over B)).obj (ModuleCat.of A (B : Type u)) where
  app P := (forget₂ (AlgCat.{u} A) (ModuleCat.{u} A)).map
    ((forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A)).map P.hom)
  naturality P Q f := by
    have hw := congrArg
      (fun g : P.left ⟶ B => (forget₂ (AlgCat.{u} A) (ModuleCat.{u} A)).map
        ((forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A)).map g)) (Over.w f)
    exact hw.trans (Category.comp_id _).symm

variable (κ : Cardinal.{u})

/-! ### The structure presheaf of the small model at linear coefficients -/

/-- **The tautological presheaf `𝒪` on the small model of `C_{B/A}`, with values in
`A`-modules**, sending an object `(P, α)` to the `A`-module underlying the polynomial algebra
`P`. -/
def smallPolynomialStructureModulePresheaf :
    (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} A :=
  smallSiteToOver A B κ ⋙ overModuleFunctor A B

/-- **The map of presheaves of `A`-modules `𝒪 ⟶ B̲` on the small model of `C_{B/A}`**, given by
the augmentations `α : P → B`. -/
def smallPolynomialModuleAugmentation :
    smallPolynomialStructureModulePresheaf A B κ ⟶
      (Functor.const (smallBoundedPolynomialSite A B κ)ᵒᵖ).obj (ModuleCat.of A (B : Type u)) :=
  Functor.whiskerLeft (smallSiteToOver A B κ) (overModuleAugmentation A B)

/-- **The sections of `𝒪` are free `A`-modules.** -/
theorem module_free_smallPolynomialStructureModulePresheaf_obj
    (X : (smallBoundedPolynomialSite A B κ)ᵒᵖ) :
    Module.Free A ((smallPolynomialStructureModulePresheaf A B κ).obj X) := by
  obtain ⟨ι, -, ⟨e⟩⟩ := (boundedPolynomialModel A B κ X.unop.unop).property
  exact Module.Free.of_equiv e.toLinearEquiv

/-- **The underlying map of abelian presheaves of the augmentation `𝒪 ⟶ B̲` of presheaves of
`A`-modules is the abelian augmentation** `CommAlgCat.smallPolynomialAugmentationAbelian`. -/
theorem whiskerRight_smallPolynomialModuleAugmentation :
    Functor.whiskerRight (smallPolynomialModuleAugmentation A B κ)
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) =
      smallPolynomialAugmentationAbelian A B κ :=
  rfl

/-! ### The Moore complex of `𝒪(U_•)` -/

/-- **The Moore complex of the evaluation of `𝒪` on the standard point resolution**, a chain
complex of `A`-modules: the complex whose term in degree `n` is the polynomial algebra
`𝒪(U_n)` and whose differentials are the alternating sums of the cofaces. -/
abbrev smallPolynomialStructureModuleMooreComplex : ChainComplex (ModuleCat.{u} A) ℕ :=
  (Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex
      (standardResolutionSmallCosimplicialObject A B)).obj
    (smallPolynomialStructureModulePresheaf A B (standardResolutionVarCardinal A B))

/-- **Every term of the Moore complex of `𝒪(U_•)` is a free `A`-module.** -/
theorem module_free_smallPolynomialStructureModuleMooreComplex_X (n : ℕ) :
    Module.Free A ((smallPolynomialStructureModuleMooreComplex A B).X n) :=
  module_free_smallPolynomialStructureModulePresheaf_obj A B (standardResolutionVarCardinal A B)
    (Opposite.op ((standardResolutionSmallCosimplicialObject A B).obj (SimplexCategory.mk n)))

/-- **The augmentation induces a quasi-isomorphism from the Moore complex of `𝒪(U_•)` to the
Moore complex of the constant diagram `B̲`.** -/
theorem quasiIso_smallPolynomialStructureModuleMooreComplex_augmentation :
    QuasiIso ((Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex
        (standardResolutionSmallCosimplicialObject A B)).map
      (smallPolynomialModuleAugmentation A B (standardResolutionVarCardinal A B))) := by
  have hqab : QuasiIso ((((SimplicialObject.whiskering (ModuleCat.{u} A)
          AddCommGrpCat.{u}).obj (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) ⋙
        alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerLeft (standardResolutionSmallCosimplicialObject A B).op
        (smallPolynomialModuleAugmentation A B (standardResolutionVarCardinal A B)))) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (Stacks.ChaoticSite.isIso_leftDerivedColimit_map_iff _
      (isPointResolution_standardResolutionSmallCosimplicialObject A B)
      (smallPolynomialAugmentationAbelian A B (standardResolutionVarCardinal A B)) n).1
      (isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian A B n)
  have hsq := (alternatingFaceMapComplexCompMapHomologicalComplexIso
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).hom.naturality
    (Functor.whiskerLeft (standardResolutionSmallCosimplicialObject A B).op
      (smallPolynomialModuleAugmentation A B (standardResolutionVarCardinal A B)))
  refine (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).1 ?_
  have key : ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        ((Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex
            (standardResolutionSmallCosimplicialObject A B)).map
          (smallPolynomialModuleAugmentation A B (standardResolutionVarCardinal A B))) =
      (alternatingFaceMapComplexCompMapHomologicalComplexIso
          (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).hom.app _ ≫
        (((SimplicialObject.whiskering (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
              (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) ⋙
            alternatingFaceMapComplex AddCommGrpCat.{u}).map
          (Functor.whiskerLeft (standardResolutionSmallCosimplicialObject A B).op
            (smallPolynomialModuleAugmentation A B (standardResolutionVarCardinal A B))) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso
          (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).inv.app _ := by
    rw [← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    exact rfl
  rw [key]
  infer_instance

/-- **The augmentation is invertible on the homology of the Moore complexes, in every degree.** -/
instance isIso_homologyMap_smallPolynomialModuleAugmentation (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex
          (standardResolutionSmallCosimplicialObject A B)).map
        (smallPolynomialModuleAugmentation A B (standardResolutionVarCardinal A B))) n) := by
  have hq := quasiIso_smallPolynomialStructureModuleMooreComplex_augmentation A B
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

/-- **The homology of the Moore complex of `𝒪(U_•)` vanishes in positive degrees.** -/
theorem isZero_homology_smallPolynomialStructureModuleMooreComplex_succ (n : ℕ) :
    IsZero ((smallPolynomialStructureModuleMooreComplex A B).homology (n + 1)) := by
  refine IsZero.of_iso ?_ (asIso (HomologicalComplex.homologyMap
      ((Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex
          (standardResolutionSmallCosimplicialObject A B)).map
        (smallPolynomialModuleAugmentation A B (standardResolutionVarCardinal A B)))
      (n + 1)) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.down ℕ) (n + 1)).mapIso
      (Stacks.ChaoticSite.mooreComplexConstIso (standardResolutionSmallCosimplicialObject A B)
        (ModuleCat.of A (B : Type u))))
  exact (ChainComplex.alternatingConst_exactAt (ModuleCat.of A (B : Type u)) (n + 1)
    (Nat.succ_ne_zero n)).isZero_homology

/-- **The degree-zero homology of the Moore complex of `𝒪(U_•)` is `B`**, through the map
induced by the augmentation (`CommAlgCat.smallPolynomialStructureModuleMooreHomologyZeroIso_hom`).
-/
def smallPolynomialStructureModuleMooreHomologyZeroIso :
    (smallPolynomialStructureModuleMooreComplex A B).homology 0 ≅ ModuleCat.of A (B : Type u) :=
  asIso (HomologicalComplex.homologyMap
      ((Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex
          (standardResolutionSmallCosimplicialObject A B)).map
        (smallPolynomialModuleAugmentation A B (standardResolutionVarCardinal A B))) 0) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.down ℕ) 0).mapIso
      (Stacks.ChaoticSite.mooreComplexConstIso (standardResolutionSmallCosimplicialObject A B)
        (ModuleCat.of A (B : Type u))) ≪≫
    ChainComplex.alternatingConstHomologyZero (ModuleCat.of A (B : Type u))

/-- **The map `H_0 ⟶ B` induced by the augmentation**: the map induced on `H_0` by the
augmentation `𝒪 ⟶ B̲`, followed by the identification of the degree-zero homology of the Moore
complex of the constant diagram `B̲` with `B`. -/
def smallPolynomialStructureModuleMooreAugmentationHomologyZero :
    (smallPolynomialStructureModuleMooreComplex A B).homology 0 ⟶ ModuleCat.of A (B : Type u) :=
  HomologicalComplex.homologyMap
      ((Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex
          (standardResolutionSmallCosimplicialObject A B)).map
        (smallPolynomialModuleAugmentation A B (standardResolutionVarCardinal A B))) 0 ≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.down ℕ) 0).map
      (Stacks.ChaoticSite.mooreComplexConstIso (standardResolutionSmallCosimplicialObject A B)
        (ModuleCat.of A (B : Type u))).hom ≫
    (ChainComplex.alternatingConstHomologyZero (ModuleCat.of A (B : Type u))).hom

/-- **The isomorphism `H_0 ≅ B` is the one induced by the augmentation.** -/
@[simp]
lemma smallPolynomialStructureModuleMooreHomologyZeroIso_hom :
    (smallPolynomialStructureModuleMooreHomologyZeroIso A B).hom =
      smallPolynomialStructureModuleMooreAugmentationHomologyZero A B :=
  rfl

/-- **The augmentation identifies `H_0` of the Moore complex of `𝒪(U_•)` with `B`.** -/
instance isIso_smallPolynomialStructureModuleMooreAugmentationHomologyZero :
    IsIso (smallPolynomialStructureModuleMooreAugmentationHomologyZero A B) :=
  (smallPolynomialStructureModuleMooreHomologyZeroIso A B).isIso_hom

end CommAlgCat

end
