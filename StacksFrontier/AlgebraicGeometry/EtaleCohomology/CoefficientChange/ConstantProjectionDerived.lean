module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ConstantProjectionDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ConstantProjectionMap
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LinearCupProductFamilyNaturality
public import StacksFrontier.Homology.KFlat.BifunctorOneSided
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ExtendScalarsAction

/-!
# The derived projection formula against constant coefficients

Let `g : X ⟶ Y` be a morphism of schemes and `Λ` a commutative ring.  This file constructs the
projection-formula map `Rg_*E ⊗^L_Λ M̲ ⟶ Rg_*(E ⊗^L_Λ M̲)` for `E ∈ D(X_étale, Λ)` and
`M ∈ D(Λ)`, natural in both variables, out of the sheaf-level projection map
`Stacks.EtaleCohomology.etaleModuleConstantProjectionMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CochainComplex.KFlatBifunctor

attribute [local instance] HasDerivedCategory.standard
universe u r

namespace Stacks.EtaleCohomology

/- The instance proofs `F.Additive`, `(F.obj X).Additive` and `HasMapBifunctor` for the tensor
product over `Λ` are the named ones of `ModuleTensor.TensorBifunctorInstances`, stated as
`etaleModuleDerivedTensor` records them, so that every `derivedBifunctor (etaleModuleTensor Λ X)`
written here is the unfolding of `etaleModuleDerivedTensor Λ X` up to proofs of the same
propositions; with independently synthesized proofs the kernel compares the two by evaluating the
derived bifunctor, which is prohibitively slow. -/
attribute [local instance high] etaleModuleTensor_additive etaleModuleTensor_obj_additive
  etaleModuleTensor_hasTotal_mapBifunctor

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The bifunctor `(F, M) ↦ F ⊗_Λ M̲` of an étale sheaf of `Λ`-modules and a `Λ`-module. -/
abbrev etaleModuleConstantTensor (Z : Scheme.{u}) :
    EtaleModules.{u, r} Λ Z ⥤ ModuleCat.{max (u + 1) r} Λ ⥤ EtaleModules.{u, r} Λ Z :=
  etaleModuleTensor.{u, r} Λ Z ⋙
    (Functor.whiskeringLeft _ _ _).obj (etaleModuleConstantSheafFunctor.{u, r} Λ Z)

/-- The bifunctor `etaleModuleConstantTensor` preserves zero morphisms in its first variable. -/
instance (Z : Scheme.{u}) : (etaleModuleConstantTensor.{u, r} Λ Z).PreservesZeroMorphisms :=
  inferInstanceAs (etaleModuleTensor.{u, r} Λ Z ⋙ _).PreservesZeroMorphisms

/-- For a fixed sheaf `F`, the functor `M ↦ F ⊗_Λ M̲` preserves zero morphisms. -/
instance (Z : Scheme.{u}) (F : EtaleModules.{u, r} Λ Z) :
    ((etaleModuleConstantTensor.{u, r} Λ Z).obj F).PreservesZeroMorphisms :=
  inferInstanceAs (etaleModuleConstantSheafFunctor.{u, r} Λ Z ⋙ _).PreservesZeroMorphisms

/-- **The projection map on total complexes**,
`Tot(g_*K ⊗ c_Y N) ⟶ g_* Tot(K ⊗ c_X N)`, for a complex `K` of étale sheaves of `Λ`-modules on
`X` and a complex `N` of `Λ`-modules: the sheaf-level projection map in each bidegree. -/
def etaleModuleTotalProjectionMap (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) :
    totalComplex (etaleModuleTensor.{u, r} Λ Y)
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).obj K)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ Y).mapHomologicalComplex _).obj N) ⟶
      ((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).obj
        (totalComplex (etaleModuleTensor.{u, r} Λ X) K
          (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex _).obj N)) :=
  Stacks.Cohomology.LinearCupProductFamily.mapBifunctorTotalMap
    (etaleModuleConstantTensor.{u, r} Λ X) (etaleModuleConstantTensor.{u, r} Λ Y)
    (etaleModuleDirectImage.{u, r} Λ g) (𝟭 _) (etaleModuleDirectImage.{u, r} Λ g)
    (fun F M => etaleModuleConstantProjectionMapApp Λ g F M)
    (fun f M => etaleModuleConstantProjectionMapApp_naturality_left Λ g f M)
    (fun F _ _ φ => etaleModuleConstantProjectionMapApp_naturality_right Λ g F φ)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) K N

/-- Naturality of the projection map on total complexes in both complexes. -/
@[reassoc]
theorem etaleModuleTotalProjectionMap_naturality {K K' : CochainComplex (EtaleModules.{u, r} Λ X) ℤ}
    {N N' : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ} (f : K ⟶ K') (φ : N ⟶ N') :
    HomologicalComplex.mapBifunctorMap
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).map f)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ Y).mapHomologicalComplex _).map φ)
        (etaleModuleTensor.{u, r} Λ Y) (ComplexShape.up ℤ) ≫
      etaleModuleTotalProjectionMap Λ g K' N' =
    etaleModuleTotalProjectionMap Λ g K N ≫
      ((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).map
        (HomologicalComplex.mapBifunctorMap f
          (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex _).map φ)
          (etaleModuleTensor.{u, r} Λ X) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.LinearCupProductFamily.mapBifunctorTotalMap_naturality
    (etaleModuleConstantTensor.{u, r} Λ X) (etaleModuleConstantTensor.{u, r} Λ Y)
    (etaleModuleDirectImage.{u, r} Λ g) (𝟭 _) (etaleModuleDirectImage.{u, r} Λ g)
    (fun F M => etaleModuleConstantProjectionMapApp Λ g F M)
    (fun f M => etaleModuleConstantProjectionMapApp_naturality_left Λ g f M)
    (fun F _ _ φ => etaleModuleConstantProjectionMapApp_naturality_right Λ g F φ)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) f φ

/-- Naturality of the projection map on total complexes in the sheaf complex. -/
@[reassoc]
theorem etaleModuleTotalProjectionMap_naturality_left
    {K K' : CochainComplex (EtaleModules.{u, r} Λ X) ℤ} (f : K ⟶ K')
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) :
    (((etaleModuleTensor.{u, r} Λ Y).map₂HomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).map f)).app
          (((etaleModuleConstantSheafFunctor.{u, r} Λ Y).mapHomologicalComplex _).obj N) ≫
      etaleModuleTotalProjectionMap Λ g K' N =
    etaleModuleTotalProjectionMap Λ g K N ≫
      ((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).map
        ((((etaleModuleTensor.{u, r} Λ X).map₂HomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).app
          (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex _).obj N)) := by
  have h := etaleModuleTotalProjectionMap_naturality Λ g f (𝟙 N)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
  exact h

/-- Naturality of the projection map on total complexes in the complex of modules. -/
@[reassoc]
theorem etaleModuleTotalProjectionMap_naturality_right
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    {N N' : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ} (φ : N ⟶ N') :
    (((etaleModuleTensor.{u, r} Λ Y).map₂HomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).obj K)).map
          (((etaleModuleConstantSheafFunctor.{u, r} Λ Y).mapHomologicalComplex _).map φ) ≫
      etaleModuleTotalProjectionMap Λ g K N' =
    etaleModuleTotalProjectionMap Λ g K N ≫
      ((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).map
        ((((etaleModuleTensor.{u, r} Λ X).map₂HomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map
          (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex _).map φ)) := by
  have h := etaleModuleTotalProjectionMap_naturality Λ g (𝟙 K) φ
  rw [CategoryTheory.Functor.map_id] at h
  exact h



/-! ### The factors of the projection map, with their types pinned

Each factor of `etaleModuleProjectionMapAux` is given its own name, with its source and target
spelled in one way (through `etaleModuleDerivedTensor`, `etaleModuleDerivedConstantSheaf`,
`totalComplex`, and composites of functors applied one at a time).  The statements below are
written in terms of them, so that the morphisms the kernel compares are syntactically equal:
comparing two spellings of one object of a derived category makes the kernel evaluate the
derived functors involved. -/

/-- The component at `N` of `Functor.mapDerivedCategoryFactors` for the constant sheaf functor,
`c_Z(Q N) ⟶ Q(c_Z N)`. -/
def etaleModuleConstantSheafQHom (Z : Scheme.{u})
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) :
    (etaleModuleDerivedConstantSheaf.{u, r} Λ Z).obj (DerivedCategory.Q.obj N) ⟶
        DerivedCategory.Q.obj (((etaleModuleConstantSheafFunctor.{u, r} Λ Z).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N) :=
  (etaleModuleConstantSheafFunctor.{u, r} Λ Z).mapDerivedCategoryFactors.hom.app N

/-- The inverse of `etaleModuleConstantSheafQHom`, `Q(c_Z N) ⟶ c_Z(Q N)`. -/
def etaleModuleConstantSheafQInv (Z : Scheme.{u})
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) :
    DerivedCategory.Q.obj (((etaleModuleConstantSheafFunctor.{u, r} Λ Z).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N) ⟶ (etaleModuleDerivedConstantSheaf.{u, r} Λ Z).obj
        (DerivedCategory.Q.obj N) :=
  (etaleModuleConstantSheafFunctor.{u, r} Λ Z).mapDerivedCategoryFactors.inv.app N

/-- `etaleModuleConstantSheafQHom` is an isomorphism. -/
instance (Z : Scheme.{u}) (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) :
    IsIso (etaleModuleConstantSheafQHom Λ Z N) :=
  inferInstanceAs
    (IsIso ((etaleModuleConstantSheafFunctor.{u, r} Λ Z).mapDerivedCategoryFactors.hom.app N))

/-- `etaleModuleConstantSheafQInv` is an isomorphism. -/
instance (Z : Scheme.{u}) (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) :
    IsIso (etaleModuleConstantSheafQInv Λ Z N) :=
  inferInstanceAs
    (IsIso ((etaleModuleConstantSheafFunctor.{u, r} Λ Z).mapDerivedCategoryFactors.inv.app N))

/-- The component at `Z` of the unit `g_* ⟶ Rg_*`, `Q(g_* Z) ⟶ Rg_*(Q Z)`. -/
def etaleModuleDirectImageUnboundedUnitApp (Z : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    DerivedCategory.Q.obj (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z) ⟶ (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).obj
        (DerivedCategory.Q.obj Z) :=
  (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).app Z

/-- The inverse of `etaleModuleComparisonRight`, `Q Tot(K ⊗ L) ⟶ K ⊗^L L`. -/
def etaleModuleComparisonRightInv (Z : Scheme.{u})
    (K L : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ)
    (hL : KFlat (etaleModuleTensor.{u, r} Λ Z) L) :
    DerivedCategory.Q.obj (totalComplex (etaleModuleTensor.{u, r} Λ Z) K L) ⟶
        ((etaleModuleDerivedTensor.{u, r} Λ Z).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj L) :=
  (comparisonRight (etaleModuleTensor.{u, r} Λ Z) K L hL).inv

/-- `etaleModuleComparisonRight` is an isomorphism. -/
instance isIso_etaleModuleComparisonRight (Z : Scheme.{u})
    (K L : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ)
    (hL : KFlat (etaleModuleTensor.{u, r} Λ Z) L) :
    IsIso (etaleModuleComparisonRight (Λ₁ := Λ) Z K L hL) :=
  inferInstanceAs (IsIso (comparisonRight (etaleModuleTensor.{u, r} Λ Z) K L hL).hom)

/-- `etaleModuleComparisonRightInv` is an isomorphism. -/
instance (Z : Scheme.{u}) (K L : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ)
    (hL : KFlat (etaleModuleTensor.{u, r} Λ Z) L) : IsIso (etaleModuleComparisonRightInv Λ Z K L
        hL) :=
  inferInstanceAs (IsIso (comparisonRight (etaleModuleTensor.{u, r} Λ Z) K L hL).inv)

/-- The total complex of an identity and a chain map, `Tot(K ⊗ L) ⟶ Tot(K ⊗ L')`. -/
def etaleModuleTotalComplexMapRight (Z : Scheme.{u})
    (K : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ)
    {L L' : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ} (φ : L ⟶ L') :
    (totalComplex (etaleModuleTensor.{u, r} Λ Z) K L) ⟶ (totalComplex (etaleModuleTensor.{u, r} Λ
        Z) K L') :=
  (((etaleModuleTensor.{u, r} Λ Z).map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map φ

/-- The total complex of a chain map and an identity, `Tot(K ⊗ L) ⟶ Tot(K' ⊗ L)`. -/
def etaleModuleTotalComplexMapLeft (Z : Scheme.{u})
    {K K' : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ}
    (f : K ⟶ K') (L : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ) :
    (totalComplex (etaleModuleTensor.{u, r} Λ Z) K L) ⟶ (totalComplex (etaleModuleTensor.{u, r} Λ
        Z) K' L) :=
  (((etaleModuleTensor.{u, r} Λ Z).map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).app L

/-- Naturality of `etaleModuleConstantSheafQHom`. -/
@[reassoc]
theorem etaleModuleConstantSheafQHom_naturality (Z : Scheme.{u})
    {N N' : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ} (φ : N ⟶ N') :
    (etaleModuleDerivedConstantSheaf.{u, r} Λ Z).map (DerivedCategory.Q.map φ) ≫
        etaleModuleConstantSheafQHom Λ Z N' =
      etaleModuleConstantSheafQHom Λ Z N ≫ DerivedCategory.Q.map
        (((etaleModuleConstantSheafFunctor.{u, r} Λ Z).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) :=
  (etaleModuleConstantSheafFunctor.{u, r} Λ Z).mapDerivedCategoryFactors.hom.naturality φ

/-- Naturality of `etaleModuleConstantSheafQInv`. -/
@[reassoc]
theorem etaleModuleConstantSheafQInv_naturality (Z : Scheme.{u})
    {N N' : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ} (φ : N ⟶ N') :
    DerivedCategory.Q.map (((etaleModuleConstantSheafFunctor.{u, r} Λ Z).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) ≫ etaleModuleConstantSheafQInv Λ Z N' =
      etaleModuleConstantSheafQInv Λ Z N ≫ (etaleModuleDerivedConstantSheaf.{u, r} Λ Z).map
          (DerivedCategory.Q.map φ) :=
  (etaleModuleConstantSheafFunctor.{u, r} Λ Z).mapDerivedCategoryFactors.inv.naturality φ

/-- Naturality of `etaleModuleDirectImageUnboundedUnitApp`. -/
@[reassoc]
theorem etaleModuleDirectImageUnboundedUnitApp_naturality
    {Z Z' : CochainComplex (EtaleModules.{u, r} Λ X) ℤ} (φ : Z ⟶ Z') :
    DerivedCategory.Q.map (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) ≫ etaleModuleDirectImageUnboundedUnitApp Λ g Z' =
        etaleModuleDirectImageUnboundedUnitApp Λ g Z ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map (DerivedCategory.Q.map φ) :=
  (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).naturality φ

/-- Naturality of `etaleModuleComparisonRight` in the K-flat right complex. -/
@[reassoc]
theorem etaleModuleComparisonRight_naturality_right (Z : Scheme.{u})
    (K : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ)
    {L L' : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ}
    (φ : L ⟶ L') (hL : KFlat (etaleModuleTensor.{u, r} Λ Z) L)
    (hL' : KFlat (etaleModuleTensor.{u, r} Λ Z) L') :
    ((etaleModuleDerivedTensor.{u, r} Λ Z).obj (DerivedCategory.Q.obj K)).map
        (DerivedCategory.Q.map φ) ≫ etaleModuleComparisonRight (Λ₁ := Λ) Z K L' hL' =
      etaleModuleComparisonRight (Λ₁ := Λ) Z K L hL ≫ DerivedCategory.Q.map
          (etaleModuleTotalComplexMapRight Λ Z K φ) :=
  comparisonRight_naturality_right _ K φ hL hL'

/-- Naturality of `etaleModuleComparisonRightInv` in the K-flat right complex. -/
@[reassoc]
theorem etaleModuleComparisonRightInv_naturality_right (Z : Scheme.{u})
    (K : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ)
    {L L' : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ}
    (φ : L ⟶ L') (hL : KFlat (etaleModuleTensor.{u, r} Λ Z) L)
    (hL' : KFlat (etaleModuleTensor.{u, r} Λ Z) L') :
    DerivedCategory.Q.map (etaleModuleTotalComplexMapRight Λ Z K φ) ≫ etaleModuleComparisonRightInv
        Λ Z K L' hL' =
      etaleModuleComparisonRightInv Λ Z K L hL ≫ ((etaleModuleDerivedTensor.{u, r} Λ Z).obj
          (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map φ) := by
  unfold etaleModuleComparisonRightInv etaleModuleTotalComplexMapRight
  rw [Iso.comp_inv_eq, Category.assoc, comparisonRight_naturality_right _ _ _ hL hL',
    Iso.inv_hom_id_assoc]

/-- Naturality of `etaleModuleComparisonRight` in the left complex, through
`etaleModuleTotalComplexMapLeft`. -/
@[reassoc]
theorem etaleModuleComparisonRight_naturality_left_totalComplexMap (Z : Scheme.{u})
    {K K' : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ} (f : K ⟶ K')
    (L : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ)
    (hL : KFlat (etaleModuleTensor.{u, r} Λ Z) L) :
    ((etaleModuleDerivedTensor.{u, r} Λ Z).map (DerivedCategory.Q.map f)).app
        (DerivedCategory.Q.obj L) ≫ etaleModuleComparisonRight (Λ₁ := Λ) Z K' L hL =
      etaleModuleComparisonRight (Λ₁ := Λ) Z K L hL ≫ DerivedCategory.Q.map
          (etaleModuleTotalComplexMapLeft Λ Z f L) :=
  comparisonRight_naturality_left _ f L hL

/-- Naturality of `etaleModuleComparisonRightInv` in the left complex. -/
@[reassoc]
theorem etaleModuleComparisonRightInv_naturality_left (Z : Scheme.{u})
    {K K' : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ} (f : K ⟶ K')
    (L : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ)
    (hL : KFlat (etaleModuleTensor.{u, r} Λ Z) L) :
    DerivedCategory.Q.map (etaleModuleTotalComplexMapLeft Λ Z f L) ≫ etaleModuleComparisonRightInv
        Λ Z K' L hL =
      etaleModuleComparisonRightInv Λ Z K L hL ≫ ((etaleModuleDerivedTensor.{u, r} Λ Z).map
          (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) := by
  unfold etaleModuleComparisonRightInv etaleModuleTotalComplexMapLeft
  rw [Iso.comp_inv_eq, Category.assoc, comparisonRight_naturality_left _ f L hL,
    Iso.inv_hom_id_assoc]

/-- Naturality of the projection map on total complexes in the complex of modules, through
`etaleModuleTotalComplexMapRight`, after `Q`. -/
@[reassoc]
theorem etaleModuleTotalProjectionMap_totalComplexMapRight
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    {N N' : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ} (φ : N ⟶ N') :
    DerivedCategory.Q.map (etaleModuleTotalComplexMapRight Λ Y (((etaleModuleDirectImage.{u, r} Λ
        g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ)) ≫ DerivedCategory.Q.map
        (etaleModuleTotalProjectionMap Λ g K N') =
      DerivedCategory.Q.map (etaleModuleTotalProjectionMap Λ g K N) ≫ DerivedCategory.Q.map
          (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (etaleModuleTotalComplexMapRight Λ X K (((etaleModuleConstantSheafFunctor.{u, r} Λ
          X).mapHomologicalComplex (ComplexShape.up ℤ)).map φ))) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (etaleModuleTotalProjectionMap_naturality_right Λ g K φ)

/-- Naturality of the projection map on total complexes in the sheaf complex, through
`etaleModuleTotalComplexMapLeft`, after `Q`. -/
@[reassoc]
theorem etaleModuleTotalProjectionMap_totalComplexMapLeft
    {K K' : CochainComplex (EtaleModules.{u, r} Λ X) ℤ}
    (f : K ⟶ K') (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ) :
    DerivedCategory.Q.map (etaleModuleTotalComplexMapLeft Λ Y (((etaleModuleDirectImage.{u, r} Λ
        g).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)) ≫ DerivedCategory.Q.map
        (etaleModuleTotalProjectionMap Λ g K' N) =
      DerivedCategory.Q.map (etaleModuleTotalProjectionMap Λ g K N) ≫ DerivedCategory.Q.map
          (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (etaleModuleTotalComplexMapLeft Λ X f (((etaleModuleConstantSheafFunctor.{u, r} Λ
          X).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (etaleModuleTotalProjectionMap_naturality_left Λ g f N)

/-- **The projection map before deriving `g_*`**: for a complex `K` on `X` and a complex `N`
of `Λ`-modules whose constant sheaf complexes are K-flat,
`g_*K ⊗^L c_Y N ⟶ Rg_*(K ⊗^L c_X N)`: the comparison of `g_*K ⊗^L c_Y N` with the total complex,
the projection map on total complexes, the unit `g_* ⟶ Rg_*`, and the comparison of
`K ⊗^L c_X N` with the total complex. -/
def etaleModuleProjectionMapAux (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (N : (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory) :
    ((etaleModuleDerivedTensor.{u, r} Λ Y).obj (DerivedCategory.Q.obj
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).obj K))).obj
        ((etaleModuleDerivedConstantSheaf.{u, r} Λ Y).obj (DerivedCategory.Q.obj N.obj)) ⟶
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).obj
        (((etaleModuleDerivedTensor.{u, r} Λ X).obj (DerivedCategory.Q.obj K)).obj
          ((etaleModuleDerivedConstantSheaf.{u, r} Λ X).obj (DerivedCategory.Q.obj N.obj))) :=
  ((etaleModuleDerivedTensor.{u, r} Λ Y).obj (DerivedCategory.Q.obj
      (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).map
      (etaleModuleConstantSheafQHom Λ Y N.obj) ≫
    etaleModuleComparisonRight (Λ₁ := Λ) Y (((etaleModuleDirectImage.{u, r} Λ
        g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N.obj) (N.property Y).1 ≫
    DerivedCategory.Q.map (etaleModuleTotalProjectionMap Λ g K N.obj) ≫
    etaleModuleDirectImageUnboundedUnitApp Λ g (totalComplex (etaleModuleTensor.{u, r} Λ X) K
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N.obj)) ≫
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map (etaleModuleComparisonRightInv Λ X K
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N.obj) (N.property X).1 ≫
      ((etaleModuleDerivedTensor.{u, r} Λ X).obj (DerivedCategory.Q.obj K)).map
          (etaleModuleConstantSheafQInv Λ X N.obj))

section NaturalityRight

variable (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
  {N N' : (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory} (f : N ⟶ N')

private theorem projAux_tail_naturality_right :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map (DerivedCategory.Q.map
        (etaleModuleTotalComplexMapRight Λ X K (((etaleModuleConstantSheafFunctor.{u, r} Λ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom))) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map (etaleModuleComparisonRightInv Λ X K
          (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N'.obj) (N'.property X).1 ≫
        ((etaleModuleDerivedTensor.{u, r} Λ X).obj (DerivedCategory.Q.obj K)).map
            (etaleModuleConstantSheafQInv Λ X N'.obj)) =
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map (etaleModuleComparisonRightInv Λ X K
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N.obj) (N.property X).1 ≫
        ((etaleModuleDerivedTensor.{u, r} Λ X).obj (DerivedCategory.Q.obj K)).map
            (etaleModuleConstantSheafQInv Λ X N.obj)) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map (((etaleModuleDerivedTensor.{u, r} Λ
          X).obj (DerivedCategory.Q.obj K)).map ((etaleModuleDerivedConstantSheaf.{u, r} Λ X).map
          (DerivedCategory.Q.map f.hom))) := by
  rw [← Functor.map_comp (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g), ← Functor.map_comp
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g),
    reassoc_of% (etaleModuleComparisonRightInv_naturality_right Λ X K
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f.hom)
      (N.property X).1 (N'.property X).1),
    ← Functor.map_comp ((etaleModuleDerivedTensor.{u, r} Λ X).obj (DerivedCategory.Q.obj K)),
        etaleModuleConstantSheafQInv_naturality Λ X f.hom,
    Functor.map_comp ((etaleModuleDerivedTensor.{u, r} Λ X).obj (DerivedCategory.Q.obj K)),
        Category.assoc]

end NaturalityRight

/-- **Naturality of `etaleModuleProjectionMapAux` in the complex of modules**, along a chain
map. -/
@[reassoc]
theorem etaleModuleProjectionMapAux_naturality_right
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    {N N' : (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory} (f : N ⟶ N') :
    ((etaleModuleDerivedTensor.{u, r} Λ Y).obj (DerivedCategory.Q.obj
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).obj K))).map
        ((etaleModuleDerivedConstantSheaf.{u, r} Λ Y).map (DerivedCategory.Q.map f.hom)) ≫
      etaleModuleProjectionMapAux Λ g K N' =
    etaleModuleProjectionMapAux Λ g K N ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map
        (((etaleModuleDerivedTensor.{u, r} Λ X).obj (DerivedCategory.Q.obj K)).map
          ((etaleModuleDerivedConstantSheaf.{u, r} Λ X).map (DerivedCategory.Q.map f.hom))) := by
  rw [etaleModuleProjectionMapAux, etaleModuleProjectionMapAux,
    ← Functor.map_comp_assoc ((etaleModuleDerivedTensor.{u, r} Λ Y).obj (DerivedCategory.Q.obj
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))),
    etaleModuleConstantSheafQHom_naturality Λ Y f.hom,
    Functor.map_comp_assoc ((etaleModuleDerivedTensor.{u, r} Λ Y).obj (DerivedCategory.Q.obj
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))),
    reassoc_of% (etaleModuleComparisonRight_naturality_right Λ Y (((etaleModuleDirectImage.{u, r} Λ
        g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f.hom)
      (N.property Y).1 (N'.property Y).1),
    reassoc_of% (etaleModuleTotalProjectionMap_totalComplexMapRight Λ g K f.hom),
    reassoc_of% (etaleModuleDirectImageUnboundedUnitApp_naturality Λ g
        (etaleModuleTotalComplexMapRight Λ X K (((etaleModuleConstantSheafFunctor.{u, r} Λ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom))),
    projAux_tail_naturality_right Λ g K f]
  simp only [Category.assoc]

section NaturalityLeft

variable {K K' : CochainComplex (EtaleModules.{u, r} Λ X) ℤ} (f : K ⟶ K')
  (N : (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory)

private theorem projAux_tail_naturality_left :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map (DerivedCategory.Q.map
        (etaleModuleTotalComplexMapLeft Λ X f (((etaleModuleConstantSheafFunctor.{u, r} Λ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.obj))) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map (etaleModuleComparisonRightInv Λ X K'
          (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N.obj) (N.property X).1 ≫
        ((etaleModuleDerivedTensor.{u, r} Λ X).obj (DerivedCategory.Q.obj K')).map
            (etaleModuleConstantSheafQInv Λ X N.obj)) =
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map (etaleModuleComparisonRightInv Λ X K
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N.obj) (N.property X).1 ≫
        ((etaleModuleDerivedTensor.{u, r} Λ X).obj (DerivedCategory.Q.obj K)).map
            (etaleModuleConstantSheafQInv Λ X N.obj)) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map (((etaleModuleDerivedTensor.{u, r} Λ
          X).map (DerivedCategory.Q.map f)).app ((etaleModuleDerivedConstantSheaf.{u, r} Λ X).obj
          (DerivedCategory.Q.obj N.obj))) := by
  rw [← Functor.map_comp (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g), ← Functor.map_comp
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g),
    reassoc_of% (etaleModuleComparisonRightInv_naturality_left Λ X f
        (((etaleModuleConstantSheafFunctor.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N.obj) (N.property X).1),
    ← ((etaleModuleDerivedTensor.{u, r} Λ X).map (DerivedCategory.Q.map f)).naturality
        (etaleModuleConstantSheafQInv Λ X N.obj), Category.assoc]

end NaturalityLeft

/-- **Naturality of `etaleModuleProjectionMapAux` in the sheaf complex.** -/
@[reassoc]
theorem etaleModuleProjectionMapAux_naturality_left
    {K K' : CochainComplex (EtaleModules.{u, r} Λ X) ℤ} (f : K ⟶ K')
    (N : (constantSheafKFlatComplexes.{u, r} Λ).FullSubcategory) :
    ((etaleModuleDerivedTensor.{u, r} Λ Y).map (DerivedCategory.Q.map
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex _).map f))).app
        ((etaleModuleDerivedConstantSheaf.{u, r} Λ Y).obj (DerivedCategory.Q.obj N.obj)) ≫
      etaleModuleProjectionMapAux Λ g K' N =
    etaleModuleProjectionMapAux Λ g K N ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map
        (((etaleModuleDerivedTensor.{u, r} Λ X).map (DerivedCategory.Q.map f)).app
          ((etaleModuleDerivedConstantSheaf.{u, r} Λ X).obj (DerivedCategory.Q.obj N.obj))) := by
  rw [etaleModuleProjectionMapAux, etaleModuleProjectionMapAux,
    ← reassoc_of% (((etaleModuleDerivedTensor.{u, r} Λ Y).map (DerivedCategory.Q.map
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        f))).naturality (etaleModuleConstantSheafQHom Λ Y N.obj)),
    reassoc_of% (etaleModuleComparisonRight_naturality_left_totalComplexMap Λ Y
        (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N.obj)
      (N.property Y).1),
    reassoc_of% (etaleModuleTotalProjectionMap_totalComplexMapLeft Λ g f N.obj),
    reassoc_of% (etaleModuleDirectImageUnboundedUnitApp_naturality Λ g
        (etaleModuleTotalComplexMapLeft Λ X f (((etaleModuleConstantSheafFunctor.{u, r} Λ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.obj))),
    projAux_tail_naturality_left Λ g f N]
  simp only [Category.assoc]

end Stacks.EtaleCohomology

end
