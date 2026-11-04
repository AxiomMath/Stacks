module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.ModelUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyFactorsh
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopSingleProjection

/-!
# The cohomology of the model complex

The model complex of a square of rings computes the derived base change `M ⊗^L_R R'`: its
cohomology, as a module over `A ⊗_R R'`, is the cohomology of `M ⊗^L_R R'` with the module
structure of Stacks 0DJ7, and the model map induces on cohomology the comparison of Stacks 065Z
followed by the given map.

## Main results

* `RingTheory.TorIndependence.modelHomologyIso` and its naturality
* `RingTheory.TorIndependence.modelHomologyLinearEquiv`
* `RingTheory.TorIndependence.modelHomology_comparison`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open CochainComplex.DerivedExtensionScalars

universe u

namespace RingTheory.TorIndependence

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

attribute [local instance] Algebra.TensorProduct.rightAlgebra HasDerivedCategory.standard

local notation "B₀" => A ⊗[R] R₀

variable {F : CochainComplex (ModuleCat.{u} R₀) ℤ}
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))
  [Module.Flat R R₀] (hF : F.KFlat) [QuasiIso ε]

/-- The model complex is functorial in the complex of `A`-modules. -/
abbrev modelComplexMap {M M' : CochainComplex (ModuleCat.{u} A) ℤ} (f : M ⟶ M') :
    modelComplex (R := R) A F M ⟶ modelComplex A F M' :=
  HomologicalComplex.mapBifunctorMap f (𝟙 F) (modelBifunctor (R := R) (A := A) (R₀ := R₀))
    (ComplexShape.up ℤ)

omit [Module.Flat R R₀] in
/-- The base model functor sends `f` to the tensor product of the base change of `f` to `R₀`
with the identity of `F`. -/
theorem baseModelFunctor_map_eq {X X' : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ X') :
    (baseModelFunctor R F).map f =
      HomologicalComplex.mapBifunctorMap
        (((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).map f) (𝟙 F)
        (curriedTensor (ModuleCat.{u} R₀)) (ComplexShape.up ℤ) := rfl

omit [Module.Flat R R₀] in
/-- The identification `modelRestrictIso` of the restriction to `R₀` of the model complex with
the base model of the restriction to `R` is natural in the complex of `A`-modules. -/
theorem modelRestrictIso_naturality {M M' : CochainComplex (ModuleCat.{u} A) ℤ} (f : M ⟶ M') :
    ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (modelComplexMap (R := R) (R₀ := R₀) (F := F) f) ≫ (modelRestrictIso F M').hom =
      (modelRestrictIso F M).hom ≫ (baseModelFunctor R F).map
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) := by
  have h := Functor.mapBifunctorTotalIso_hom_naturality
    (modelBifunctor (R := R) (A := A) (R₀ := R₀))
    (curriedTensor (ModuleCat.{u} R₀))
    (ModuleCat.restrictScalars (algebraMap R A) ⋙ baseChangeFunctor R R₀) (𝟭 _)
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)) modelBifunctorIso
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c := ComplexShape.up ℤ)
    modelBifunctorIso_naturality_left modelBifunctorIso_naturality_right M M' F F f (𝟙 F)
  rw [baseModelFunctor_map_eq]
  exact h

/-- **The model computes the derived base change**, read in `D(R₀)`: the restriction to `R₀`
of the model complex of `M` is the derived base change of `M` from `R` to `R'`. -/
def modelXi (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (modelComplex A F M)) ≅
      (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.obj
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
            (DerivedCategory.Q.obj M))) :=
  (ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategoryFactors.app
      (modelComplex A F M) ≪≫
    DerivedCategory.Q.mapIso (modelRestrictIso F M) ≪≫
    (baseModelDerivedFac hF).symm.app
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) ≪≫
    (asIso ((baseModelLift (R := R) ε hF).app (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)))).symm ≪≫
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor ⋙
      (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory).mapIso
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.symm.app M)

/-- The identification `modelXi` is natural in the complex of `A`-modules. -/
theorem modelXi_naturality {M M' : CochainComplex (ModuleCat.{u} A) ℤ} (f : M ⟶ M') :
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategory.map
        (DerivedCategory.Q.map (modelComplexMap (R := R) (R₀ := R₀) (F := F) f)) ≫
      (modelXi ε hF M').hom =
    (modelXi ε hF M).hom ≫
      (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory.map
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.map
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
            (DerivedCategory.Q.map f))) := by
  dsimp only [modelXi, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv,
    Functor.comp_map]
  have h1 := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.inv.naturality f
  have h2 := (baseModelLift (R := R) ε hF).naturality
    (DerivedCategory.Q.map (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f))
  have h3 := (baseModelDerivedFac (R := R) hF).inv.naturality
    (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  have h4 := congrArg DerivedCategory.Q.map (modelRestrictIso_naturality (R := R) (A := A)
    (R₀ := R₀) (F := F) f)
  simp only [Functor.map_comp] at h4
  dsimp only [Functor.comp_map, Functor.comp_obj] at h1 h2 h3
  rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc, reassoc_of% h4, reassoc_of% h3]
  simp only [Category.assoc]
  congr 3
  have h5 : (baseModelDerived (R := R) hF).map (DerivedCategory.Q.map
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)) ≫
      inv ((baseModelLift (R := R) ε hF).app (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M'))) =
      inv ((baseModelLift (R := R) ε hF).app (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M))) ≫
      (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory.map
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.map
          (DerivedCategory.Q.map
            (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f))) := by
    rw [IsIso.eq_inv_comp, ← reassoc_of% h2, IsIso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% h5, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, h1]

variable (n : ℤ)

/-- The cohomology of the model complex, read over `R₀`, is the cohomology of the derived base
change. -/
def modelHomologyIso (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).obj
          (DerivedCategory.Q.obj (modelComplex A F M))) ≅
      (ModuleCat.restrictScalars (algebraMap R₀ R')).obj
        (baseChangeCohomologyOverBase (R := R) (R' := R') (DerivedCategory.Q.obj M) n) :=
  (((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategoryHomologyIso n).app
      (DerivedCategory.Q.obj (modelComplex A F M))).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R₀) n).mapIso (modelXi ε hF M) ≪≫
    ((ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategoryHomologyIso n).app _

/-- The isomorphism `modelHomologyIso` is natural in the complex of `A`-modules. -/
theorem modelHomologyIso_naturality {M M' : CochainComplex (ModuleCat.{u} A) ℤ} (f : M ⟶ M') :
    (ModuleCat.restrictScalars (algebraMap R₀ B₀)).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
          (DerivedCategory.Q.map (modelComplexMap (R := R) (R₀ := R₀) (F := F) f))) ≫
      (modelHomologyIso (R := R) ε hF n M').hom =
    (modelHomologyIso (R := R) ε hF n M).hom ≫
      (ModuleCat.restrictScalars (algebraMap R₀ R')).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.map
            ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
              (DerivedCategory.Q.map f)))) := by
  dsimp only [modelHomologyIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom]
  have h1 := ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategoryHomologyIso
    n).inv.naturality (DerivedCategory.Q.map (modelComplexMap (R := R) (R₀ := R₀) (F := F) f))
  have h2 := ((ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategoryHomologyIso
    n).hom.naturality ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.map
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
        (DerivedCategory.Q.map f)))
  have h3 := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} R₀) n).map
    (modelXi_naturality (R := R) (A := A) ε hF f)
  simp only [Functor.map_comp] at h3
  dsimp only [Functor.comp_map, Functor.comp_obj] at h1 h2
  rw [reassoc_of% h1, reassoc_of% h3, h2]
  simp only [Category.assoc]

omit [Module.Flat R R₀] in
/-- On `(B₀ ⊗_A X) ⊗_{B₀} (B₀ ⊗_{R₀} W)`, the base change of multiplication by `a` on `X`,
tensored with the identity, is multiplication by `a ⊗ 1`. -/
theorem rTensor_baseChange_smul_raw (X : Type u) [AddCommGroup X] [Module A X]
    (W : Type u) [AddCommGroup W] [Module R₀ W] (a : A)
    (t : (B₀ ⊗[A] X) ⊗[B₀] (B₀ ⊗[R₀] W)) :
    LinearMap.rTensor _ ((a • LinearMap.id : X →ₗ[A] X).baseChange B₀) t =
      (a ⊗ₜ[R] (1 : R₀)) • t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]
  | add t t' ht ht' => rw [map_add, ht, ht', smul_add]
  | tmul m w =>
    induction m using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, smul_zero]
    | add m m' hm hm' =>
      rw [TensorProduct.add_tmul, map_add, hm, hm', smul_add]
    | tmul c x =>
      rw [LinearMap.rTensor_tmul, LinearMap.baseChange_tmul, LinearMap.smul_apply,
        LinearMap.id_apply, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul]
      congr 2
      rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]

omit [Module.Flat R R₀] in
/-- The model bifunctor sends multiplication by `a` on an `A`-module to multiplication by
`a ⊗ 1`. -/
theorem modelBifunctor_map_smul (X : ModuleCat.{u} A) (W : ModuleCat.{u} R₀) (a : A) :
    ((modelBifunctor (R := R) (A := A) (R₀ := R₀)).map (a • 𝟙 X)).app W =
      ((a ⊗ₜ[R] (1 : R₀) : B₀)) • 𝟙 _ := by
  ext t
  exact rTensor_baseChange_smul_raw X W a t

omit [Module.Flat R R₀] in
/-- Multiplication by `a ⊗ 1` on the model complex is the model of multiplication by `a`. -/
theorem modelComplex_smul (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) :
    ((a ⊗ₜ[R] (1 : R₀) : B₀)) • 𝟙 (modelComplex A F M) =
      modelComplexMap (R := R) (R₀ := R₀) (F := F) (a • 𝟙 M) := by
  ext n : 1
  show (((a ⊗ₜ[R] (1 : R₀) : B₀)) • 𝟙 (HomologicalComplex.mapBifunctor M F
    (modelBifunctor (R := R) (A := A) (R₀ := R₀)) (ComplexShape.up ℤ))).f n = _
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.smul_f_apply,
    HomologicalComplex.id_f, Linear.comp_smul, Category.comp_id, HomologicalComplex.smul_f_apply,
    HomologicalComplex.id_f, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    Category.id_comp, modelBifunctor_map_smul, Linear.smul_comp, Category.id_comp]

variable (R A R' R₀) in
/-- The ring map `A ⊗_R R₀ ⟶ A ⊗_R R'`. -/
abbrev modelBaseRingMap : B₀ →+* A ⊗[R] R' :=
  (Algebra.TensorProduct.map (AlgHom.id R A) (IsScalarTower.toAlgHom R R₀ R')).toRingHom

omit [Module.Flat R R₀] in
/-- The ring map `A ⊗_R R₀ ⟶ A ⊗_R R'` sends `a ⊗ r` to `a ⊗ r`, with `r` mapped to `R'`. -/
theorem modelBaseRingMap_tmul (a : A) (r : R₀) :
    modelBaseRingMap R A R' R₀ (a ⊗ₜ[R] r) = a ⊗ₜ[R] algebraMap R₀ R' r := rfl

/-- **The cohomology of the model is the cohomology of the derived base change**, as modules over
`A ⊗_R R₀`. -/
def modelHomologyLinearEquiv (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).obj
        (DerivedCategory.Q.obj (modelComplex A F M)) ≃ₗ[B₀]
      (ModuleCat.restrictScalars (modelBaseRingMap R A R' R₀)).obj
        (baseChangeCohomologyCat (R := R) (R' := R') (DerivedCategory.Q.obj M) n) where
  toFun y := (modelHomologyIso (R := R) ε hF n M).hom.hom y
  invFun y := (modelHomologyIso (R := R) ε hF n M).inv.hom y
  map_add' y y' := (modelHomologyIso (R := R) ε hF n M).hom.hom.map_add y y'
  map_smul' b y := by
    let HB := (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).obj
      (DerivedCategory.Q.obj (modelComplex A F M))
    let E : HB → baseChangeCohomologyOverBase (R := R) (R' := R') (DerivedCategory.Q.obj M) n :=
      fun z => (modelHomologyIso (R := R) ε hF n M).hom.hom z
    let H := baseChangeCohomologyCat (R := R) (R' := R') (DerivedCategory.Q.obj M) n
    let := baseChangeCohomologyModule (R := R) (R' := R') (DerivedCategory.Q.obj M) n
    change E (b • y) = modelBaseRingMap R A R' R₀ b • (show H from E y)
    have hR : ∀ (r : R₀) (z : HB), E (((1 : A) ⊗ₜ[R] r) • z) =
          (Algebra.TensorProduct.includeRight (algebraMap R₀ R' r) : A ⊗[R] R') •
            (show H from E z) := by
      intro r z
      refine Eq.trans ?_ (baseChangeCohomologyModule_includeRight_smul (R := R) (R' := R')
        (DerivedCategory.Q.obj M) n (algebraMap R₀ R' r) (E z)).symm
      have : ((1 : A) ⊗ₜ[R] r) • z = algebraMap R₀ B₀ r • z := by
        rw [Algebra.TensorProduct.right_algebraMap_apply]
      exact (congrArg E this).trans ((modelHomologyIso (R := R) ε hF n M).hom.hom.map_smul r z)
    have hA : ∀ (a : A) (z : HB), E ((a ⊗ₜ[R] (1 : R₀)) • z) =
          (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') •
            (show H from E z) := by
      intro a z
      refine Eq.trans ?_ (baseChangeCohomologyModule_includeLeft_smul (R := R) (R' := R')
        (DerivedCategory.Q.obj M) n a (E z)).symm
      refine Eq.trans ?_ (baseChangeCohomologyAction_apply_eq (R := R) (R' := R')
        (DerivedCategory.Q.obj M) n a (E z)).symm
      let := DerivedCategory.homologyFunctor_linear (C := ModuleCat.{u} B₀) B₀ n
      have h1 : (a ⊗ₜ[R] (1 : R₀)) • z =
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
            (DerivedCategory.Q.map (modelComplexMap (R := R) (R₀ := R₀) (F := F)
              (a • 𝟙 M)))).hom z := by
        rw [← modelComplex_smul, Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_smul,
          CategoryTheory.Functor.map_id]
        rfl
      have h2 := congrArg (fun f => f.hom z)
        (modelHomologyIso_naturality (R := R) ε hF n (a • 𝟙 M))
      refine (congrArg E h1).trans (h2.trans ?_)
      change ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.map
            ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
              (DerivedCategory.Q.map (a • 𝟙 M))))).hom (E z) = _
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    have hE0 : E 0 = 0 := (modelHomologyIso (R := R) ε hF n M).hom.hom.map_zero
    have hEadd : ∀ z z' : HB, E (z + z') = E z + E z' :=
      (modelHomologyIso (R := R) ε hF n M).hom.hom.map_add
    induction b using TensorProduct.induction_on with
    | zero =>
      rw [zero_smul, hE0, map_zero]
      exact (zero_smul _ _).symm
    | add b b' hb hb' =>
      rw [add_smul, hEadd, hb, hb', map_add]
      exact (add_smul _ _ _).symm
    | tmul a r =>
      have ht : a ⊗ₜ[R] r = (a ⊗ₜ[R] (1 : R₀)) * ((1 : A) ⊗ₜ[R] r) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [ht, mul_smul, hA, hR, ← mul_smul, map_mul]
      congr 1
      rw [modelBaseRingMap_tmul, modelBaseRingMap_tmul, map_one]
      rfl
  left_inv y := congrArg (fun f => f.hom y) (modelHomologyIso (R := R) ε hF n M).hom_inv_id
  right_inv y := congrArg (fun f => f.hom y) (modelHomologyIso (R := R) ε hF n M).inv_hom_id

section Square

/-- Reassociation of a composite of four morphisms. -/
theorem comp_assoc_helper {C : Type*} [Category C] {a b c d e : C} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) (k : d ⟶ e) : (f ≫ g ≫ h) ≫ k = f ≫ g ≫ h ≫ k := by
  simp only [Category.assoc]

/-- The isomorphism `Functor.mapHomologicalComplexCompIso` attached to the identity of
`G₁ ⋙ G₂` is the identity at every complex. -/
theorem mapHomologicalComplexCompIso_refl_hom_app {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
    (G₁ : C₁ ⥤ C₂) (G₂ : C₂ ⥤ C₃) [G₁.Additive] [G₂.Additive]
    (M : CochainComplex C₁ ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (ComplexShape.up ℤ)).hom.app M =
      𝟙 _ := by
  ext n
  rfl

variable (R A R' A') in
/-- At a complex `M` of `A`-modules, the derived comparison of the square, followed by the
comparison for `A ⟶ A'`, is the comparison for `R ⟶ R'` followed by the termwise comparison
`R' ⊗_R M ⟶ A' ⊗_A M`, up to the identifications of restriction of scalars. -/
theorem squareDerivedComparison_app_Q (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app
        (DerivedCategory.Q.obj M) ≫
      (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).comparison.app M) ≫
      (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) =
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.map
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.hom.app M) ≫
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).comparison.app
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (squareTermComparison R A R' A')
        (ComplexShape.up ℤ)).app M) := by
  have h := NatTrans.congr_app
    (@derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
    R A R' A' _ _ _ _ _ _ _ _ (algebraMap R A) (algebraMap R R') (algebraMap A A')
    (algebraMap R' A') baseChangeSquare
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).comparison
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).comparison
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).isLeftDerived
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).isLeftDerived).2.2.2 M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    mapHomologicalComplexCompIso_refl_hom_app, CategoryTheory.Functor.map_id,
    Functor.comp_obj] at h
  simp only [Category.comp_id, Category.assoc] at h
  exact h

variable (R A R' A') in
/-- The derived comparison of the square at a complex `M`, followed by the comparison for
`A ⟶ A'`, is the comparison for `R ⟶ R'` followed by the termwise comparison
`R' ⊗_R M ⟶ A' ⊗_A M`, with the target identified through restriction of scalars. -/
theorem squareDerivedComparison_app_Q' (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app
        (DerivedCategory.Q.obj M) ≫
      (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).comparison.app M) =
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.map
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.hom.app M) ≫
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).comparison.app
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (squareTermComparison R A R' A')
        (ComplexShape.up ℤ)).app M) ≫
      (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryFactors.inv.app
        (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) := by
  refine ((Iso.eq_comp_inv
    ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryFactors.app
      (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M))).2 ((Category.assoc _ _ _).trans
        (squareDerivedComparison_app_Q R A R' A' M))).trans ?_
  exact comp_assoc_helper (C := DerivedCategory (ModuleCat.{u} R')) _ _ _ _

end Square


section Comparison

variable (R A R' A' R₀) in
/-- `restrictScalarsSquareHom` is an isomorphism, the identity on underlying groups. -/
def restrictScalarsSquareIso :
    ModuleCat.restrictScalars (algebraMap R' A') ⋙ ModuleCat.restrictScalars (algebraMap R₀ R') ≅
      ModuleCat.restrictScalars (modelRingMap R A R' A' R₀) ⋙
        ModuleCat.restrictScalars (algebraMap R₀ B₀) where
  hom := restrictScalarsSquareHom R A R' A' R₀
  inv :=
    { app X := ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars (algebraMap R₀ B₀)).obj
          ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj X))
        (Y := (ModuleCat.restrictScalars (algebraMap R₀ R')).obj
          ((ModuleCat.restrictScalars (algebraMap R' A')).obj X))
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => by
            have h : algebraMap R' A' (algebraMap R₀ R' r) =
                modelRingMap R A R' A' R₀ (algebraMap R₀ B₀ r) := by
              rw [Algebra.TensorProduct.right_algebraMap_apply, modelRingMap_tmul, map_one,
                one_mul]
            exact congrArg (fun a : A' => a • (show X from x)) h.symm }
      naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The model map, with its target spelled as a restriction of scalars. -/
abbrev modelMapX (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    modelComplex A F M ⟶
      ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) :=
  modelMapE (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε M

/-- The derived map of the model complex to `A' ⊗_A M`, read over `A ⊗_R R₀`. -/
abbrev modelDerivedMap (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    DerivedCategory.Q.obj (modelComplex A F M) ⟶
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) :=
  DerivedCategory.Q.map (modelMapX (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε M) ≫
    (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategoryFactors.inv.app
      (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)

section Spelling

variable (R R') in
/-- The comparison of derived base change to `R'` with termwise base change, with its target
spelled as a complex. -/
def alphaG (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.obj
        (DerivedCategory.Q.obj X) ⟶
      DerivedCategory.Q.obj (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X) :=
  (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).comparison.app X

variable (A A') in
/-- The comparison of derived base change to `A'` with termwise base change, with its target
spelled as a complex. -/
def alphaH (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj
        (DerivedCategory.Q.obj M) ⟶
      DerivedCategory.Q.obj (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) :=
  (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).comparison.app M

variable (R A R' A') in
/-- The comparison `R' ⊗_R M ⟶ A' ⊗_A M` of complexes. -/
def tau0C (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ⟶
      ((ModuleCat.restrictScalars (algebraMap R' A')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) :=
  (NatTrans.mapHomologicalComplex (squareTermComparison R A R' A') (ComplexShape.up ℤ)).app M

variable (R A R' A' R₀) in
/-- The identity between the two restrictions of a complex of `A'`-modules to `R₀`. -/
def squareC (X : CochainComplex (ModuleCat.{u} A') ℤ) :
    ((ModuleCat.restrictScalars (algebraMap R₀ R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R' A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X) ⟶
      ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X) :=
  (NatTrans.mapHomologicalComplex (restrictScalarsSquareHom R A R' A' R₀) (ComplexShape.up ℤ)).app X

/-- The comparison of the base model, with its target spelled as a complex. -/
def cC (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (baseModelFunctor R F).obj X ⟶
      ((ModuleCat.restrictScalars (algebraMap R₀ R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X) :=
  (baseModelComparison F ε).app X

omit [Module.Flat R R₀] [QuasiIso ε] in
/-- Restricted to `R₀`, the model map at `M` is the comparison of the base model, followed by
the termwise comparison `R' ⊗_R M ⟶ A' ⊗_A M` and the identity `squareC`. -/
theorem modelMapX_restrict (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (modelRestrictIso F M).inv ≫
        ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (modelMapX (R := R) (A := A) (R' := R') (A' := A')
            (R₀ := R₀) ε M) =
      cC ε (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≫
        ((ModuleCat.restrictScalars (algebraMap R₀ R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (tau0C R A R' A' M) ≫
        squareC R A R' A' R₀ (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) :=
  modelMapE_restrict (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) F ε M

/-- The derived comparison of the square at `M`, followed by `alphaH`, is `alphaG` followed by
the termwise comparison `tau0C`, with the target identified through restriction of scalars. -/
theorem squareDerivedComparison_app_Q'' (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app
        (DerivedCategory.Q.obj M) ≫
      (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map (alphaH A A' M) =
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.map
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.hom.app M) ≫
      alphaG R R' (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Q.map (tau0C R A R' A' M) ≫
      (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryFactors.inv.app
        (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) :=
  squareDerivedComparison_app_Q' R A R' A' M

/-- The lift `baseModelLift`, composed with the comparison `cC` of the base model, is the
restriction to `R₀` of the comparison `alphaG` of derived with termwise base change. -/
theorem baseModelLift_fac' (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (baseModelLift (R := R) ε hF).app (DerivedCategory.Q.obj X) ≫
        (baseModelDerivedFac hF).hom.app X ≫ DerivedCategory.Q.map (cC ε X) ≫
        (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) =
      (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory.map (alphaG R R' X) := by
  refine Eq.trans ?_ (baseModelLift_fac (R := R) ε hF X)
  congr 1
  simp only [baseModelDerivedComparison, cC, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp]
  exact congrArg (fun t => _ ≫ _ ≫ t) (Category.comp_id _).symm

end Spelling

/-- Two restrictions of a complex to `R₀` and their derived counterparts. -/
abbrev restrictTwiceIso {S T : Type u} [CommRing S] [CommRing T] (φ : R₀ →+* S) (χ : S →+* T)
    (X : CochainComplex (ModuleCat.{u} T) ℤ) :
    DerivedCategory.Q.obj (((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.restrictScalars χ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X)) ≅
      (ModuleCat.restrictScalars φ).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars χ).mapDerivedCategory.obj (DerivedCategory.Q.obj X)) :=
  ((ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.app
      (((ModuleCat.restrictScalars χ).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)).symm ≪≫
    (ModuleCat.restrictScalars φ).mapDerivedCategory.mapIso
      ((ModuleCat.restrictScalars χ).mapDerivedCategoryFactors.app X).symm

/-- A functor sends the inverse of a component of a natural isomorphism, followed by the
component itself, to the identity. -/
private theorem map_inv_app_comp_map_hom_app {C D E : Type*} [Category C] [Category D]
    [Category E] (F : D ⥤ E) {G₁ G₂ : C ⥤ D} (α : G₁ ≅ G₂) (X : C) :
    F.map (α.inv.app X) ≫ F.map (α.hom.app X) = 𝟙 _ := by
  rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]

/-- **The derived identity of the model.** Read in `D(R₀)` through the identification `modelXi`,
the comparison of Stacks 065Z at `M` is the derived map of the model. -/
theorem modelXi_comparison (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (modelXi ε hF M).hom ≫
        (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory.map
          ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app
              (DerivedCategory.Q.obj M) ≫
            (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map
              (alphaH A A' M)) ≫
        (restrictTwiceIso (algebraMap R₀ R') (algebraMap R' A')
          (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)).inv ≫
        DerivedCategory.Q.map (squareC R A R' A' R₀
          (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) =
      (ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategory.map
          (modelDerivedMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε M) ≫
        (restrictTwiceIso (algebraMap R₀ B₀) (modelRingMap R A R' A' R₀)
          (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)).inv := by
  have hR : (ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategory.map
        (modelDerivedMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε M) ≫
      (restrictTwiceIso (algebraMap R₀ B₀) (modelRingMap R A R' A' R₀)
        (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).inv =
      (ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategoryFactors.hom.app
          (modelComplex A F M) ≫
        DerivedCategory.Q.map (((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (modelMapX (R := R) (A := A) (R' := R') (A' := A')
            (R₀ := R₀) ε M)) := by
    dsimp only [modelDerivedMap, restrictTwiceIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Iso.app_hom]
    have e := map_inv_app_comp_map_hom_app
      (ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategory
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategoryFactors
      (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)
    rw [Functor.map_comp, Category.assoc, reassoc_of% e]
    exact Functor.mapDerivedCategoryFactors_hom_naturality _ _
  rw [hR]
  have hτ := squareDerivedComparison_app_Q'' (R := R) (A := A) (R' := R') (A' := A') M
  rw [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc, hτ]
  dsimp only [modelXi, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    asIso_inv, Functor.comp_map, restrictTwiceIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  simp only [Functor.map_comp, Category.assoc]
  have e1 := map_inv_app_comp_map_hom_app
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor ⋙
      (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory)
    (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors M
  have e2 := map_inv_app_comp_map_hom_app
    (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory
    (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryFactors
    (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M)
  have e3 := baseModelLift_fac' ε hF
    (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
  rw [← IsIso.eq_inv_comp] at e3
  have e5 := (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategoryFactors_hom_naturality
    (tau0C R A R' A' M)
  rw [reassoc_of% e1, reassoc_of% e2, ← reassoc_of% e3,
    Iso.inv_hom_id_app_assoc, reassoc_of% e5, Iso.inv_hom_id_app_assoc]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← modelMapX_restrict (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε M,
    Iso.hom_inv_id_assoc]

end Comparison

section Homology

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The cohomology comparison of `G` at the derived image of a complex, after the factorization of
`G` through the derived category, is the termwise cohomology comparison of `G`. -/
private theorem homologyFunctor_map_mapDerivedCategoryFactors_inv_comp
    {S S' : Type u} [Ring S] [Ring S'] (G : ModuleCat.{u} S ⥤ ModuleCat.{u} S') [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (n : ℤ)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S') n).map
        (G.mapDerivedCategoryFactors.inv.app K) ≫
      (G.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K) =
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S') n).hom.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
      G.map ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) n).inv.app K) := by
  rw [Functor.mapDerivedCategoryHomologyIso_hom_app_Q, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The compatibility square on the image of a complex, for exact functors between categories
of modules.**  Let `τ : F ⟶ G ⋙ H` be a natural transformation of exact functors.  The derived
map built from `τ` is carried to `τ` itself, on the cohomology of a complex, by the cohomology
comparisons of `F`, of `G` and of `H`. -/
private theorem compat_Q_moduleCat {S₁ S₂ S₃ : Type u} [Ring S₁] [Ring S₂] [Ring S₃]
    (F : ModuleCat.{u} S₁ ⥤ ModuleCat.{u} S₃) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : ModuleCat.{u} S₁ ⥤ ModuleCat.{u} S₂) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (H : ModuleCat.{u} S₂ ⥤ ModuleCat.{u} S₃)
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] (τ : F ⟶ G ⋙ H) (n : ℤ)
    (K : CochainComplex (ModuleCat.{u} S₁) ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S₃) n).map
        (F.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
          H.mapDerivedCategoryFactors.inv.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app K)) ≫
      (H.mapDerivedCategoryHomologyIso n).hom.app
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      H.map ((G.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K)) =
    (F.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K) ≫
      τ.app ((DerivedCategory.homologyFunctor (ModuleCat.{u} S₁) n).obj
        (DerivedCategory.Q.obj K)) := by
  have hT : ∀ T : ShortComplex (ModuleCat.{u} S₁),
      ShortComplex.homologyMap (T.mapNatTrans τ) ≫
          ((T.map G).mapHomologyIso H).hom ≫ H.map (T.mapHomologyIso G).hom =
        (T.mapHomologyIso F).hom ≫ τ.app T.homology := by
    intro T
    rw [ShortComplex.homologyMap_mapNatTrans, ← ShortComplex.mapHomologyIso_comp_hom]
    simp
  have homologyIso_mapNatTrans_compat :
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} S₃) (ComplexShape.up ℤ) n).map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
        (H.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        H.map ((G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K) =
      (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
        τ.app ((HomologicalComplex.homologyFunctor (ModuleCat.{u} S₁) (ComplexShape.up ℤ) n).obj
          K) :=
    hT ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S₁) (ComplexShape.up ℤ) n).obj K)
  have h1 : (DerivedCategory.homologyFunctor (ModuleCat.{u} S₃) n).map
        (H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app K)) ≫
      (H.mapDerivedCategoryHomologyIso n).hom.app
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) =
      (H.mapDerivedCategoryHomologyIso n).hom.app
        (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      H.map ((DerivedCategory.homologyFunctor (ModuleCat.{u} S₂) n).map
        (G.mapDerivedCategoryFactors.inv.app K)) :=
    (H.mapDerivedCategoryHomologyIso n).hom.naturality _
  have h2 := homologyFunctor_map_mapDerivedCategoryFactors_inv_comp H n
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have h3 := homologyFunctor_map_mapDerivedCategoryFactors_inv_comp G n K
  have h4 : H.map ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S₂) n).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      H.map ((DerivedCategory.homologyFunctor (ModuleCat.{u} S₂) n).map
        (G.mapDerivedCategoryFactors.inv.app K)) ≫
      H.map ((G.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K)) =
      H.map ((G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K) ≫
      H.map (G.map ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S₁) n).inv.app K)) := by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc, h3,
      Iso.inv_hom_id_app_assoc, Functor.map_comp]
  have h5 : (DerivedCategory.homologyFunctor (ModuleCat.{u} S₃) n).map
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)) ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S₃) n).hom.app
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S₃) n).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} S₃) (ComplexShape.up ℤ) n).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S₃) n).hom.naturality _
  have h6 : F.map ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S₁) n).inv.app K) ≫
      τ.app ((DerivedCategory.homologyFunctor (ModuleCat.{u} S₁) n).obj (DerivedCategory.Q.obj K)) =
      τ.app ((HomologicalComplex.homologyFunctor (ModuleCat.{u} S₁) (ComplexShape.up ℤ) n).obj K) ≫
      H.map (G.map ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S₁) n).inv.app K)) :=
    τ.naturality _
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, h4, Functor.mapDerivedCategoryHomologyIso_hom_app_Q,
    reassoc_of% h5, reassoc_of% homologyIso_mapNatTrans_compat]
  simp only [Category.assoc]
  rw [h6]

/-- **The comparison of Stacks 065Z on cohomology, through the model.** Read over `R₀`, the
cohomology comparison at `M` is the cohomology of the derived map of the model. -/
theorem modelHomology_comparison (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (modelHomologyIso ε hF n M).hom ≫
        (ModuleCat.restrictScalars (algebraMap R₀ R')).map
          (cohomologyComparisonMap (R := R) (R' := R') (DerivedCategory.Q.obj M)
            (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M)) (alphaH A A' M) n) ≫
        (restrictScalarsSquareHom R A R' A' R₀).app
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj
            (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M))) =
      (ModuleCat.restrictScalars (algebraMap R₀ B₀)).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
            (modelDerivedMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε M)) ≫
        (ModuleCat.restrictScalars (algebraMap R₀ B₀)).map
          (((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategoryHomologyIso
            n).hom.app (DerivedCategory.Q.obj (((ModuleCat.extendScalars
              (algebraMap A A')).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) := by
  have c1 := compat_Q_moduleCat
    (ModuleCat.restrictScalars (algebraMap R' A') ⋙ ModuleCat.restrictScalars (algebraMap R₀ R'))
    (ModuleCat.restrictScalars (algebraMap R' A')) (ModuleCat.restrictScalars (algebraMap R₀ R'))
    (𝟙 _) n (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M)
  have c2 := compat_Q_moduleCat
    (ModuleCat.restrictScalars (algebraMap R' A') ⋙ ModuleCat.restrictScalars (algebraMap R₀ R'))
    (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀))
    (ModuleCat.restrictScalars (algebraMap R₀ B₀))
    (restrictScalarsSquareHom R A R' A' R₀) n
    (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M)
  have D := modelXi_comparison (R := R) (A := A) (R' := R') (A' := A') ε hF M
  simp only [NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Functor.comp_obj] at c1
  simp only [Category.comp_id, Category.id_comp] at c1
  let Hn := DerivedCategory.homologyFunctor (ModuleCat.{u} R₀) n
  let Fcf := (ModuleCat.restrictScalars (algebraMap R' A') ⋙
    ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategoryFactors.app
      (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)
  let rT := restrictTwiceIso (algebraMap R₀ R') (algebraMap R' A')
    (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M)
  let rT' := restrictTwiceIso (algebraMap R₀ B₀) (modelRingMap R A R' A' R₀)
    (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M)
  have c1' : Hn.map (Fcf.hom ≫ rT.hom) ≫
      ((ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategoryHomologyIso n).hom.app
          ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj
            (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M))) ≫
        (ModuleCat.restrictScalars (algebraMap R₀ R')).map
          (((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso n).hom.app
            (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M))) =
      ((ModuleCat.restrictScalars (algebraMap R' A') ⋙
        ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategoryHomologyIso
          n).hom.app (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M)) := c1
  have c2' : Hn.map (Fcf.hom ≫ DerivedCategory.Q.map (squareC R A R' A' R₀
      (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)) ≫ rT'.hom) ≫
      ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategoryHomologyIso n).hom.app
          ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategory.obj
            (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M))) ≫
        (ModuleCat.restrictScalars (algebraMap R₀ B₀)).map
          (((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategoryHomologyIso
            n).hom.app (DerivedCategory.Q.obj
                (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj M))) =
      ((ModuleCat.restrictScalars (algebraMap R' A') ⋙
        ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategoryHomologyIso
          n).hom.app (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M)) ≫
        (restrictScalarsSquareHom R A R' A' R₀).app
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj
            (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M))) := c2
  have D' : (ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategory.map
        (modelDerivedMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε M) =
      ((modelXi ε hF M).hom ≫
        (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory.map
          ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app
              (DerivedCategory.Q.obj M) ≫
            (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map
              (alphaH A A' M)) ≫ rT.inv ≫ Fcf.inv) ≫
        (Fcf.hom ≫ DerivedCategory.Q.map (squareC R A R' A' R₀
          (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) ≫ rT'.hom) := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% D, Iso.inv_hom_id, Category.comp_id]
  rw [← cancel_epi (((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategoryHomologyIso
    n).hom.app (DerivedCategory.Q.obj (modelComplex A F M)))]
  have nρ := ((ModuleCat.restrictScalars (algebraMap R₀ B₀)).mapDerivedCategoryHomologyIso
    n).hom.naturality (modelDerivedMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε M)
  dsimp only [Functor.comp_map] at nρ
  dsimp only [Hn] at c1' c2'
  rw [← reassoc_of% nρ, D', Functor.map_comp, Category.assoc, c2', ← c1']
  dsimp only [modelHomologyIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, cohomologyComparisonMap]
  have nπ := ((ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategoryHomologyIso
    n).hom.naturality ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app
      (DerivedCategory.Q.obj M) ≫
        (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map (alphaH A A' M))
  dsimp only [Functor.comp_map] at nπ
  generalize (squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app
      (DerivedCategory.Q.obj M) ≫
        (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map (alphaH A A' M) =
      g at nπ ⊢
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc, Iso.map_inv_hom_id_assoc]
  rw [reassoc_of% nπ]

end Homology

end RingTheory.TorIndependence
