module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseModelChange
import all StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.LocalizedModuleCriterion

/-!
# The localized model of a square of rings

Let `R → A`, `R → R'`, `A → B`, `R' → B` be a square of rings with a model `(R₀, F)`, and let
`R₁ → A₁`, `R₁ → R'₁`, `A₁ → B`, `R'₁ → B` be a second square whose rings are localizations of
`R`, `A`, `R'`. Localizing `R₀` at the elements whose image in `R'₁` is a unit gives a model of
the second square. Hence, when `B` is a localization of `A₁ ⊗_{R₁} R'₁`, the base change map on
cohomology `ringBaseChangeCohomologyMap` of the second square is invertible exactly when the
cohomology of the model map of the first square is a localization at the elements of `A ⊗_R R₀`
becoming units in `B`.

## Main results

* `RingTheory.TorIndependence.isIso_local_iff_isLocalizedModule_modelKappa`: the base change map
  on cohomology of the localized square is invertible in degree `n` if and only if the cohomology
  of the model map of the original square is a localization at the elements of `A ⊗_R R₀`
  becoming units in `B`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open CochainComplex.DerivedExtensionScalars

universe u

namespace RingTheory.TorIndependence

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The saturation of a localization along a surjection.** If `B` is the localization of `C` at
`S` and `σ : D ⟶ C` is surjective, every element of `D` becoming a unit in `B` divides an element
of the preimage of `S`. -/
theorem exists_mul_mem_comap_of_isUnit {C D B : Type u} [CommRing C] [CommRing D] [CommRing B]
    [Algebra C B] (S : Submonoid C) [IsLocalization S B] (σ : D →+* C)
    (hσ : Function.Surjective σ)
    (x : IsLocalizedModule.unitsComap ((algebraMap C B).comp σ)) :
    ∃ m : D, m * x ∈ S.comap σ := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨v, hv⟩ := (hx : IsUnit (algebraMap C B (σ x)))
  obtain ⟨⟨c, s⟩, hc⟩ := IsLocalization.surj S (↑v⁻¹ : B)
  have hv' : algebraMap C B (σ x) = v := hv.symm
  have h1 : algebraMap C B (σ x * c) = algebraMap C B s := by
    rw [map_mul]
    show _ * algebraMap C B (c, s).1 = _
    rw [← hc, hv', ← mul_assoc, Units.mul_inv, one_mul]
  obtain ⟨s', hs'⟩ := IsLocalization.exists_of_eq (M := S) h1
  obtain ⟨m, hm⟩ := hσ (s' * c)
  refine ⟨m, ?_⟩
  show σ (m * x) ∈ S
  rw [map_mul, hm, mul_assoc, mul_comm c, hs']
  exact S.mul_mem s'.2 s.2

/-- Localization at the preimage of `S` under a surjection `σ` is localization at the elements
becoming units in the localization of the target at `S`. -/
private theorem isLocalizedModule_comap_iff_unitsComap {C D B M N : Type u} [CommRing C]
    [CommRing D] [CommRing B] [Algebra C B] [AddCommGroup M] [Module D M] [AddCommGroup N]
    [Module D N] (S : Submonoid C) [IsLocalization S B] (σ : D →+* C) (hσ : Function.Surjective σ)
    (f : M →ₗ[D] N) :
    IsLocalizedModule (S.comap σ) f ↔
      IsLocalizedModule (IsLocalizedModule.unitsComap ((algebraMap C B).comp σ)) f :=
  IsLocalizedModule.iff_of_exists_mul_mem (S.comap σ) _
    (fun x hx => IsLocalization.map_units B (⟨σ x, hx⟩ : S))
    (exists_mul_mem_comap_of_isUnit S σ hσ) f

section Units

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

local notation "B₀" => A ⊗[R] R₀

variable {F : CochainComplex (ModuleCat.{u} R₀) ℤ}
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))
  [Module.Flat R R₀] (hF : F.KFlat) [QuasiIso ε] (n : ℤ)

include hF in
/-- **The criterion of the model, at the units.** When `A'` is a localization of `A ⊗_R R'`,
the base change map `ringBaseChangeCohomologyMap` in degree `n` is invertible exactly when the
cohomology of the model map is a localization at the elements of `A ⊗_R R₀` becoming units in
`A'`. -/
theorem isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule_units
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      ∃ S : Submonoid (A ⊗[R] R'), IsLocalization S A')
    (hsurj : Function.Surjective (algebraMap R₀ R'))
    (N : CochainComplex (ModuleCat.{u} A) ℤ) (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
        (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n) ↔
      IsLocalizedModule (IsLocalizedModule.unitsComap (modelRingMap R A R' A' R₀))
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
          (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
            ε N Z α))).hom := by
  let := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
  obtain ⟨S, hS⟩ := hloc
  rw [isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule ε hF n S hS hsurj]
  exact isLocalizedModule_comap_iff_unitsComap S _
    (TensorProduct.map_surjective Function.surjective_id hsurj) _

end Units

section Augmentation

variable {R₀ R₀₁ R' R'₁ : Type u} [CommRing R₀] [CommRing R₀₁] [CommRing R'] [CommRing R'₁]
  [Algebra R₀ R₀₁] [Algebra R₀ R'] [Algebra R₀₁ R'₁] [Algebra R' R'₁] [Algebra R₀ R'₁]
  [IsScalarTower R₀ R₀₁ R'₁] [IsScalarTower R₀ R' R'₁]

/-- The map `R₀₁ ⊗_{R₀} R' ⟶ R'₁`, `a ⊗ r ↦ a · r`. -/
def baseChangeAugmentationMap :
    (baseChangeFunctor R₀ R₀₁).obj (ModuleCat.of R₀ R') ⟶ ModuleCat.of R₀₁ R'₁ :=
  ModuleCat.ofHom (LinearMap.liftBaseChange R₀₁ (IsScalarTower.toAlgHom R₀ R' R'₁).toLinearMap)

/-- The map `baseChangeAugmentationMap` sends `a ⊗ r` to `a • r`, with `r` viewed in `R'₁`. -/
theorem baseChangeAugmentationMap_tmul (a : R₀₁) (r : R') :
    (baseChangeAugmentationMap (R₀ := R₀) (R₀₁ := R₀₁) (R' := R') (R'₁ := R'₁)).hom (a ⊗ₜ r) =
      a • algebraMap R' R'₁ r :=
  rfl

variable (F : CochainComplex (ModuleCat.{u} R₀) ℤ)
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))

/-- The base change of an augmentation `F ⟶ R'` to an augmentation `R₀₁ ⊗_{R₀} F ⟶ R'₁`. -/
def baseChangeAugmentation :
    ((baseChangeFunctor R₀ R₀₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj F ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} R₀₁) 0).obj (ModuleCat.of R₀₁ R'₁) :=
  ((baseChangeFunctor R₀ R₀₁).mapHomologicalComplex (ComplexShape.up ℤ)).map ε ≫
    (HomologicalComplex.singleMapHomologicalComplex (baseChangeFunctor R₀ R₀₁)
      (ComplexShape.up ℤ) 0).hom.app (ModuleCat.of R₀ R') ≫
    (CochainComplex.singleFunctor (ModuleCat.{u} R₀₁) 0).map baseChangeAugmentationMap

/-- The augmentation of `baseChangeAugmentation F ε` sends `1 ⊗ w` to the image in `R'₁` of the
augmentation of `w`. -/
theorem augmentation_baseChangeAugmentation (w : F.X 0) :
    augmentation _ (baseChangeAugmentation (R₀₁ := R₀₁) (R'₁ := R'₁) F ε) ((1 : R₀₁) ⊗ₜ[R₀] w) =
      algebraMap R' R'₁ (augmentation F ε w) := by
  show (baseChangeAugmentationMap (R₀ := R₀) (R₀₁ := R₀₁) (R' := R') (R'₁ := R'₁)).hom
    ((1 : R₀₁) ⊗ₜ[R₀] augmentation F ε w) = _
  rw [baseChangeAugmentationMap_tmul, one_smul]

/-- If `R₀₁` is flat over `R₀`, `ε` is a quasi-isomorphism and `R₀₁ ⊗_{R₀} R' ⟶ R'₁` is an
isomorphism, then `baseChangeAugmentation F ε` is a quasi-isomorphism. -/
theorem quasiIso_baseChangeAugmentation [Module.Flat R₀ R₀₁] [QuasiIso ε]
    [IsIso (baseChangeAugmentationMap (R₀ := R₀) (R₀₁ := R₀₁) (R' := R') (R'₁ := R'₁))] :
    QuasiIso (baseChangeAugmentation (R₀₁ := R₀₁) (R'₁ := R'₁) F ε) := by
  have : QuasiIso (((baseChangeFunctor R₀ R₀₁).mapHomologicalComplex (ComplexShape.up ℤ)).map ε) :=
    quasiIso_baseChangeFunctor_map (R := R₀) (R₀ := R₀₁) ε
  unfold baseChangeAugmentation
  infer_instance

omit [Algebra R₀₁ R'₁] [IsScalarTower R₀ R₀₁ R'₁] in
/-- `R'₁` is the localization of `R'` at `V`, read over `R₀` along a surjection `R₀ ⟶ R'`. -/
theorem isLocalizedModule_algebraMap_comap (hσ : Function.Surjective (algebraMap R₀ R'))
    (V : Submonoid R') [IsLocalization V R'₁] :
    IsLocalizedModule (V.comap (algebraMap R₀ R'))
      (IsScalarTower.toAlgHom R₀ R' R'₁).toLinearMap := by
  have h1 := (ModuleCat.isLocalizedModule_restrictScalars_iff (algebraMap R₀ R') hσ V
    (ModuleCat.ofHom (X := ModuleCat.of R' R') (Y := ModuleCat.of R' R'₁)
      (Algebra.linearMap R' R'₁))).2
      (inferInstanceAs (IsLocalizedModule V (Algebra.linearMap R' R'₁)))
  let e₁ : R' ≃ₗ[R₀] (ModuleCat.restrictScalars (algebraMap R₀ R')).obj (ModuleCat.of R' R') :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => Algebra.smul_def r x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : (ModuleCat.restrictScalars (algebraMap R₀ R')).obj (ModuleCat.of R' R'₁) ≃ₗ[R₀] R'₁ :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        show (algebraMap R₀ R' r) • (show R'₁ from x) = r • (show R'₁ from x)
        rw [algebraMap_smul]
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h2 := IsLocalizedModule.of_linearEquiv (V.comap (algebraMap R₀ R'))
    ((ModuleCat.restrictScalars (algebraMap R₀ R')).map (ModuleCat.ofHom (X := ModuleCat.of R' R')
      (Y := ModuleCat.of R' R'₁) (Algebra.linearMap R' R'₁))).hom e₂
  have h3 := IsLocalizedModule.of_linearEquiv_right (V.comap (algebraMap R₀ R'))
    (e₂.toLinearMap ∘ₗ ((ModuleCat.restrictScalars (algebraMap R₀ R')).map
      (ModuleCat.ofHom (X := ModuleCat.of R' R') (Y := ModuleCat.of R' R'₁)
        (Algebra.linearMap R' R'₁))).hom) e₁
  convert h3 using 1
  exact LinearMap.ext fun _ => rfl

/-- If `R₀₁` is the localization of `R₀` at `V` and `R' ⟶ R'₁` is a localization of `R₀`-modules
at `V`, then `R₀₁ ⊗_{R₀} R' ⟶ R'₁` is an isomorphism. -/
theorem isIso_baseChangeAugmentationMap (V : Submonoid R₀) [IsLocalization V R₀₁]
    (h : IsLocalizedModule V (IsScalarTower.toAlgHom R₀ R' R'₁).toLinearMap) :
    IsIso (baseChangeAugmentationMap (R₀ := R₀) (R₀₁ := R₀₁) (R' := R') (R'₁ := R'₁)) := by
  have hb := (isLocalizedModule_iff_isBaseChange V R₀₁
    (IsScalarTower.toAlgHom R₀ R' R'₁).toLinearMap).1 h
  rw [ConcreteCategory.isIso_iff_bijective]
  have : (baseChangeAugmentationMap (R₀ := R₀) (R₀₁ := R₀₁) (R' := R') (R'₁ := R'₁)).hom =
      hb.equiv.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun a r => ?_
    exact (baseChangeAugmentationMap_tmul a r).trans (IsBaseChange.equiv_tmul hb a r).symm
  show Function.Bijective (baseChangeAugmentationMap (R₀ := R₀) (R₀₁ := R₀₁) (R' := R')
    (R'₁ := R'₁)).hom
  rw [this]
  exact hb.equiv.bijective

end Augmentation


section Local

variable {R A R' B R₁ A₁ R'₁ R₀ : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing B]
  [CommRing R₁] [CommRing A₁] [CommRing R'₁] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R B] [Algebra A B] [Algebra R' B]
  [IsScalarTower R A B] [IsScalarTower R R' B]
  [Algebra R₁ A₁] [Algebra R₁ R'₁] [Algebra R₁ B] [Algebra A₁ B] [Algebra R'₁ B]
  [IsScalarTower R₁ A₁ B] [IsScalarTower R₁ R'₁ B]
  [Algebra R R₁] [Algebra A A₁] [Algebra R' R'₁] [Algebra R A₁] [Algebra R R'₁]
  [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁] [IsScalarTower A A₁ B] [IsScalarTower R' R'₁ B]
  [IsScalarTower R R₁ R'₁] [IsScalarTower R R' R'₁]
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R'] [Module.Flat R R₀]

local notation "B₀" => A ⊗[R] R₀

/-- **The base change map of a localized square and the localized model map.** Let `R₁`, `A₁`,
`R'₁` be localizations of `R`, `A`, `R'`, with `B` a localization of `A₁ ⊗_{R₁} R'₁`,
`N₁ ≅ A₁ ⊗_A N`, and `α`, `α₁` compatible maps to a complex `Z` of `B`-modules. The base change
map on cohomology of the square `R₁ → A₁ → B ← R'₁` at `α₁` is invertible in degree `n` if and
only if the cohomology of the model map of the square `R → A → B ← R'` at `α` is a localization
at the elements of `A ⊗_R R₀` becoming units in `B`. -/
theorem isIso_local_iff_isLocalizedModule_modelKappa (U : Submonoid R) [IsLocalization U R₁]
    (W : Submonoid A) [IsLocalization W A₁] (V : Submonoid R') [IsLocalization V R'₁]
    (hsurj : Function.Surjective (algebraMap R₀ R'))
    {F : CochainComplex (ModuleCat.{u} R₀) ℤ}
    (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))
    (hF : F.KFlat) [QuasiIso ε]
    (hloc₁ : letI := (baseChangeTensorRingMap (R := R₁) (A := A₁) (R' := R'₁) (A' := B)).toAlgebra
      ∃ S : Submonoid (A₁ ⊗[R₁] R'₁), IsLocalization S B)
    {N : CochainComplex (ModuleCat.{u} A) ℤ} {N₁ : CochainComplex (ModuleCat.{u} A₁) ℤ}
    (eN : ((baseChangeFunctor A A₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj N ≅ N₁)
    {Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (α : ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z)
    (α₁ : ((ModuleCat.extendScalars (algebraMap A₁ B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N₁ ⟶ Z)
    (hα : ∀ i (m : N.X i), (α₁.f i).hom ((1 : B) ⊗ₜ[A₁,algebraMap A₁ B]
      (eN.hom.f i).hom ((1 : A₁) ⊗ₜ[A] m)) = (α.f i).hom ((1 : B) ⊗ₜ[A,algebraMap A B] m))
    (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R₁) (R' := R'₁) (DerivedCategory.Q.obj N₁)
      (DerivedCategory.Q.obj Z) (alphaH A₁ B N₁ ≫ DerivedCategory.Q.map α₁) n) ↔
    IsLocalizedModule (IsLocalizedModule.unitsComap (modelRingMap R A R' B R₀))
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map (DerivedCategory.Q.map
        (modelKappa (R := R) (A := A) (R' := R') (A' := B) (R₀ := R₀) ε N Z α))).hom := by
  let σ : R₀ →+* R'₁ := (algebraMap R' R'₁).comp (algebraMap R₀ R')
  let Zs : Submonoid R₀ := IsLocalizedModule.unitsComap σ
  let R₀₁ := Localization Zs
  have hU : ∀ u : U, IsUnit (algebraMap R R₀₁ u) := by
    intro u
    rw [IsScalarTower.algebraMap_apply R R₀ R₀₁]
    refine IsLocalization.map_units R₀₁ (⟨algebraMap R R₀ u, ?_⟩ : Zs)
    show IsUnit (algebraMap R' R'₁ (algebraMap R₀ R' (algebraMap R R₀ u)))
    rw [← IsScalarTower.algebraMap_apply R R₀ R', ← IsScalarTower.algebraMap_apply R R' R'₁,
      IsScalarTower.algebraMap_apply R R₁ R'₁]
    exact (IsLocalization.map_units R₁ u).map _
  let : Algebra R₁ R₀₁ := (IsLocalization.lift (M := U) hU).toAlgebra
  have : IsScalarTower R R₁ R₀₁ := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.lift_eq (M := U) hU r).symm
  have hZsU : ∀ z : Zs, IsUnit (σ z) := fun z => z.2
  let : Algebra R₀₁ R'₁ := (IsLocalization.lift (M := Zs) (g := σ) hZsU).toAlgebra
  have hσ : ∀ x : R₀, algebraMap R₀₁ R'₁ (algebraMap R₀ R₀₁ x) =
      algebraMap R' R'₁ (algebraMap R₀ R' x) := fun x =>
    IsLocalization.lift_eq (M := Zs) (g := σ) hZsU x
  have : IsScalarTower R₁ R₀₁ R'₁ := IsScalarTower.of_algebraMap_eq' <|
    IsLocalization.ringHom_ext U <| RingHom.ext fun r => by
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply R R₁ R'₁, ← IsScalarTower.algebraMap_apply R R₁ R₀₁,
        IsScalarTower.algebraMap_apply R R₀ R₀₁, hσ, ← IsScalarTower.algebraMap_apply R R₀ R',
        ← IsScalarTower.algebraMap_apply R R' R'₁]
  let : Algebra R₀ R'₁ := σ.toAlgebra
  have : IsScalarTower R₀ R₀₁ R'₁ := IsScalarTower.of_algebraMap_eq fun x => (hσ x).symm
  have : IsScalarTower R₀ R' R'₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat R₁ R₀₁ := (Module.flat_iff_of_isLocalization R₁ U R₀₁).2 inferInstance
  have hsurj₁ : Function.Surjective (algebraMap R₀₁ R'₁) := by
    intro y
    obtain ⟨⟨r, v⟩, hy⟩ := IsLocalization.surj V y
    obtain ⟨x, rfl⟩ := hsurj r
    obtain ⟨t, ht⟩ := hsurj v
    have htZ : t ∈ Zs := by
      show IsUnit (algebraMap R' R'₁ (algebraMap R₀ R' t))
      rw [ht]
      exact IsLocalization.map_units R'₁ v
    refine ⟨IsLocalization.mk' R₀₁ x (⟨t, htZ⟩ : Zs), ?_⟩
    show IsLocalization.lift (M := Zs) (g := σ) hZsU (IsLocalization.mk' R₀₁ x _) = y
    refine (IsLocalization.lift_mk'_spec (M := Zs) (g := σ) hZsU _ _ _).2 ?_
    show algebraMap R' R'₁ (algebraMap R₀ R' x) = algebraMap R' R'₁ (algebraMap R₀ R' t) * y
    rw [ht, mul_comm, hy]
  have hZs : IsLocalizedModule Zs (IsScalarTower.toAlgHom R₀ R' R'₁).toLinearMap := by
    have h1 := isLocalizedModule_algebraMap_comap (R₀ := R₀) (R' := R') (R'₁ := R'₁) hsurj V
    exact (isLocalizedModule_comap_iff_unitsComap V _ hsurj _).1 h1
  have := isIso_baseChangeAugmentationMap (R₀ := R₀) (R₀₁ := R₀₁) (R' := R') (R'₁ := R'₁) Zs hZs
  have := quasiIso_baseChangeAugmentation (R₀ := R₀) (R₀₁ := R₀₁) (R' := R') (R'₁ := R'₁) F ε
  exact (isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule_units (R := R₁) (A := A₁)
    (R' := R'₁) (A' := B) (R₀ := R₀₁) (baseChangeAugmentation (R₀₁ := R₀₁) (R'₁ := R'₁) F ε)
    (kFlat_baseChangeFunctor_obj (R := R₀) (R₀ := R₀₁) hF) n hloc₁ hsurj₁ N₁ Z α₁).trans
    (isLocalizedModule_modelKappa_iff_local (R₀₁ := R₀₁) eN F ε
    (baseChangeAugmentation (R₀₁ := R₀₁) (R'₁ := R'₁) F ε) α α₁ U W Zs hσ
    (augmentation_baseChangeAugmentation (R₀₁ := R₀₁) (R'₁ := R'₁) F ε) hα n)

end Local

end RingTheory.TorIndependence
