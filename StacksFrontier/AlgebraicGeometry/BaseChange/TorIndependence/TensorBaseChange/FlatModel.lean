module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.LocalizedModuleCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.RingTensor
public import StacksFrontier.Homology.Tor.DerivedTensorFlatBaseChange

/-!
# The map of Stacks 0DJ7 over a flat base change of rings

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a square of rings in which `R'` is flat over `R` and
`A'` is a localization of `A ⊗_R R'`. For every complex `N` of `A`-modules and every isomorphism
`A' ⊗_A N ≅ Z`, the map of Stacks 0DJ7 is an isomorphism in every degree.

## Main results

* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_of_flat`: if `R'` is flat over `R`
  and `A'` is a localization of `A ⊗_R R'`, the map of Stacks 0DJ7 is an isomorphism in every
  degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard Algebra.TensorProduct.rightAlgebra

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- With `R₀ = R'`, the ring map `A ⊗_R R₀ ⟶ A ⊗_R R'` of the model is bijective. -/
theorem bijective_modelBaseRingMap_self : Function.Bijective (modelBaseRingMap R A R' R') := by
  have h : modelBaseRingMap R A R' R' = RingHom.id _ := by
    refine RingHom.ext fun x ↦ ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  exact h ▸ Function.bijective_id

/-- With `R₀ = R'`, `A'` is a localization of `A ⊗_R R₀` through the ring map of the model. -/
theorem isLocalization_modelRingMap_self (S : Submonoid (A ⊗[R] R'))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      IsLocalization S A') :
    letI := (modelRingMap R A R' A' R').toAlgebra
    IsLocalization (S.comap (modelBaseRingMap R A R' R')) A' := by
  let := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
  let σ := RingEquiv.ofBijective (modelBaseRingMap R A R' R') bijective_modelBaseRingMap_self
  have h := IsLocalization.isLocalization_of_base_ringEquiv S A' σ.symm
  have hS : S.map σ.symm = S.comap (modelBaseRingMap R A R' R') := by
    ext x
    simp only [Submonoid.mem_map, Submonoid.mem_comap]
    refine ⟨?_, fun hx ↦ ⟨σ x, hx, σ.symm_apply_apply x⟩⟩
    rintro ⟨y, hy, rfl⟩
    convert hy
    exact σ.apply_symm_apply y
  have hA : ((algebraMap (A ⊗[R] R') A').comp σ.symm.symm.toRingHom) =
      modelRingMap R A R' A' R' := RingHom.ext fun _ => rfl
  rwa [hS, hA] at h

variable (X : Type u) [AddCommGroup X] [Module A X]

/-- With `R₀ = R'`, the degreewise map of the model is the localization
`(A ⊗_R R') ⊗_A X ⟶ A' ⊗_A X`. -/
theorem isLocalizedModule_modelTermMap_self (S : Submonoid (A ⊗[R] R'))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      IsLocalization S A') :
    IsLocalizedModule (S.comap (modelBaseRingMap R A R' R'))
      ((modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R')).app
        (ModuleCat.of A X)).hom := by
  let := (modelRingMap R A R' A' R').toAlgebra
  have := isLocalization_modelRingMap_self S hloc
  have : IsScalarTower A (A ⊗[R] R') A' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    show algebraMap A A' a = modelRingMap R A R' A' R' (a ⊗ₜ[R] 1)
    rw [modelRingMap_tmul, map_one, map_one, mul_one]
  let e : (A ⊗[R] R') ⊗[A] X ≃ₗ[A ⊗[R] R']
      ((A ⊗[R] R') ⊗[A] X) ⊗[A ⊗[R] R'] ((A ⊗[R] R') ⊗[R'] R') :=
    (TensorProduct.rid (A ⊗[R] R') _).symm ≪≫ₗ
      TensorProduct.congr (LinearEquiv.refl _ _)
        (TensorProduct.AlgebraTensorModule.rid R' (A ⊗[R] R') (A ⊗[R] R')).symm
  let gX := TensorProduct.AlgebraTensorModule.rTensor A X (Algebra.linearMap (A ⊗[R] R') A')
  let i : A' ⊗[A] X →ₗ[A ⊗[R] R'] (ModuleCat.restrictScalars (modelRingMap R A R' A' R')).obj
      ((baseChangeFunctor A A').obj (ModuleCat.of A X)) :=
    { toFun := fun y ↦ y
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hfac : ((modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R')).app
      (ModuleCat.of A X)).hom ∘ₗ e.toLinearMap = i ∘ₗ gX := by
    refine LinearMap.ext fun t ↦ ?_
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul c x =>
      show modelTermAdd (R := R) (A := A) (R' := R') (A' := A') (R₀ := R') X
        ((c ⊗ₜ[A] x) ⊗ₜ[A ⊗[R] R'] ((1 : A ⊗[R] R') ⊗ₜ[R'] (1 : R'))) = _
      simp only [modelTermAdd_tmul, modelUnitAddHom_tmul, map_one, one_mul]
      rfl
  refine (IsLocalizedModule.comp_iff_of_bijective_right (S := S.comap (modelBaseRingMap R A R' R'))
    e.toLinearMap (f := ((modelTermMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R')).app
      (ModuleCat.of A X)).hom) e.bijective).1 ?_
  have h2 : IsLocalizedModule (S.comap (modelBaseRingMap R A R' R')) (i ∘ₗ gX) :=
    (IsLocalizedModule.comp_iff_of_bijective_left (S := S.comap (modelBaseRingMap R A R' R'))
      i Function.bijective_id).2 inferInstance
  rwa [← hfac] at h2

omit X in
/-- **The map of Stacks 0DJ7 over a flat base change of rings.** If `R'` is flat over `R` and `A'`
is a localization of `A ⊗_R R'`, then for every complex `N` of `A`-modules and every isomorphism
`α : A' ⊗_A N ≅ Z` the map of Stacks 0DJ7 at `(N, Z, α)` is an isomorphism in every degree. -/
theorem isIso_ringBaseChangeCohomologyMap_of_flat [Module.Flat R R'] (S : Submonoid (A ⊗[R] R'))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      IsLocalization S A')
    (N : CochainComplex (ModuleCat.{u} A) ℤ) (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z) [IsIso α] (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
      (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n) := by
  let F := (CochainComplex.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R')
  have hF : F.KFlat := CochainComplex.DerivedTensor.kFlat_single_of_flat _
  rw [isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule (R₀ := R') (𝟙 F) hF n S hloc
    (fun x ↦ ⟨x, rfl⟩), isLocalizedModule_homologyFunctor_map_Q_iff]
  refine CochainComplex.isLocalizedModule_homologyMap _ _ (fun i ↦ ?_) n
  simp only [modelKappa, modelMapX, modelMapE, modelMap, HomologicalComplex.comp_f,
    ModuleCat.hom_comp]
  have hiso : ∀ {X Y : CochainComplex (ModuleCat.{u} (A ⊗[R] R')) ℤ} (φ : X ⟶ Y) [IsIso φ],
      Function.Bijective (φ.f i).hom := fun φ _ ↦ ConcreteCategory.bijective_of_isIso (φ.f i)
  iterate 2 refine (IsLocalizedModule.comp_iff_of_bijective_left _ _ (hiso _)).2 ?_
  refine (IsLocalizedModule.comp_iff_of_bijective_right _ _ (hiso _)).2 ?_
  exact (IsLocalizedModule.comp_iff_of_bijective_right _ _
    (hiso ((tensorSingleIso ((baseChangeFunctor R' (A ⊗[R] R')).obj (ModuleCat.of R' R'))).inv.app
      (((baseChangeFunctor A (A ⊗[R] R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)))).2
    (isLocalizedModule_modelTermMap_self (N.X i) S hloc)

end RingTheory.TorIndependence
