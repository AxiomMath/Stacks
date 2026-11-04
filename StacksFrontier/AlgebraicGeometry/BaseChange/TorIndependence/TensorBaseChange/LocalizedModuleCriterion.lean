module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.ModelHomology
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.RingCriterion

/-!
# The map of Stacks 0DJ7 at a localization, through the model

When `A'` is a localization of `A ⊗_R R'`, the map of Stacks 0DJ7 in degree `n` is an
isomorphism exactly when `H^n(K ⊗^L_R R') ⟶ H^n(K')` is a localization of modules at the same
submonoid.  Through the model complex this becomes a statement about the cohomology of an
explicit complex of `A ⊗_R R₀`-modules.

## Main results

* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open CochainComplex.DerivedExtensionScalars

universe u

section Surjective

variable {B₀ B : Type u} [CommRing B₀] [CommRing B] (σ : B₀ →+* B)
  (hσ : Function.Surjective σ) (S : Submonoid B)

include hσ in
/-- Along a surjective ring map, a localization of modules is detected after restriction of
scalars, at the preimage of the submonoid. -/
private theorem ModuleCat.isLocalizedModule_restrictScalars_iff {M N : ModuleCat.{u} B}
    (f : M ⟶ N) :
    IsLocalizedModule (S.comap σ) ((ModuleCat.restrictScalars σ).map f).hom ↔
      IsLocalizedModule S f.hom := by
  have hunit : ∀ (s₀ : B₀) (s : B), σ s₀ = s →
      (IsUnit (algebraMap B₀ (Module.End B₀ ((ModuleCat.restrictScalars σ).obj N)) s₀) ↔
        IsUnit (algebraMap B (Module.End B N) s)) := by
    rintro s₀ _ rfl
    rw [Module.End.isUnit_iff, Module.End.isUnit_iff]
    rfl
  have hlift : ∀ s : S, ∃ s₀ : S.comap σ, σ s₀ = s := fun s => by
    obtain ⟨s₀, hs₀⟩ := hσ s
    exact ⟨⟨s₀, by simp [hs₀]⟩, hs₀⟩
  rw [isLocalizedModule_iff, isLocalizedModule_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
    · obtain ⟨s₀, hs₀⟩ := hlift s
      exact (hunit s₀ s hs₀).1 (h1 s₀)
    · obtain ⟨⟨x, s₀⟩, h⟩ := h2 y
      exact ⟨⟨x, ⟨σ s₀, s₀.2⟩⟩, h⟩
    · obtain ⟨c₀, hc⟩ := h3 hx
      exact ⟨⟨σ c₀, c₀.2⟩, hc⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun s₀ => (hunit s₀ (σ s₀) rfl).2 (h1 ⟨σ s₀, s₀.2⟩), fun y => ?_,
      fun {x₁ x₂} hx => ?_⟩
    · obtain ⟨⟨x, s⟩, h⟩ := h2 y
      obtain ⟨s₀, hs₀⟩ := hlift s
      refine ⟨⟨x, s₀⟩, ?_⟩
      show σ s₀ • y = f.hom x
      rwa [hs₀]
    · obtain ⟨c, hc⟩ := h3 hx
      obtain ⟨c₀, hc₀⟩ := hlift c
      refine ⟨c₀, ?_⟩
      show σ c₀ • x₁ = σ c₀ • x₂
      rwa [hc₀]

end Surjective

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

section Naturality

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- The cohomology comparison is natural in the target of `φ`. -/
theorem cohomologyComparisonMap_comp (K : DerivedCategory (ModuleCat.{u} A))
    {K₁ K₂ : DerivedCategory (ModuleCat.{u} A')}
    (φ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K ⟶ K₁)
    (χ : K₁ ⟶ K₂) (n : ℤ) :
    cohomologyComparisonMap (R := R) (R' := R') K K₂ (φ ≫ χ) n =
      cohomologyComparisonMap (R := R) (R' := R') K K₁ φ n ≫
        (ModuleCat.restrictScalars (algebraMap R' A')).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map χ) := by
  dsimp only [cohomologyComparisonMap]
  have h := ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso
    n).hom.naturality χ
  dsimp only [Functor.comp_map] at h
  simp only [Functor.map_comp, Category.assoc]
  rw [h]

end Naturality

end RingTheory.TorIndependence

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard Algebra.TensorProduct.rightAlgebra

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

local notation "B₀" => A ⊗[R] R₀

variable {F : CochainComplex (ModuleCat.{u} R₀) ℤ}
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))
  [Module.Flat R R₀] (hF : F.KFlat) [QuasiIso ε] (n : ℤ)

/-- The model map composed with a map of complexes of `A'`-modules. -/
abbrev modelKappa (N : CochainComplex (ModuleCat.{u} A) ℤ) (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z) :
    modelComplex A F N ⟶
      ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z :=
  modelMapX (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N ≫
    ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map α

/-- The identification of the cohomology of the target of the model map. -/
abbrev modelTargetIso (Z : CochainComplex (ModuleCat.{u} A') ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).obj
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Z)) ≅
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj (DerivedCategory.Q.obj Z)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).mapIso
      (((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategoryFactors.app
        Z).symm) ≪≫
    ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategoryHomologyIso n).app
      (DerivedCategory.Q.obj Z)

/-- **The key identity of the model**, on elements: the comparison of Stacks 065Z followed by
`α`, read through the model, is the cohomology of the model map. -/
theorem modelKappa_homology_apply (N : CochainComplex (ModuleCat.{u} A) ℤ)
    (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z)
    (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).obj
      (DerivedCategory.Q.obj (modelComplex A F N))) :
    (modelTargetIso n Z).hom.hom (((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
        (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
          ε N Z α))).hom y) =
      (cohomologyComparisonMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
        (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n).hom
        ((modelHomologyIso (R := R) ε hF n N).hom.hom y) := by
  have hc := congrArg (fun f => f.hom y)
    (modelHomology_comparison (R := R) (A := A) (R' := R') (A' := A') ε hF n N)
  rw [cohomologyComparisonMap_comp]
  show _ = ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map
    (DerivedCategory.Q.map α)).hom ((cohomologyComparisonMap (R := R) (R' := R')
      (DerivedCategory.Q.obj N) _ (alphaH A A' N) n).hom
        ((modelHomologyIso (R := R) ε hF n N).hom.hom y))
  have hc' : (cohomologyComparisonMap (R := R) (R' := R')
      (DerivedCategory.Q.obj N) _ (alphaH A A' N) n).hom
        ((modelHomologyIso (R := R) ε hF n N).hom.hom y) =
      (((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategoryHomologyIso
        n).hom.app (DerivedCategory.Q.obj (((ModuleCat.extendScalars
          (algebraMap A A')).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
          (modelDerivedMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N)).hom y) := hc
  rw [hc']
  have key : (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
        (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
          ε N Z α)) ≫ (modelTargetIso n Z).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
          (modelDerivedMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N) ≫
        ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategoryHomologyIso
          n).hom.app (DerivedCategory.Q.obj (((ModuleCat.extendScalars
            (algebraMap A A')).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) ≫
        (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map
            (DerivedCategory.Q.map α)) := by
    have n1 :=
      ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategoryHomologyIso
        n).hom.naturality (DerivedCategory.Q.map α)
    have n2 := ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapDerivedCategoryFactors
      ).inv.naturality α
    dsimp only [Functor.comp_map] at n1 n2
    dsimp only [modelTargetIso, modelKappa, modelDerivedMap, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Iso.app_inv, Iso.app_hom]
    have n2' := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map n2
    simp only [Functor.map_comp] at n2'
    simp only [Functor.map_comp, Category.assoc]
    rw [← n1, reassoc_of% n2']
  exact congrArg (fun f => f.hom y) key

include hF in
/-- **The criterion of the model.** The base-change map of Stacks 0DJ7 at
`(Q N, Q Z, α)` is invertible in degree `n` exactly when the cohomology of the model map is a
localization at the preimage of `S`, where `A'` is the localization of `A ⊗_R R'` at `S`. -/
theorem isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule
    (S : Submonoid (A ⊗[R] R'))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      IsLocalization S A')
    (hsurj : Function.Surjective (algebraMap R₀ R'))
    (N : CochainComplex (ModuleCat.{u} A) ℤ) (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
        (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n) ↔
      IsLocalizedModule (S.comap (modelBaseRingMap R A R' R₀))
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B₀) n).map
          (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀)
            ε N Z α))).hom := by
  let := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
  have : IsScalarTower (A ⊗[R] R') A'
      ((ModuleCat.restrictScalars (baseChangeTensorRingMap (R := R) (A := A) (R' := R')
        (A' := A'))).obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj
          (DerivedCategory.Q.obj Z))) :=
    ⟨fun b a x => mul_smul (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') b) a x⟩
  have hρ : Function.Surjective (modelBaseRingMap R A R' R₀) :=
    TensorProduct.map_surjective Function.surjective_id hsurj
  rw [isIso_ringBaseChangeCohomologyMap_iff_isBaseChange, ← isLocalizedModule_iff_isBaseChange S,
    ← ModuleCat.isLocalizedModule_restrictScalars_iff _ hρ]
  let E := modelHomologyLinearEquiv (R := R) (A := A) (R' := R') ε hF n N
  let H' := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj (DerivedCategory.Q.obj Z)
  let T' : (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).obj H' →ₗ[B₀]
      (ModuleCat.restrictScalars (modelBaseRingMap R A R' R₀)).obj
        ((ModuleCat.restrictScalars (baseChangeTensorRingMap (R := R) (A := A) (R' := R')
          (A' := A'))).obj H') :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT' : Function.Bijective (T'.comp (modelTargetIso n Z).toLinearEquiv.toLinearMap) :=
    Function.bijective_id.comp (modelTargetIso n Z).toLinearEquiv.bijective
  refine (IsLocalizedModule.comp_iff_of_bijective_right _ E.toLinearMap E.bijective).symm.trans
    (Iff.trans ?_ (IsLocalizedModule.comp_iff_of_bijective_left _ _ hT'))
  apply iff_of_eq
  congr 1
  refine LinearMap.ext fun y => ?_
  exact (modelKappa_homology_apply (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε hF n
    N Z α y).symm

end RingTheory.TorIndependence
