module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.StalkComplexCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.ModulesStalkTensor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseModelChange
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The stalk of an associated complex as a base change

For a complex `M` of `R`-modules and a point `y` of `Spec R`, the germs at `y` of the global
sections `M^p ⟶ Γ(M̃^p) ⟶ (M̃^p)_y` form a map of complexes which is a localization at the prime of
`y` in every degree; hence the stalk complex of `M̃` at `y` is `𝒪_{Spec R, y} ⊗_R M`.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChange.tildeStalkMap`: the germs at `y` of the global sections of
  `M̃`, as a map of complexes over `R ⟶ 𝒪_{Spec R, y}`.
* `RingTheory.TorIndependence.baseChangeComplexIsoOfIsLocalizedModule`: a map of complexes over a
  localization `A ⟶ A₁` which is a localization in every degree, as an isomorphism
  `A₁ ⊗_A M ≅ M₁`.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.isLocalizedModule_tildeStalkMap`: `tildeStalkMap M y` is a
  localization at the complement of the prime `y` in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

variable {A A₁ : Type u} [CommRing A] [CommRing A₁] [Algebra A A₁] (S : Submonoid A)
  [IsLocalization S A₁]

/-- A localization `X ⟶ X₁` over a localization `A ⟶ A₁`, as an identification
`A₁ ⊗_A X ≅ X₁`. -/
def baseChangeEquivOfIsLocalizedModule {X : ModuleCat.{u} A} {X₁ : ModuleCat.{u} A₁}
    (μ : X ⟶ (ModuleCat.restrictScalars (algebraMap A A₁)).obj X₁)
    (hμ : IsLocalizedModule S μ.hom) : A₁ ⊗[A] X ≃ₗ[A₁] X₁ :=
  letI : Module A X₁ := Module.compHom X₁ (algebraMap A A₁)
  haveI : IsScalarTower A A₁ X₁ := ⟨fun a b x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  ((isLocalizedModule_iff_isBaseChange S A₁ (show X →ₗ[A] X₁ from μ.hom)).1 hμ).equiv

/-- The identification `A₁ ⊗_A X ≅ X₁` sends `b ⊗ x` to `b • μ x`. -/
theorem baseChangeEquivOfIsLocalizedModule_tmul {X : ModuleCat.{u} A} {X₁ : ModuleCat.{u} A₁}
    (μ : X ⟶ (ModuleCat.restrictScalars (algebraMap A A₁)).obj X₁)
    (hμ : IsLocalizedModule S μ.hom) (b : A₁) (x : X) :
    baseChangeEquivOfIsLocalizedModule S μ hμ (b ⊗ₜ[A] x) = b • (show X₁ from μ.hom x) := by
  let : Module A X₁ := Module.compHom X₁ (algebraMap A A₁)
  have : IsScalarTower A A₁ X₁ := ⟨fun a b x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  exact IsBaseChange.equiv_tmul _ b x

/-- A map of complexes `M ⟶ M₁` over a localization `A ⟶ A₁` which is a localization in every
degree gives `A₁ ⊗_A M ≅ M₁`. -/
def baseChangeComplexIsoOfIsLocalizedModule {M : CochainComplex (ModuleCat.{u} A) ℤ}
    {M₁ : CochainComplex (ModuleCat.{u} A₁) ℤ}
    (μ : M ⟶ ((ModuleCat.restrictScalars (algebraMap A A₁)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M₁)
    (hμ : ∀ p, IsLocalizedModule S (μ.f p).hom) :
    ((baseChangeFunctor A A₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ≅ M₁ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (baseChangeEquivOfIsLocalizedModule S (μ.f p) (hμ p)).toModuleIso)
    fun p q _ => by
      apply baseChangeFunctor_hom_ext
      intro b x
      change (M₁.d p q).hom (baseChangeEquivOfIsLocalizedModule S (μ.f p) (hμ p) (b ⊗ₜ[A] x)) =
        baseChangeEquivOfIsLocalizedModule S (μ.f q) (hμ q) (b ⊗ₜ[A] (M.d p q).hom x)
      rw [baseChangeEquivOfIsLocalizedModule_tmul, baseChangeEquivOfIsLocalizedModule_tmul,
        map_smul]
      congr 1
      exact congrArg (fun φ => φ.hom x) (μ.comm p q)

/-- In each degree `p`, the identification `A₁ ⊗_A M ≅ M₁` sends `1 ⊗ x` to `μ x`. -/
theorem baseChangeComplexIsoOfIsLocalizedModule_hom_f_tmul
    {M : CochainComplex (ModuleCat.{u} A) ℤ} {M₁ : CochainComplex (ModuleCat.{u} A₁) ℤ}
    (μ : M ⟶ ((ModuleCat.restrictScalars (algebraMap A A₁)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M₁)
    (hμ : ∀ p, IsLocalizedModule S (μ.f p).hom) (p : ℤ) (x : M.X p) :
    ((baseChangeComplexIsoOfIsLocalizedModule S μ hμ).hom.f p).hom ((1 : A₁) ⊗ₜ[A] x) =
      (μ.f p).hom x :=
  (baseChangeEquivOfIsLocalizedModule_tmul S (μ.f p) (hμ p) 1 x).trans (one_smul _ _)

end RingTheory.TorIndependence

namespace Stacks.Cohomology.DerivedBaseChange

variable {R : CommRingCat.{u}}

/-- The stalk functor at a point `y` of `Spec R` on sheaves of modules is additive. -/
instance (y : PrimeSpectrum R) :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec R) y).Additive :=
  AlgebraicGeometry.modulesStalkFunctor_additive (X := Spec R) y

/-- The germs at `y` of the global sections of `M̃`, as a map of complexes over the germ map
`R ⟶ 𝒪_{Spec R, y}`. -/
def tildeStalkMap (M : CochainComplex (ModuleCat.{u} R) ℤ) (y : PrimeSpectrum R) :
    M ⟶ ((ModuleCat.restrictScalars (StructureSheaf.toStalk R y).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (((Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec R)
        y).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) where
  f p := ModuleCat.ofHom (X := M.X p)
      (Y := (ModuleCat.restrictScalars (StructureSheaf.toStalk R y).hom).obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec R) y).obj
          (tilde (M.X p))))
    { toFun := fun m => (tilde.toStalk (M.X p) y).hom m
      map_add' := (tilde.toStalk (M.X p) y).hom.map_add
      map_smul' := (tilde.toStalk (M.X p) y).hom.map_smul }
  comm' p q _ := by
    ext m
    change ((Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec R) y).map (tilde.map (M.d p q))).hom
        ((tilde.toStalk (M.X p) y).hom m) = (tilde.toStalk (M.X q) y).hom ((M.d p q).hom m)
    exact (Stacks.ModuleSkyscraper.stalkMapLinear_germ
      ((SheafOfModules.forget _).map (tilde.map (M.d p q))) y ⊤ trivial
        ((tilde.toOpen (M.X p) ⊤).hom m)).trans
      (congrArg (fun φ => (tilde (M.X q)).presheaf.germ ⊤ y trivial (φ.hom m))
        (tilde.toOpen_map_app (M.d p q) ⊤))

/-- In degree `p`, `tildeStalkMap M y` sends `m` to its germ at `y` in the stalk of `M̃^p`. -/
theorem tildeStalkMap_f_apply (M : CochainComplex (ModuleCat.{u} R) ℤ) (y : PrimeSpectrum R)
    (p : ℤ) (m : M.X p) :
    ((tildeStalkMap M y).f p).hom m = (tilde.toStalk (M.X p) y).hom m :=
  rfl

/-- In every degree, `tildeStalkMap M y` is a localization at the complement of the prime `y`. -/
theorem isLocalizedModule_tildeStalkMap (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (y : PrimeSpectrum R) (p : ℤ) :
    IsLocalizedModule y.asIdeal.primeCompl ((tildeStalkMap M y).f p).hom := by
  exact IsLocalizedModule.of_linearEquiv y.asIdeal.primeCompl (tilde.toStalk (M.X p) y).hom
    (LinearEquiv.refl R ((tilde (M.X p)).presheaf.stalk y))

end Stacks.Cohomology.DerivedBaseChange

