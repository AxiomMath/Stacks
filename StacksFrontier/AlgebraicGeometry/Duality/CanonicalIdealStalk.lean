module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.RingTheory.Dualizing.CanonicalIdealExtension

/-!
# The stalks of the pullback of an ideal onto a dualizing module

Let `B` be a Noetherian domain, `f : X ⟶ Spec B` a dominant morphism from an integral locally
Noetherian scheme, `J ⊆ B` a nonzero ideal and `ω` a dualizing module on `X`. If `f^*J~ ⟶ ω` is
an epimorphism, then at every point `x` the ideal `J · 𝒪_{X,x}` is a dualizing module of the
local ring `𝒪_{X,x}`.

## Main results

* `AlgebraicGeometry.injective_germ_comp_appTop`: for `f` dominant and `X` integral, the ring map
  `B ⟶ 𝒪_{X,x}` is injective.
* `AlgebraicGeometry.surjective_liftBaseChange_toStalk`: `𝒪_{Spec B, y} ⊗_B J ⟶ (J~)_y` is
  surjective.
* `AlgebraicGeometry.exists_surjective_tensor_stalk_of_epi_of_eq_stalkMap`: an epimorphism
  `f^*J~ ⟶ ω` gives a surjection `𝒪_{X,x} ⊗_B J ⟶ ω_x` of `𝒪_{X,x}`-modules, for the algebra
  structure on `𝒪_{X,x}` through the stalk map of `f`.
* `AlgebraicGeometry.isDualizingRingModule_stalk`: the stalk of a dualizing module is a dualizing
  module of the local ring.
* `AlgebraicGeometry.isDualizingRingModule_stalk_of_epi`: `J · 𝒪_{X,x}` is a dualizing module of
  `𝒪_{X,x}`, by `Stacks.Duality.isDualizingRingModule_map_of_surjective`.

## Implementation notes

The ambient derived categories are the standard models (`HasDerivedCategory.standard`, installed
with priority `10000`), as in `StacksFrontier.AlgebraicGeometry.Duality.DualizingModule`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **The ring map `B ⟶ 𝒪_{X,x}` of a dominant morphism from an integral scheme is injective.**
A global function of `Spec B` killed in `𝒪_{X,x}` pulls back to zero on the integral scheme `X`,
so its non-vanishing locus has empty preimage; being open and the image of `f` dense, it is
empty, and `B` is reduced. -/
theorem injective_germ_comp_appTop {B : Type u} [CommRing B] [IsDomain B] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Spec (.of B)) [IsDominant f] (x : X) :
    Function.Injective
      ((Scheme.ΓSpecIso (.of B)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  set s := (Scheme.ΓSpecIso (.of B)).inv.hom b with hs
  have ht : f.appTop s = 0 := by
    apply germ_injective_of_isIntegral X x (U := ⊤) trivial
    rw [map_zero]
    simpa [hs] using hb
  have hbot : (Spec (.of B)).basicOpen s = ⊥ := by
    by_contra hne
    obtain ⟨x', hx'⟩ := f.denseRange.exists_mem_open ((Spec (.of B)).basicOpen s).isOpen
      (Set.nonempty_iff_ne_empty.mpr (SetLike.coe_set_eq.not.mpr hne :
        ((Spec (.of B)).basicOpen s : Set (Spec (.of B))) ≠ (⊥ : (Spec (.of B)).Opens)))
    have : x' ∈ f ⁻¹ᵁ (Spec (.of B)).basicOpen s := hx'
    rwa [Scheme.preimage_basicOpen_top, ht, Scheme.basicOpen_zero] at this
  rw [AlgebraicGeometry.basicOpen_eq_bot_iff] at hbot
  simpa [hs] using congrArg (Scheme.ΓSpecIso (.of B)).hom.hom hbot

/-! ### The stalk of `f^*J~` -/

section PullbackStalk

variable {R : CommRingCat.{u}} (J : ModuleCat.{u} R) (y : Spec R)

/-- The germ map `R ⟶ 𝒪_{Spec R, y}`. -/
abbrev specGerm : R ⟶ (Spec R).presheaf.stalk y :=
  (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ y trivial

/-- The scalar tower `R ⟶ 𝒪_{Spec R, y} ⟶ (J~)_y`. -/
theorem isScalarTower_tildeStalk :
    letI : Algebra R ((Spec R).presheaf.stalk y) := (specGerm y).hom.toAlgebra
    letI := tilde.instModuleCarrierCarrierStalkAbPresheaf J y
    IsScalarTower R ((Spec R).presheaf.stalk y) ((tilde J).presheaf.stalk y) :=
  let : Algebra R ((Spec R).presheaf.stalk y) := (specGerm y).hom.toAlgebra
  let := tilde.instModuleCarrierCarrierStalkAbPresheaf J y
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- **`𝒪_{Spec R, y} ⊗_R J ⟶ (J~)_y` is surjective**: the stalk is the localization of `J` at `y`,
and the denominators are units of `𝒪_{Spec R, y}`. -/
theorem surjective_liftBaseChange_toStalk :
    letI : Algebra R ((Spec R).presheaf.stalk y) := (specGerm y).hom.toAlgebra
    letI := tilde.instModuleCarrierCarrierStalkAbPresheaf J y
    letI := isScalarTower_tildeStalk J y
    Function.Surjective
      ((tilde.toStalk J y).hom.liftBaseChange ((Spec R).presheaf.stalk y)) := by
  let : Algebra R ((Spec R).presheaf.stalk y) := (specGerm y).hom.toAlgebra
  let := tilde.instModuleCarrierCarrierStalkAbPresheaf J y
  let := isScalarTower_tildeStalk J y
  intro m
  let z : PrimeSpectrum.Top R := y
  have hloc : IsLocalizedModule z.asIdeal.primeCompl (tilde.toStalk J z).hom := inferInstance
  obtain ⟨⟨a, s⟩, hs⟩ := hloc.surj m
  have hunit : IsUnit ((specGerm y).hom (s : R)) := by
    have hy : y ∈ (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv.hom (s : R)) := by
      rw [basicOpen_eq_of_affine]
      exact s.2
    exact (Scheme.mem_basicOpen_top _ _ y).mp hy
  obtain ⟨v, hv⟩ := hunit
  refine ⟨(↑v⁻¹ : (Spec R).presheaf.stalk y) ⊗ₜ[R] a, ?_⟩
  rw [LinearMap.liftBaseChange_tmul, ← hs]
  change (↑v⁻¹ : (Spec R).presheaf.stalk y) • ((specGerm y).hom (s : R) • m) = m
  rw [← hv, smul_smul, Units.inv_mul, one_smul]

end PullbackStalk

/-! ### The stalk of a dualizing module -/

/-- **The stalk of a dualizing module is a dualizing module of the local ring**
([Stacks, Tag 0A7G] at the prime of the point). -/
theorem isDualizingRingModule_stalk {X : Scheme.{u}} [IsLocallyNoetherian X] (ω : X.Modules)
    (hω : Stacks.Duality.IsDualizingModule ω) (x : X) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule ω x
    Stacks.Duality.IsDualizingRingModule (X.presheaf.stalk x) (ω.presheaf.stalk x) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule ω x
  obtain ⟨hcoh, k, hk⟩ := hω
  have : ω.IsQuasicoherent := isQuasicoherent_of_isCoherent ω
  have hD := Stacks.Duality.isDualizingComplex_single_stalk ω k hk x
  refine ⟨?_, 0, hD⟩
  have := hD.finiteCohomology 0
  let e : ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        (ModuleCat.of (X.presheaf.stalk x) (ω.presheaf.stalk x)))) ≅
      ModuleCat.of (X.presheaf.stalk x) (ω.presheaf.stalk x) :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} (X.presheaf.stalk x)) 0).app _
  exact Module.Finite.equiv e.toLinearEquiv

/-! ### The surjection onto the stalk of `ω` -/

/-- **An epimorphism `f^*J~ ⟶ ω` gives a surjection `𝒪_{X,x} ⊗_R J ⟶ ω_x`.** The stalk of
`f^*J~` at `x` is `𝒪_{X,x} ⊗_{𝒪_{Spec R, f x}} (J~)_{f x}` ([Stacks, Tag 0098]), onto which
`𝒪_{X,x} ⊗_R J` maps surjectively, and an epimorphism of sheaves of modules is surjective on
stalks. The ring map `φ : R ⟶ 𝒪_{X,x}` is any map equal to the composite through
`𝒪_{Spec R, f x}`. -/
theorem exists_surjective_tensor_stalk_of_epi_of_eq_stalkMap {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (J : ModuleCat.{u} R) (ω : X.Modules)
    (π : (Scheme.Modules.pullback f).obj ((tilde.functor R).obj J) ⟶ ω) [Epi π] (x : X)
    (φ : R →+* X.presheaf.stalk x) (hφ : φ = (f.stalkMap x).hom.comp (specGerm (f x)).hom) :
    letI : Algebra R (X.presheaf.stalk x) := φ.toAlgebra
    letI := Stacks.ModuleStalkSpecialization.stalkModule ω x
    ∃ g : X.presheaf.stalk x ⊗[R] J →ₗ[X.presheaf.stalk x] ω.presheaf.stalk x,
      Function.Surjective g := by
  subst hφ
  let := Stacks.ModuleStalkSpecialization.stalkModule ω x
  let : Algebra R ((Spec R).presheaf.stalk (f x)) := (specGerm (f x)).hom.toAlgebra
  let : Algebra ((Spec R).presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra R (X.presheaf.stalk x) :=
    ((f.stalkMap x).hom.comp (specGerm (f x)).hom).toAlgebra
  have : IsScalarTower R ((Spec R).presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := tilde.instModuleCarrierCarrierStalkAbPresheaf J (f x)
  have := isScalarTower_tildeStalk J (f x)
  let v := (tilde.toStalk J (f x)).hom.liftBaseChange ((Spec R).presheaf.stalk (f x))
  let e₀ := TensorProduct.AlgebraTensorModule.cancelBaseChange R
    ((Spec R).presheaf.stalk (f x)) (X.presheaf.stalk x) (X.presheaf.stalk x) J
  let v' := v.baseChange (X.presheaf.stalk x)
  have hv' : Function.Surjective v' := by
    change Function.Surjective (v.baseChange (X.presheaf.stalk x) :
      _ → X.presheaf.stalk x ⊗[(Spec R).presheaf.stalk (f x)] _)
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective _ (surjective_liftBaseChange_toStalk J (f x))
  let e₁ : X.presheaf.stalk x ⊗[(Spec R).presheaf.stalk (f x)] (tilde J).presheaf.stalk (f x)
      ≃ₗ[X.presheaf.stalk x]
      ((Scheme.Modules.pullback f).obj ((tilde.functor R).obj J)).presheaf.stalk x :=
    Stacks.ModuleSkyscraper.pullbackStalkLinearEquiv f x ((tilde.functor R).obj J)
  let p : ((Scheme.Modules.pullback f).obj ((tilde.functor R).obj J)).presheaf.stalk x
      →ₗ[X.presheaf.stalk x] ω.presheaf.stalk x :=
    Stacks.ModuleSkyscraper.stalkMapLinear (R := X.presheaf) π.val x
  have hp : Function.Surjective p :=
    (Stacks.SheafOfModules.StalkEpiMono.epi_iff_stalk_surjective π).mp ‹Epi π› x
  exact ⟨p ∘ₗ e₁.toLinearMap ∘ₗ v' ∘ₗ e₀.symm.toLinearMap,
    hp.comp (e₁.surjective.comp (hv'.comp e₀.symm.surjective))⟩

/-! ### The extended ideal is dualizing at every stalk -/

/-- **An ideal mapping onto a dualizing module is dualizing at every stalk.** Let `B` be a
Noetherian domain, `f : X ⟶ Spec B` a dominant morphism from an integral locally Noetherian
scheme, `J ≠ 0` an ideal of `B` and `ω` a dualizing module on `X` receiving an epimorphism
`f^*J~ ⟶ ω`. Then at every point `x` the extended ideal `J · 𝒪_{X,x}` is a dualizing module of
`𝒪_{X,x}`. -/
theorem isDualizingRingModule_stalk_of_epi {B : Type u} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of B)) [IsDominant f] (J : Ideal B) (hJ : J ≠ ⊥) (ω : X.Modules)
    (hω : Stacks.Duality.IsDualizingModule ω)
    (π : (Scheme.Modules.pullback f).obj ((tilde.functor (.of B)).obj (ModuleCat.of B J)) ⟶ ω)
    [Epi π] (x : X) :
    ∃ _ : IsNoetherianRing (X.presheaf.stalk x),
      Stacks.Duality.IsDualizingRingModule (X.presheaf.stalk x)
        (J.map ((Scheme.ΓSpecIso (.of B)).inv ≫ f.appTop ≫
          X.presheaf.germ ⊤ x trivial).hom) := by
  refine ⟨inferInstance, ?_⟩
  set ψ := (Scheme.ΓSpecIso (.of B)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial with hψdef
  let : Algebra B (X.presheaf.stalk x) := ψ.hom.toAlgebra
  let := Stacks.ModuleStalkSpecialization.stalkModule ω x
  have hψ : ψ.hom = (f.stalkMap x).hom.comp (specGerm (f x)).hom := by
    rw [← CommRingCat.hom_comp]
    congr 1
    rw [hψdef, specGerm, Category.assoc]
    congr 1
    exact (Scheme.Hom.germ_stalkMap f ⊤ x trivial).symm
  obtain ⟨g, hg⟩ :=
    exists_surjective_tensor_stalk_of_epi_of_eq_stalkMap f (ModuleCat.of B J) ω π x ψ.hom hψ
  exact Stacks.Duality.isDualizingRingModule_map_of_surjective
    (injective_germ_comp_appTop f x) J hJ (ω.presheaf.stalk x)
    (isDualizingRingModule_stalk ω hω x) g hg

end AlgebraicGeometry
