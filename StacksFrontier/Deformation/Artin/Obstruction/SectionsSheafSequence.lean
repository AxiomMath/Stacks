module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightScalar
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightUnit
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Sections
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsLift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.CategoryTheory.Sites.Stack.PresheafElementsStack
public import StacksFrontier.Deformation.Artin.Obstruction.Theory
public import StacksFrontier.Topology.Sheaves.Modules.Flat.PullbackTensorExact

/-!
# The sheaf-level sequence and the obstruction functor of Stacks 07YH

Let `R` be a ring, `π : X → Spec R` a morphism of schemes and `𝓕` an `𝒪_X`-module flat over
`Spec R`. For an `R`-module `M` write `𝓕 ⊗_R M` for the `𝒪_X`-module `π^*M̃ ⊗_{𝒪_X} 𝓕`. This file
shows that `M ↦ 𝓕 ⊗_R M` is exact, defines the obstruction module functor
`𝒪(M) = H¹(X, 𝓕 ⊗_R M)` on `R`-modules and the obstruction element of a global section of
`𝓕 ⊗_R M₃` attached to a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, and proves that this
element vanishes exactly when the section lifts to `𝓕 ⊗_R M₂`, that it is natural in the
sequence, and that `𝒪` is `R`-linear.

## Main definitions

* `Deformation.Artin.SectionsSheaf.pullbackTensor` — the functor `G ↦ π^*G ⊗_{𝒪_X} 𝓕` of
  [Stacks, Tag 0GMU], with `(Spec R).Modules` as its domain.
* `Deformation.Artin.SectionsSheaf.tensorSheafFunctor` — the functor `M ↦ 𝓕 ⊗_R M` from
  `R`-modules to `𝒪_X`-modules, and `Deformation.Artin.SectionsSheaf.tensorSheafFunctorObjSelf`
  the identification of its value at `R` with `𝓕`.
* `Deformation.Artin.SectionsSheaf.sectionsOverBase` — `R`-linear global sections
  `H⁰(X, -)`, and `Deformation.Artin.SectionsSheaf.cohomologyDeltaFunctor` the cohomology
  δ-functor `Hⁿ(X, -)` it generates.
* `Deformation.Artin.SectionsSheaf.obstructionFunctor` — the obstruction module functor
  `𝒪(M) = H¹(X, 𝓕 ⊗_R M)`, and `Deformation.Artin.SectionsSheaf.obstructionLinearEndofunctor`
  the same as a `Deformation.Artin.LinearEndofunctor`.
* `Deformation.Artin.SectionsSheaf.boundary` — the boundary map
  `H⁰(X, 𝓕 ⊗_R M₃) → H¹(X, 𝓕 ⊗_R M₁)`, and `Deformation.Artin.SectionsSheaf.obstructionClass`
  the obstruction element it assigns to a section.
* `Deformation.Artin.SectionsSheaf.zeroIsoSections` — the identification of the degree-zero
  term `H⁰(X, -)` of the cohomology δ-functor with global sections.

## Main results

* `Deformation.Artin.SectionsSheaf.tensorSheafFunctor_shortExact` — `M ↦ 𝓕 ⊗_R M` carries a
  short exact sequence of `R`-modules to a short exact sequence of `𝒪_X`-modules.
* `Deformation.Artin.SectionsSheaf.obstructionClass_eq_zero_iff` and
  `Deformation.Artin.SectionsSheaf.exists_section_iff_obstructionClass_eq_zero` — the
  obstruction class of a section vanishes if and only if the section lifts, for the degree-zero
  term of the δ-functor and for global sections.
* `Deformation.Artin.SectionsSheaf.boundary_naturality` and
  `Deformation.Artin.SectionsSheaf.obstructionClass_naturality` — a morphism of short exact
  sequences of `R`-modules carries the obstruction class of a section to the obstruction class
  of its image.
* `Deformation.Artin.SectionsSheaf.linear_obstructionFunctor` — the obstruction module functor
  is `R`-linear.
* `Deformation.Artin.SectionsSheaf.hasLift_iff_exists_section` — an object of the category of
  elements of a presheaf on the big fppf site lifts across a deformation situation, in the sense
  of `Deformation.Artin.AffineObject.HasLift`, exactly when the section it names is the
  restriction of a section over the thickening.
* `Deformation.Artin.SectionsSheaf.exists_preimage_iff_δ_eq_zero` — for a cohomological
  δ-functor with module values and a short exact sequence, an element of `F⁰(X₃)` lifts to
  `F⁰(X₂)` if and only if its image in `F¹(X₁)` vanishes.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace Deformation.Artin.SectionsSheaf

/-! ### The lifting criterion for a δ-functor -/

/-- **The lifting criterion for a cohomological δ-functor with module values.** For a short
exact sequence `0 → X₁ → X₂ → X₃ → 0` and an element `s` of `F⁰(X₃)`, the element `s` is the
image of an element of `F⁰(X₂)` if and only if its connecting image in `F¹(X₁)` vanishes. -/
theorem exists_preimage_iff_δ_eq_zero {A : Type v} [Category.{u} A] [Preadditive A]
    {Λ : Type u} [Ring Λ]
    (Φ : DeltaFunctor A (ModuleCat.{u} Λ)) {S : ShortComplex A} (hS : S.ShortExact)
    (s : ((Φ.functor 0).obj S.X₃ : Type u)) :
    (∃ t : ((Φ.functor 0).obj S.X₂ : Type u), ((Φ.functor 0).map S.g) t = s) ↔
      (Φ.δ hS 0) s = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    have h2 : ((Φ.functor 0).map S.g ≫ Φ.δ hS 0) t = 0 := by
      rw [Φ.map_g_δ hS 0]; simp
    simpa only [CategoryTheory.comp_apply] using h2
  · intro h
    exact ((ShortComplex.moduleCat_exact_iff _).1 (Φ.scδ₁_exact hS 0)) s h

/-! ### The sheaf-level short exact sequence -/

section Base

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
  (F : SheafOfModules.{u} X.ringCatSheaf)

/-- The functor `G ↦ π^*G ⊗_{𝒪_X} 𝓕` of [Stacks, Tag 0GMU], from `𝒪_{Spec R}`-modules to
`𝒪_X`-modules, stated with `(Spec R).Modules` as its domain. -/
def pullbackTensor : (Spec R).Modules ⥤ SheafOfModules.{u} X.ringCatSheaf :=
  Stacks.SheafOfModules.pullbackTensorFunctor π.toLRSHom.toShHom F

/-- The functor `G ↦ π^*G ⊗_{𝒪_X} 𝓕` is additive. -/
instance additive_pullbackTensor : (pullbackTensor π F).Additive :=
  Stacks.SheafOfModules.additive_pullbackTensorFunctor π.toLRSHom.toShHom F

/-- `G ↦ π^*G ⊗_{𝒪_X} 𝓕` preserves finite limits when `𝓕` is flat over `Spec R`; this is the
left-exact half of [Stacks, Tag 0GMU]. -/
theorem preservesFiniteLimits_pullbackTensor
    (hF : AlgebraicGeometry.IsFlatOver π.toLRSHom.toShHom F) :
    PreservesFiniteLimits (pullbackTensor π F) :=
  ((exactFunctor_iff _).mp
    (Stacks.SheafOfModules.pullbackTensorFunctor_exact π.toLRSHom.toShHom F hF)).1

/-- `G ↦ π^*G ⊗_{𝒪_X} 𝓕` preserves finite colimits; this is the right-exact half of
[Stacks, Tag 0GMU]. -/
theorem preservesFiniteColimits_pullbackTensor
    (hF : AlgebraicGeometry.IsFlatOver π.toLRSHom.toShHom F) :
    PreservesFiniteColimits (pullbackTensor π F) :=
  ((exactFunctor_iff _).mp
    (Stacks.SheafOfModules.pullbackTensorFunctor_exact π.toLRSHom.toShHom F hF)).2

/-- **The functor `M ↦ 𝓕 ⊗_R M`** from `R`-modules to `𝒪_X`-modules: pull the quasi-coherent
module `M̃` back to `X` and tensor it with `𝓕`. -/
def tensorSheafFunctor : ModuleCat.{u} R ⥤ SheafOfModules.{u} X.ringCatSheaf :=
  AlgebraicGeometry.tilde.functor R ⋙ pullbackTensor π F

/-- The functor `M ↦ 𝓕 ⊗_R M` is additive. -/
instance additive_tensorSheafFunctor : (tensorSheafFunctor π F).Additive := by
  unfold tensorSheafFunctor; infer_instance

/-- The functor `M ↦ 𝓕 ⊗_R M` takes the base ring `R` to `𝓕`. -/
def tensorSheafFunctorObjSelf : (tensorSheafFunctor π F).obj (ModuleCat.of R R) ≅ F := by
  let pullbackUnitIso :=
    RingedSpaceModuleAdjunction.modulePullbackObjUnitIso π.toLRSHom.toShHom
  let factorIso := pullbackUnitIso.prod (Iso.refl F)
  let tensorUnitIso := (Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).mapIso factorIso
  exact tensorUnitIso ≪≫ Stacks.unitSheafTensorIso F

/-- `M ↦ 𝓕 ⊗_R M` preserves finite limits when `𝓕` is flat over `Spec R`. -/
theorem preservesFiniteLimits_tensorSheafFunctor
    (hF : AlgebraicGeometry.IsFlatOver π.toLRSHom.toShHom F) :
    PreservesFiniteLimits (tensorSheafFunctor π F) :=
  have := preservesFiniteLimits_pullbackTensor π F hF
  inferInstanceAs
    (PreservesFiniteLimits (AlgebraicGeometry.tilde.functor R ⋙ pullbackTensor π F))

/-- `M ↦ 𝓕 ⊗_R M` preserves finite colimits. -/
theorem preservesFiniteColimits_tensorSheafFunctor
    (hF : AlgebraicGeometry.IsFlatOver π.toLRSHom.toShHom F) :
    PreservesFiniteColimits (tensorSheafFunctor π F) :=
  have := preservesFiniteColimits_pullbackTensor π F hF
  inferInstanceAs
    (PreservesFiniteColimits (AlgebraicGeometry.tilde.functor R ⋙ pullbackTensor π F))

/-- When `𝓕` is flat over `Spec R`, a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of
`R`-modules is carried by `M ↦ 𝓕 ⊗_R M` to a short exact sequence
```
0 → 𝓕 ⊗_R M₁ → 𝓕 ⊗_R M₂ → 𝓕 ⊗_R M₃ → 0
```
of `𝒪_X`-modules. -/
theorem tensorSheafFunctor_shortExact
    (hF : AlgebraicGeometry.IsFlatOver π.toLRSHom.toShHom F)
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    (S.map (tensorSheafFunctor π F)).ShortExact :=
  have := preservesFiniteLimits_tensorSheafFunctor π F hF
  have := preservesFiniteColimits_tensorSheafFunctor π F hF
  hS.map_of_exact _

/-! ### The obstruction module functor -/

section Cohomology

attribute [local instance] HasDerivedCategory.standard

/-- **`R`-linear global sections `H⁰(X, -)`.** Global sections of an `𝒪_X`-module, regarded as
an `R`-module by restriction of scalars along `R ≅ Γ(Spec R, 𝒪) → Γ(X, 𝒪_X)`. -/
def sectionsOverBase : SheafOfModules.{u} X.ringCatSheaf ⥤ ModuleCat.{u} R :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars (((Scheme.ΓSpecIso R).inv ≫ π.appTop).hom)

/-- `R`-linear global sections form an additive functor. -/
instance additive_sectionsOverBase : (sectionsOverBase π).Additive where
  map_add := rfl

/-- `R`-linear global sections preserve finite limits. -/
instance preservesFiniteLimits_sectionsOverBase :
    PreservesFiniteLimits (sectionsOverBase π) := by
  have h : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{u} (((Scheme.ΓSpecIso R).inv ≫ π.appTop).hom)) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  exact @comp_preservesFiniteLimits _ _ _ _ _ _
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
    (ModuleCat.restrictScalars.{u} (((Scheme.ΓSpecIso R).inv ≫ π.appTop).hom)) inferInstance h

/-- **The cohomology δ-functor `Hⁿ(X, -)` with `R`-linear values**: the right derived
δ-functor of `R`-linear global sections. -/
def cohomologyDeltaFunctor :
    DeltaFunctor (SheafOfModules.{u} X.ringCatSheaf) (ModuleCat.{u} R) :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (sectionsOverBase π)

/-- The degree-`n` part of the cohomology δ-functor is the `n`-th right derived functor of
`R`-linear global sections. -/
theorem cohomologyDeltaFunctor_functor (n : ℕ) :
    (cohomologyDeltaFunctor π).functor n = (sectionsOverBase π).rightDerived n :=
  rfl

/-- **The obstruction module functor** `𝒪(M) = H¹(X, 𝓕 ⊗_R M)`, an endofunctor of the
category of `R`-modules. -/
def obstructionFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  tensorSheafFunctor π F ⋙ (cohomologyDeltaFunctor π).functor 1

/-- The obstruction module functor is additive. -/
instance additive_obstructionFunctor : (obstructionFunctor π F).Additive := by
  unfold obstructionFunctor; infer_instance

/-- The obstruction module functor evaluated at `M` is `H¹(X, 𝓕 ⊗_R M)`. -/
theorem obstructionFunctor_obj (M : ModuleCat.{u} R) :
    (obstructionFunctor π F).obj M =
      ((cohomologyDeltaFunctor π).functor 1).obj ((tensorSheafFunctor π F).obj M) :=
  rfl

/-! ### The obstruction module functor is `R`-linear -/

/-- The ring map `R ≅ Γ(Spec R, 𝒪) → Γ(X, 𝒪_X)`. -/
abbrev baseHom : ↑R →+* ↑Γ(X, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ π.appTop).hom

/-- **Multiplication by the image of a scalar `r : R`**, as an endomorphism of the identity
functor of the category of `𝒪_X`-modules. -/
abbrev baseScalarEnd (r : ↑R) : End (𝟭 (SheafOfModules.{u} X.ringCatSheaf)) :=
  Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf ⊤ Limits.isTerminalTop (baseHom π r)

/-- Multiplication by `r` is the scalar action of `r` on the identity morphism. -/
theorem baseScalarEnd_app_eq_smul_id (r : ↑R) (N : SheafOfModules.{u} X.ringCatSheaf) :
    letI := AlgebraicGeometry.Scheme.linearOfRingHom X ↑R (baseHom π)
    (baseScalarEnd π r).asHom.app N = r • 𝟙 N :=
  (Category.comp_id _).symm

/-- **Pushforward to `Spec R` followed by global sections is `R`-linear global sections**, as
an equality of functors. -/
theorem modulePushforward_comp_moduleSpecΓFunctor :
    RingedSpaceModuleAdjunction.modulePushforward π.toLRSHom.toShHom ⋙
        AlgebraicGeometry.moduleSpecΓFunctor =
      sectionsOverBase π :=
  rfl

/-- Pushforward to `Spec R` followed by global sections carries multiplication by `r` on an
`𝒪_X`-module to multiplication by `r` on its `R`-module of global sections. -/
theorem sectionsOverBase_map_baseScalarEnd (r : ↑R) (N : SheafOfModules.{u} X.ringCatSheaf) :
    (RingedSpaceModuleAdjunction.modulePushforward π.toLRSHom.toShHom ⋙
        AlgebraicGeometry.moduleSpecΓFunctor).map ((baseScalarEnd π r).asHom.app N) =
      (Stacks.scalarEnd R r).asHom.app
        ((RingedSpaceModuleAdjunction.modulePushforward π.toLRSHom.toShHom ⋙
          AlgebraicGeometry.moduleSpecΓFunctor).obj N) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let y : N.val.obj (op ⊤) := x
  show ((baseScalarEnd π r).asHom.app N).val.app (op ⊤) y =
      (show X.ringCatSheaf.obj.obj (op ⊤) from baseHom π r) • y
  rw [baseScalarEnd_app_eq_smul_id π r N]
  simpa using AlgebraicGeometry.Scheme.smul_val_app_top X ↑R (baseHom π) r (𝟙 N) y

/-- **`M ↦ π^*M̃` carries multiplication by `r` to multiplication by `r`.** -/
theorem tildePullback_map_scalarEnd (r : ↑R) (M : ModuleCat.{u} R) :
    (AlgebraicGeometry.tilde.functor R ⋙
        RingedSpaceModuleAdjunction.modulePullback π.toLRSHom.toShHom).map
          ((Stacks.scalarEnd R r).asHom.app M) =
      (baseScalarEnd π r).asHom.app ((AlgebraicGeometry.tilde.functor R ⋙
        RingedSpaceModuleAdjunction.modulePullback π.toLRSHom.toShHom).obj M) :=
  Adjunction.map_endOfId
    (AlgebraicGeometry.tilde.adjunction.comp
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction π.toLRSHom.toShHom))
    (sectionsOverBase_map_baseScalarEnd π r) M

/-- **`M ↦ 𝓕 ⊗_R M` carries multiplication by `r` to multiplication by `r`.** -/
theorem tensorSheafFunctor_map_scalarEnd (r : ↑R) (M : ModuleCat.{u} R) :
    (tensorSheafFunctor π F).map ((Stacks.scalarEnd R r).asHom.app M) =
      (baseScalarEnd π r).asHom.app ((tensorSheafFunctor π F).obj M) := by
  have h2 := congrArg
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj F).map
    (tildePullback_map_scalarEnd π r M)
  exact h2.trans (Stacks.sheafTensorRight_map_globalSmul F
    (Stacks.SheafOfModules.terminalSection X.ringCatSheaf ⊤ Limits.isTerminalTop
      (baseHom π r)) _)

/-- **`M ↦ 𝓕 ⊗_R M` is `R`-linear**, for the `R`-linear structure on `𝒪_X`-modules given by
the ring map `R → Γ(X, 𝒪_X)`. -/
theorem linear_tensorSheafFunctor :
    letI := AlgebraicGeometry.Scheme.linearOfRingHom X ↑R (baseHom π)
    Functor.Linear ↑R (tensorSheafFunctor π F) := by
  let _ : Linear ↑R (SheafOfModules.{u} X.ringCatSheaf) :=
    AlgebraicGeometry.Scheme.linearOfRingHom X ↑R (baseHom π)
  rw [Functor.linear_iff]
  intro M r
  exact (tensorSheafFunctor_map_scalarEnd π F r M).trans
    (baseScalarEnd_app_eq_smul_id π r _)

/-- **`R`-linear global sections are `R`-linear**, for the same structure on `𝒪_X`-modules. -/
theorem linear_sectionsOverBase :
    letI := AlgebraicGeometry.Scheme.linearOfRingHom X ↑R (baseHom π)
    Functor.Linear ↑R (sectionsOverBase π) := by
  let _ : Linear ↑R (SheafOfModules.{u} X.ringCatSheaf) :=
    AlgebraicGeometry.Scheme.linearOfRingHom X ↑R (baseHom π)
  rw [Functor.linear_iff]
  intro N r
  exact (congrArg (fun ψ => (sectionsOverBase π).map ψ)
      (baseScalarEnd_app_eq_smul_id π r N)).symm.trans
    (sectionsOverBase_map_baseScalarEnd π r N)

/-- **`Hⁿ(X, -)` is `R`-linear.** -/
theorem linear_cohomologyDeltaFunctor (n : ℕ) :
    letI := AlgebraicGeometry.Scheme.linearOfRingHom X ↑R (baseHom π)
    Functor.Linear ↑R ((cohomologyDeltaFunctor π).functor n) := by
  let := AlgebraicGeometry.Scheme.linearOfRingHom X ↑R (baseHom π)
  let := linear_sectionsOverBase π
  exact Stacks.DerivedLinear.rightDerived_linear (sectionsOverBase π) n

/-- **The obstruction module functor is `R`-linear**: `𝒪(M) = H¹(X, 𝓕 ⊗_R M)` is an
`R`-linear endofunctor of the category of `R`-modules. -/
instance linear_obstructionFunctor : Functor.Linear ↑R (obstructionFunctor π F) := by
  let := AlgebraicGeometry.Scheme.linearOfRingHom X ↑R (baseHom π)
  let := linear_tensorSheafFunctor π F
  let := linear_cohomologyDeltaFunctor π 1
  exact inferInstanceAs
    (Functor.Linear ↑R (tensorSheafFunctor π F ⋙ (cohomologyDeltaFunctor π).functor 1))

/-- The obstruction module functor `𝒪(M) = H¹(X, 𝓕 ⊗_R M)`, as an `R`-linear endofunctor of
`Mod_R`. -/
def obstructionLinearEndofunctor : Deformation.Artin.LinearEndofunctor ↑R where
  functor := obstructionFunctor π F

/-! ### The boundary map and the obstruction element -/

/-- **The boundary map** `H⁰(X, 𝓕 ⊗_R M₃) → H¹(X, 𝓕 ⊗_R M₁)`: the connecting morphism of the
short exact sequence `0 → 𝓕 ⊗_R M₁ → 𝓕 ⊗_R M₂ → 𝓕 ⊗_R M₃ → 0`. -/
def boundary (hF : AlgebraicGeometry.IsFlatOver π.toLRSHom.toShHom F)
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    ((cohomologyDeltaFunctor π).functor 0).obj ((tensorSheafFunctor π F).obj S.X₃) ⟶
      ((cohomologyDeltaFunctor π).functor 1).obj ((tensorSheafFunctor π F).obj S.X₁) :=
  (cohomologyDeltaFunctor π).δ (tensorSheafFunctor_shortExact π F hF hS) 0

/-- The target of the boundary map is the obstruction module. -/
theorem boundary_target_eq (M : ModuleCat.{u} R) :
    ((cohomologyDeltaFunctor π).functor 1).obj ((tensorSheafFunctor π F).obj M) =
      (obstructionFunctor π F).obj M :=
  rfl

/-- **The obstruction element**: the image of a section `x` of `𝓕 ⊗_R M₃` under the boundary
map, an element of `H¹(X, 𝓕 ⊗_R M₁)`. -/
def obstructionClass (hF : AlgebraicGeometry.IsFlatOver π.toLRSHom.toShHom F)
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (x : (((cohomologyDeltaFunctor π).functor 0).obj
      ((tensorSheafFunctor π F).obj S.X₃) : Type u)) :
    (((cohomologyDeltaFunctor π).functor 1).obj
      ((tensorSheafFunctor π F).obj S.X₁) : Type u) :=
  (boundary π F hF hS) x

/-- The obstruction element of a section `x` of `𝓕 ⊗_R M₃` vanishes if and only if `x` is the
image of a section of `𝓕 ⊗_R M₂`. -/
theorem obstructionClass_eq_zero_iff
    (hF : AlgebraicGeometry.IsFlatOver π.toLRSHom.toShHom F)
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (x : (((cohomologyDeltaFunctor π).functor 0).obj
      ((tensorSheafFunctor π F).obj S.X₃) : Type u)) :
    obstructionClass π F hF hS x = 0 ↔
      ∃ y : (((cohomologyDeltaFunctor π).functor 0).obj
          ((tensorSheafFunctor π F).obj S.X₂) : Type u),
        (((cohomologyDeltaFunctor π).functor 0).map ((tensorSheafFunctor π F).map S.g)) y = x :=
  (exists_preimage_iff_δ_eq_zero (cohomologyDeltaFunctor π)
    (tensorSheafFunctor_shortExact π F hF hS) x).symm

/-! ### The lifting criterion on global sections -/

/-- **`H⁰(X, -)` is the functor of global sections**: the degree-zero term of the cohomology
δ-functor is isomorphic to `R`-linear global sections. -/
def zeroIsoSections : (cohomologyDeltaFunctor π).functor 0 ≅ sectionsOverBase π :=
  Functor.rightDerivedZeroIsoSelf (sectionsOverBase π)

/-- The degree-zero comparison commutes with the map induced by a morphism of
`𝒪_X`-modules. -/
theorem zeroIsoSections_inv_app_map {G₂ G₃ : SheafOfModules.{u} X.ringCatSheaf} (g : G₂ ⟶ G₃)
    (y : ((sectionsOverBase π).obj G₂ : Type u)) :
    (((cohomologyDeltaFunctor π).functor 0).map g) ((zeroIsoSections π).inv.app G₂ y) =
      (zeroIsoSections π).inv.app G₃ (((sectionsOverBase π).map g) y) :=
  (ConcreteCategory.congr_hom ((zeroIsoSections π).inv.naturality g) y).symm

/-- The degree-zero comparison is injective on sections. -/
theorem zeroIsoSections_inv_app_injective (G : SheafOfModules.{u} X.ringCatSheaf)
    {a b : ((sectionsOverBase π).obj G : Type u)}
    (h : (zeroIsoSections π).inv.app G a = (zeroIsoSections π).inv.app G b) : a = b := by
  simpa using congrArg ((zeroIsoSections π).hom.app G) h

/-- The inverse of the degree-zero comparison undoes the comparison on sections. -/
theorem zeroIsoSections_inv_hom_app (G : SheafOfModules.{u} X.ringCatSheaf)
    (y : (((cohomologyDeltaFunctor π).functor 0).obj G : Type u)) :
    (zeroIsoSections π).inv.app G ((zeroIsoSections π).hom.app G y) = y := by
  simp

/-- A global section `x` of `𝓕 ⊗_R M₃` is the image of a global section of `𝓕 ⊗_R M₂` if and
only if its obstruction class vanishes. -/
theorem exists_section_iff_obstructionClass_eq_zero
    (hF : AlgebraicGeometry.IsFlatOver π.toLRSHom.toShHom F)
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (x : ((sectionsOverBase π).obj ((tensorSheafFunctor π F).obj S.X₃) : Type u)) :
    (∃ y : ((sectionsOverBase π).obj ((tensorSheafFunctor π F).obj S.X₂) : Type u),
        ((sectionsOverBase π).map ((tensorSheafFunctor π F).map S.g)) y = x) ↔
      obstructionClass π F hF hS ((zeroIsoSections π).inv.app _ x) = 0 := by
  rw [obstructionClass_eq_zero_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(zeroIsoSections π).inv.app _ y,
      zeroIsoSections_inv_app_map π ((tensorSheafFunctor π F).map S.g) y⟩
  · rintro ⟨y, hy⟩
    refine ⟨(zeroIsoSections π).hom.app _ y, ?_⟩
    refine zeroIsoSections_inv_app_injective π ((tensorSheafFunctor π F).obj S.X₃) ?_
    rw [← zeroIsoSections_inv_app_map π ((tensorSheafFunctor π F).map S.g),
      zeroIsoSections_inv_hom_app]
    exact hy

/-- **Naturality of the boundary map.** A morphism
`φ` of short exact sequences of `R`-modules makes the square of boundary maps commute. -/
theorem boundary_naturality (hF : AlgebraicGeometry.IsFlatOver π.toLRSHom.toShHom F)
    {S T : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    ((cohomologyDeltaFunctor π).functor 0).map ((tensorSheafFunctor π F).map φ.τ₃) ≫
        boundary π F hF hT =
      boundary π F hF hS ≫
        ((cohomologyDeltaFunctor π).functor 1).map ((tensorSheafFunctor π F).map φ.τ₁) :=
  (cohomologyDeltaFunctor π).δ_naturality (tensorSheafFunctor_shortExact π F hF hS)
    (tensorSheafFunctor_shortExact π F hF hT) ((tensorSheafFunctor π F).mapShortComplex.map φ) 0

/-- **Naturality of the obstruction element.** A morphism of short exact
sequences of `R`-modules carries the obstruction element of a section to the obstruction
element of its image. -/
theorem obstructionClass_naturality (hF : AlgebraicGeometry.IsFlatOver π.toLRSHom.toShHom F)
    {S T : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (x : (((cohomologyDeltaFunctor π).functor 0).obj
      ((tensorSheafFunctor π F).obj S.X₃) : Type u)) :
    obstructionClass π F hF hT
        ((((cohomologyDeltaFunctor π).functor 0).map ((tensorSheafFunctor π F).map φ.τ₃)) x) =
      (((cohomologyDeltaFunctor π).functor 1).map ((tensorSheafFunctor π F).map φ.τ₁))
        (obstructionClass π F hF hS x) :=
  ConcreteCategory.congr_hom (boundary_naturality π F hF hS hT φ) x

end Cohomology

end Base

/-! ### Flatness under base change -/

section BaseChange

variable {Λ : CommRingCat.{u}} {W : Scheme.{u}} (p : W ⟶ Spec Λ)
  (𝓕 : SheafOfModules.{u} W.ringCatSheaf) [𝓕.IsQuasicoherent]

/-- **Flatness over the base passes to every base change**: if a quasi-coherent `𝓕` on `W` is
flat over `Spec Λ`, then for every `T ⟶ Spec Λ` its pullback `𝓕_T` to `W_T = T ×_{Spec Λ} W`
is flat over `T`. -/
theorem isFlatOver_baseChange
    (hF : AlgebraicGeometry.IsFlatOver p.toLRSHom.toShHom 𝓕)
    {T : Scheme.{u}} (t : T ⟶ Spec Λ) :
    AlgebraicGeometry.IsFlatOver (Limits.pullback.fst t p).toLRSHom.toShHom
      ((RingedSpaceModuleAdjunction.modulePullback
        (Limits.pullback.snd t p).toLRSHom.toShHom).obj 𝓕) := by
  have : (show SheafOfModules.{u} (structureSheafRing W.toRingedSpace) from
      𝓕).IsQuasicoherent := inferInstanceAs 𝓕.IsQuasicoherent
  exact AlgebraicGeometry.modulePullback_isFlatOver
    (CategoryTheory.IsPullback.of_hasPullback t p).flip 𝓕 hF

end BaseChange

/-! ### Lifting in the category of elements of a presheaf -/

section FibredCategory

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (Y : Scheme.{u}) (hY : B.Contains Y)
  (presheaf : (AlgebraicGeometry.BigFppfOver B Y hY)ᵒᵖ ⥤ Type u)

/-- An object of the category of elements of a presheaf on the big fppf site over `Y`, lying
over `Spec A`, lifts across a deformation situation `A' → A`, in the sense of
`Deformation.Artin.AffineObject.HasLift`, if and only if the section it names is the
restriction of a section over `Spec A'`. -/
theorem hasLift_iff_exists_section
    (Q : Deformation.Artin.AffineObject B Y hY
      (PresheafOfCategories.discreteProjection presheaf))
    (t : Deformation.Artin.DeformationSituation B Y hY Q.alg) :
    Deformation.Artin.AffineObject.HasLift
        (Functor.IsFiberedInSets.isFiberedInGroupoids
          (PresheafOfCategories.discreteProjection presheaf)) Q t ↔
      ∃ s' : presheaf.obj (op t.top.over),
        presheaf.map t.hom.specMap.op s' =
          PresheafOfCategories.discreteFiberEquiv presheaf Q.alg.over Q.obj :=
  PresheafOfCategories.nonempty_iso_pullbackFunctor_obj_iff presheaf t.hom.specMap Q.obj

end FibredCategory

end Deformation.Artin.SectionsSheaf

end
