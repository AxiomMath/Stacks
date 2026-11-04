module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.Functoriality
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjImmersion.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherent modules and the canonical morphism to `Proj` of the section ring

In the situation of Stacks Tag 01QH — `X` a scheme, `L` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, L)` the graded section ring of Stacks Tag 01CV and `f : X ⟶ Proj S` the canonical
morphism of Stacks Tag 01PZ — Stacks Tag 01QJ attaches to a quasi-coherent `𝒪_X`-module `ℱ` the
graded `S`-module `M = Γ_*(X, L, ℱ) = ⨁_{m ≥ 0} Γ(X, ℱ ⊗ L ^⊗ m)` and asserts that `f^* M̃` is
isomorphic to `ℱ`, functorially in `ℱ`.

This file assembles the functor the assertion is about. The graded module is covariant in `ℱ`
(`Stacks.TwistedSections.twistModuleLinearMap`), the sheaf associated to a graded module is
covariant in the graded module
(`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor`), and pulling
back along `f` is a functor, so the composite

`ℱ ↦ f^* (Γ_*(X, L, ℱ))~`

is an endofunctor of the category of `𝒪_X`-modules. Functoriality of Tag 01QJ's isomorphism in
`ℱ` is the statement that this endofunctor is naturally isomorphic to the identity.

## Main definitions

* `Stacks.SectionRingProjQuasicoherent.gradedTwistedSections`: `Γ_*(X, L, ℱ)` as an object of
  the category of graded `Γ_*(X, L)`-modules.
* `Stacks.SectionRingProjQuasicoherent.gradedTwistedSectionsFunctor`: the same, as a functor in
  `ℱ`.
* `Stacks.SectionRingProjQuasicoherent.associatedSchemeFunctor`: the associated-sheaf functor,
  with its target written as the category of modules on the *scheme* `Proj Γ_*(X, L)`.
* `Stacks.SectionRingProjQuasicoherent.tildeFunctor`: `ℱ ↦ (Γ_*(X, L, ℱ))~` on `Proj Γ_*(X, L)`.
* `Stacks.SectionRingProjQuasicoherent.pullbackTildeFunctor`: `ℱ ↦ f^* (Γ_*(X, L, ℱ))~`, the
  left-hand side of Stacks Tag 01QJ.

## References

* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace DirectSum
open Stacks.Ample Stacks.GradedSections
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (GradedModuleCat
  associatedModuleSheafFunctor)

universe u

namespace Stacks.SectionRingProjQuasicoherent

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### The graded module of twisted sections as a functor -/

/-- **`Γ_*(X, L, ℱ) = ⨁_{m ≥ 0} Γ(X, ℱ ⊗ L ^⊗ m)` as a graded `Γ_*(X, L)`-module**, in the
bundled category of graded modules whose associated sheaf on `Proj Γ_*(X, L)` is formed. -/
def gradedTwistedSections (F : X.Modules) :
    GradedModuleCat.{u, u, u} (grading L) where
  carrier := Stacks.TwistedSections.twistModule F L
  grade := Stacks.TwistedSections.moduleGrading F L

/-- The grading of `gradedTwistedSections L F` is the grading of `Γ_*(X, L, F)` by degree. -/
@[simp] theorem gradedTwistedSections_grade (F : X.Modules) :
    (gradedTwistedSections L F).grade = Stacks.TwistedSections.moduleGrading F L := rfl

/-- Two degree-preserving morphisms of graded modules with the same underlying linear map are
equal. -/
theorem gradedModuleCat_hom_ext {𝒮 : ℕ → AddSubgroup (sectionRing L)} [GradedRing 𝒮]
    {M N : GradedModuleCat.{u, u, u} 𝒮} {φ ψ : M ⟶ N}
    (h : φ.toLinearMap = ψ.toLinearMap) : φ = ψ := by
  cases φ; cases ψ; subst h; rfl

/-- **The graded module of twisted sections, as a functor in the module.** -/
@[ega "0 5.4.6" "partial"]
def gradedTwistedSectionsFunctor :
    X.Modules ⥤ GradedModuleCat.{u, u, u} (grading L) where
  obj F := gradedTwistedSections L F
  map φ := ⟨Stacks.TwistedSections.twistModuleLinearMap φ,
    Stacks.TwistedSections.twistModuleHom_mem_moduleGrading φ⟩
  map_id _F := gradedModuleCat_hom_ext L <| LinearMap.ext fun x =>
    DFunLike.congr_fun (Stacks.TwistedSections.twistModuleHom_id (L := L)) x
  map_comp φ ψ := gradedModuleCat_hom_ext L <| LinearMap.ext fun x =>
    DFunLike.congr_fun (Stacks.TwistedSections.twistModuleHom_comp (L := L) φ ψ) x

/-- `gradedTwistedSectionsFunctor L` sends `F` to `gradedTwistedSections L F`. -/
@[simp] theorem gradedTwistedSectionsFunctor_obj (F : X.Modules) :
    (gradedTwistedSectionsFunctor L).obj F = gradedTwistedSections L F := rfl

/-- The linear map underlying `(gradedTwistedSectionsFunctor L).map φ` is the map
`Γ_*(X, L, F) → Γ_*(X, L, G)` induced by `φ`. -/
@[simp] theorem gradedTwistedSectionsFunctor_map_toLinearMap {F G : X.Modules} (φ : F ⟶ G) :
    ((gradedTwistedSectionsFunctor L).map φ).toLinearMap =
      Stacks.TwistedSections.twistModuleLinearMap φ := rfl

/-! ### The associated sheaf on the scheme `Proj Γ_*(X, L)` -/

/-- **The associated-sheaf functor of Stacks Tag 01M6, with its target written as the category
of modules on the scheme `Proj Γ_*(X, L)`.** The two sheaves of rings are the same by
definition. -/
def associatedSchemeFunctor :
    GradedModuleCat.{u, u, u} (grading L) ⥤
      (AlgebraicGeometry.Proj (grading L)).Modules :=
  associatedModuleSheafFunctor (grading L)

/-- **`ℱ ↦ (Γ_*(X, L, ℱ))~`**, the sheaf on `Proj Γ_*(X, L)` associated to the graded module of
twisted sections, as a functor in `ℱ`. -/
def tildeFunctor : X.Modules ⥤ (AlgebraicGeometry.Proj (grading L)).Modules :=
  gradedTwistedSectionsFunctor L ⋙ associatedSchemeFunctor L

/-- **`ℱ ↦ f^* (Γ_*(X, L, ℱ))~`, the left-hand side of Stacks Tag 01QJ**, for `f` the canonical
morphism `X ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ. -/
def pullbackTildeFunctor (hL : IsAmple X L) : X.Modules ⥤ X.Modules :=
  tildeFunctor L ⋙
    Scheme.Modules.pullback (Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL)

end Stacks.SectionRingProjQuasicoherent

end
