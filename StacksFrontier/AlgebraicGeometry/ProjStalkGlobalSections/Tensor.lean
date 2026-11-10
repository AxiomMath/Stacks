module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Tensor
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections

/-!
# Global sections and the tensor product of associated sheaves on Proj

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ` and let `M`, `N` be
`ℤ`-graded `S`-modules. The canonical morphism `M̃ ⊗_𝒪 Ñ ⟶ (M ⊗[S] N)~` of Tag 01MK is
compatible with the maps from degree-zero elements into global sections: the square whose
top edge is `M₀ ⊗ N₀ → (M ⊗ N)₀`, whose bottom edge is that morphism on global sections and
whose vertical edges are the degree-zero global-sections maps, commutes. This file proves
that on a pure tensor of degree-zero elements, which is the remaining assertion of Tag 01MK.

## Main results

* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafTensorMap_globalSections`:
  the canonical morphism carries the tensor of the global sections attached to `m` and `n` to
  the global section attached to `m ⊗ₜ n`.

## Implementation notes

The morphism is the sheafification adjunct of the pointwise tensor of sections, so on a
section coming from the tensor-product presheaf it is the pointwise tensor map. Evaluating at
a point, both sides are the fraction `(m ⊗ₜ n) / 1` in the localization of `M ⊗[S] N`, once
the localized tensor product is identified with the tensor product of the localizations by
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorLocalizationEquivOverLocalization`.

All three modules live in the same universe because the tensor product of sheaves of modules
is taken from `Stacks.SheafOfModules.TensorStalkRingedSpace`, which is stated over a
`RingedSpace.{u, u}`.

## References

* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite TopCat DirectSum
open AlgebraicGeometry
open Stacks.GradedLocalization
open Stacks.GradedModule (tensorGrading)
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u w t t'

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S M N : Type u} {σ : Type w} {τ : Type t} {υ : Type t'}
  [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]
  [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]

/-- The canonical morphism commutes with the maps from degree-zero elements into global
sections, evaluated on a pure tensor. -/
@[stacks 01MK "global-sections compatibility"]
theorem associatedModuleSheafTensorMap_globalSections (m : 𝒨 0) (n : 𝒩 0) :
    letI := ProjSheafFunctoriality.tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
    letI := ProjSheafFunctoriality.tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
    let F := ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨
    let G := ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒩
    ((ProjSheafFunctoriality.associatedModuleSheafTensorMap 𝒮 𝒨 𝒩).val.app (op ⊤))
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
        (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace F G (op ⊤)
        ((degreeZeroToGlobalSections 𝒮 𝒨 m) ⊗ₜ[_]
         (degreeZeroToGlobalSections 𝒮 𝒩 n))) =
      degreeZeroToGlobalSections 𝒮 (tensorGrading (S := S) 𝒨 𝒩)
        ⟨m.1 ⊗ₜ[S] n.1,
          (by
            apply AddSubgroup.subset_closure
            exact ⟨0, 0, by simp, m.1, m.2, n.1, n.2, rfl⟩)⟩ := by
  let _ := ProjSheafFunctoriality.tensorGrading_decomposition (S := S) 𝒮 𝒨 𝒩
  let _ := ProjSheafFunctoriality.tensorGrading_gradedSMul (S := S) 𝒮 𝒨 𝒩
  dsimp
  refine .trans (ProjSheafFunctoriality.associatedModuleSheafTensorMap_app_toTensorSheafSection
    𝒮 𝒨 𝒩 _ _) ?_
  change ProjSheafFunctoriality.tensorModuleSectionsAddHom
      (S := S) (𝒮 := 𝒮) (𝒨 := 𝒨) (𝒩 := 𝒩) (⊤ : Opens (ProjectiveSpectrum.top 𝒮))
      ((degreeZeroToGlobalSections 𝒮 𝒨 m) ⊗ₜ[
        ↑((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op ⊤))]
       (degreeZeroToGlobalSections 𝒮 𝒩 n)) = _
  refine .trans (ProjSheafFunctoriality.tensorModuleSectionsAddHom_tmul 𝒮 𝒨 𝒩 _ _ _) ?_
  apply Subtype.ext
  funext x
  change ProjSheafFunctoriality.tensorLocalizationEquivOverLocalization
      (S := S) (M := M) (N := N) x.1.asHomogeneousIdeal.toIdeal.primeCompl
      ((degreeZeroToGlobalSections 𝒮 𝒨 m).1 x ⊗ₜ[S]
       (degreeZeroToGlobalSections 𝒮 𝒩 n).1 x) =
    (degreeZeroToGlobalSections 𝒮 (tensorGrading (S := S) 𝒨 𝒩) ⟨m.1 ⊗ₜ[S] n.1, _⟩).1 x
  rw [degreeZeroToGlobalSections_apply, degreeZeroToGlobalSections_apply,
    degreeZeroToGlobalSections_apply,
    ProjSheafFunctoriality.tensorLocalizationEquivOverLocalization_mk]
  congr 1
  apply Subtype.ext
  simp

end Stacks.AlgebraicGeometry.ProjStalkGlobalSections
