module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerGradedFamily

/-!
# Factoring the products `IᵐN` through a subobject

Let `X` be an algebraic space, `I ⊆ 𝒪_X` a sheaf of ideals generated on the affine étale charts
by global functions `a₁, …, a_r`, and `N₀ ⊆ F` a submodule of an `𝒪_X`-module.  Let
`η : N₀ ⟶ V` be a morphism of `𝒪_X`-modules, `ρ m : V ⟶ V` endomorphisms and `ι : E ⟶ V` a
monomorphism.  Suppose that `η ≫ ρ 0` factors through `ι`, and that for each `i` there are
endomorphisms `σᵢ` of `V` and `eᵢ` of `E` with `aᵢ ≫ ρ (m + 1) = ρ m ≫ σᵢ` and
`ι ≫ σᵢ = eᵢ ≫ ι`.  Then `IᵐN₀ ⟶ N₀ ⟶ V` followed by `ρ m` factors through `ι` for every `m`.

This is the shape of the inclusion of the degree-`m` piece `IᵐF tᵐ` into the Rees module of the
proof of [Stacks, Tag 08AW]: `ρ m` is multiplication by `tᵐ` and `σᵢ` multiplication by the
degree-one element `aᵢ t` of the Rees algebra, which preserves the Rees module.

## Main results

* `AlgebraicGeometry.Space.exists_comp_eq_idealPowSmul_homOfLE_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules (globalSmul)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **The products `IᵐN₀`, mapped to `V` and multiplied by `ρ m`, factor through `ι`.** -/
theorem exists_comp_eq_idealPowSmul_homOfLE_comp {F : Modules.{u, u} B S hS X.1 X.2}
    (N₀ : F.Submodule) (I : IdealSheaves B S hS X.1 X.2) {r : ℕ}
    (a : Fin r → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
    (ha : ∀ i (W : SmallEtale B S hS X.1), (a i).1 (op W) ∈ I.obj (op W))
    (hgen : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
      ∀ b ∈ I.obj (op A), ∃ c : Fin r → (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        (op A), b = ∑ i, c i * (a i).1 (op A))
    {V E : Modules.{u, u} B S hS X.1 X.2} (η : N₀.toSheafOfModules ⟶ V) (ρ : ℕ → (V ⟶ V))
    (ι : E ⟶ V) [hι : Mono ι] (σ : Fin r → (V ⟶ V)) (e : Fin r → (E ⟶ E))
    (h₀ : ∃ w, w ≫ ι = Stacks.SheafOfModules.Submodule.homOfLE
      (Stacks.Sites.idealPowSmul_le_self I 0 N₀) ≫ η ≫ ρ 0)
    (hρ : ∀ i m, globalSmul _ (a i) V ≫ ρ (m + 1) = ρ m ≫ σ i)
    (hσ : ∀ i, ι ≫ σ i = e i ≫ ι) (m : ℕ) :
    ∃ w, w ≫ ι = Stacks.SheafOfModules.Submodule.homOfLE
      (Stacks.Sites.idealPowSmul_le_self I m N₀) ≫ η ≫ ρ m := by
  induction m with
  | zero => exact h₀
  | succ m ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨Abelian.monoLift ι _ ?_, Abelian.monoLift_comp _ _ _⟩
    refine eq_zero_of_comp_idealSmulHom_eq_zero I a ha hgen
      (Stacks.Sites.idealPowSmul (M := F) I m N₀) (Stacks.Sites.idealPowSmul (M := F) I (m + 1) N₀)
      (idealPowSmul_succ_eq_idealSmul I m N₀).symm _ (fun i => ?_)
    have hincl : idealSmulHom I (a i) (ha i) (Stacks.Sites.idealPowSmul (M := F) I m N₀)
        (Stacks.Sites.idealPowSmul (M := F) I (m + 1) N₀)
        (idealPowSmul_succ_eq_idealSmul I m N₀).symm.le ≫
          Stacks.SheafOfModules.Submodule.homOfLE (Stacks.Sites.idealPowSmul_le_self I (m + 1) N₀) =
        Stacks.SheafOfModules.Submodule.homOfLE (Stacks.Sites.idealPowSmul_le_self I m N₀) ≫
          globalSmul _ (a i) N₀.toSheafOfModules := by
      rw [← cancel_mono N₀.ι, Category.assoc, Category.assoc,
        Stacks.SheafOfModules.Submodule.homOfLE_comp_ι, idealSmulHom_ι,
        ← Stacks.Cohomology.SiteModules.comp_globalSmul,
        Stacks.SheafOfModules.Submodule.homOfLE_comp_ι_assoc]
    calc _ = (idealSmulHom I (a i) (ha i) (Stacks.Sites.idealPowSmul (M := F) I m N₀)
          (Stacks.Sites.idealPowSmul (M := F) I (m + 1) N₀)
          (idealPowSmul_succ_eq_idealSmul I m N₀).symm.le ≫
          Stacks.SheafOfModules.Submodule.homOfLE (Stacks.Sites.idealPowSmul_le_self I (m + 1) N₀))
            ≫ η ≫ ρ (m + 1) ≫ cokernel.π ι := by simp only [Category.assoc]
      _ = Stacks.SheafOfModules.Submodule.homOfLE (Stacks.Sites.idealPowSmul_le_self I m N₀) ≫
          (η ≫ globalSmul _ (a i) V) ≫ ρ (m + 1) ≫ cokernel.π ι := by
          rw [hincl, Category.assoc, ← Category.assoc (globalSmul _ (a i) N₀.toSheafOfModules) η,
            ← Stacks.Cohomology.SiteModules.comp_globalSmul]
      _ = (Stacks.SheafOfModules.Submodule.homOfLE (Stacks.Sites.idealPowSmul_le_self I m N₀) ≫
          η ≫ ρ m) ≫ σ i ≫ cokernel.π ι := by
          rw [Category.assoc η, ← Category.assoc (globalSmul _ (a i) V), hρ i m]
          simp only [Category.assoc]
      _ = w ≫ (ι ≫ σ i) ≫ cokernel.π ι := by rw [← hw]; simp only [Category.assoc]
      _ = 0 := by rw [hσ i]; simp only [Category.assoc, cokernel.condition, comp_zero]

end AlgebraicGeometry.Space

end
