module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.AffineScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Gluing morphisms that agree on affine test schemes

A family of morphisms `φ z : U z ⟶ Y` on open neighbourhoods `U z` of the points of a scheme `Z`
glues to a morphism `Z ⟶ Y` as soon as any two of them agree after composition with maps from an
affine scheme into the two opens that agree in `Z`.

## Main results

* `AlgebraicGeometry.Scheme.exists_hom_of_affine_compat`: morphisms on the opens of a cover that
  agree on affine test schemes glue to a morphism `Z ⟶ Y`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Morphisms glue along an open cover when they agree on affine test schemes.** If for every
point `z` of `Z` a morphism `φ z : U z ⟶ Y` is given on an open neighbourhood `U z`, and any two of
them agree after composition with maps from an affine scheme `R` into the two opens which agree in
`Z`, then they glue to a morphism `Z ⟶ Y`. -/
@[ega "I 2.5.3" "partial"]
theorem Scheme.exists_hom_of_affine_compat {Z Y : Scheme.{u}} (U : Z → Z.Opens)
    (hU : ∀ z, z ∈ U z) (φ : ∀ z, (U z).toScheme ⟶ Y)
    (hcomp : ∀ (z z' : Z) (R : Scheme.{u}) [IsAffine R] (r : R ⟶ U z) (r' : R ⟶ U z'),
      r ≫ (U z).ι = r' ≫ (U z').ι → r ≫ φ z = r' ≫ φ z') :
    ∃ Φ : Z ⟶ Y, ∀ z, (U z).ι ≫ Φ = φ z := by
  let 𝒰 : Z.OpenCover := {
    I₀ := Z, X i := (U i), f i := (U i).ι,
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      exact ⟨fun x ↦ ⟨x, by simpa using hU x⟩, inferInstance⟩ }
  have hf (x y : Z) : pullback.fst (𝒰.f x) (𝒰.f y) ≫ φ x = pullback.snd _ _ ≫ φ y :=
    (pullback (𝒰.f x) (𝒰.f y)).affineCover.hom_ext _ _ fun _ ↦ by
      rw [← Category.assoc, ← Category.assoc]
      exact hcomp x y _ _ _ (by rw [Category.assoc, Category.assoc, pullback.condition])
  exact ⟨𝒰.glueMorphisms φ hf, 𝒰.ι_glueMorphisms φ hf⟩

end AlgebraicGeometry

end
