module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianComposition

/-!
# Cancelling the first factor of a composite along which a module is cartesian

`Stacks.PresheafOfModules.bijective_restrictionBaseChange_comp_iff` compares the base-change
comparison of a presheaf of modules over a composite `f ≫ g` with the one over `f`, given that the
module is cartesian over `g`. This file records the other cancellation: if the module is cartesian
over `f` and over `f ≫ g`, it is cartesian over `g`. The comparison over `f ≫ g` is the comparison
over `g` precomposed with the base change of the comparison over `f`, up to the cancellation
isomorphism of tensor products, and the latter base change is then bijective.

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_comp`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v r m

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
  (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))

/-- **Cancellation of the first factor.** If `M` is cartesian over `f` and over `f ≫ g`, it is
cartesian over `g`. -/
theorem bijective_restrictionBaseChange_of_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Function.Bijective (restrictionBaseChange M f))
    (hfg : Function.Bijective (restrictionBaseChange M (f ≫ g))) :
    Function.Bijective (restrictionBaseChange M g) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let : Algebra (R.obj Y) (R.obj Z) := (R.map g).hom.toAlgebra
  let : Algebra (R.obj X) (R.obj Z) := (R.map (f ≫ g)).hom.toAlgebra
  let : IsScalarTower (R.obj X) (R.obj Y) (R.obj Z) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show (R.map (f ≫ g)).hom a = (R.map g).hom ((R.map f).hom a)
    rw [R.map_comp]
    rfl
  let θ : TensorProduct (R.obj X) (R.obj Y) (M.obj X) →ₗ[R.obj Y] M.obj Y :=
    (restrictionBaseChange M f).hom
  let θg : TensorProduct (R.obj Y) (R.obj Z) (M.obj Y) →ₗ[R.obj Z] M.obj Z :=
    (restrictionBaseChange M g).hom
  let θfg : TensorProduct (R.obj X) (R.obj Z) (M.obj X) →ₗ[R.obj Z] M.obj Z :=
    (restrictionBaseChange M (f ≫ g)).hom
  let c := AlgebraTensorModule.cancelBaseChange (R.obj X) (R.obj Y) (R.obj Z) (R.obj Z)
    (M.obj X)
  have key : ∀ z, θfg (c z) = θg (LinearMap.lTensor (R.obj Z) θ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul d w =>
      induction w using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | add w w' hw hw' => simp only [tmul_add, map_add, hw, hw']
      | tmul b x =>
        rw [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.lTensor_tmul]
        have h1 : θfg ((b • d) ⊗ₜ x) = (b • d) • (M.map (f ≫ g) x : M.obj Z) :=
          restrictionBaseChange_tmul M (f ≫ g) (b • d) x
        have h2 : θ (b ⊗ₜ x) = b • (M.map f x : M.obj Y) := restrictionBaseChange_tmul M f b x
        have h3 : θg (d ⊗ₜ (b • (M.map f x : M.obj Y))) =
            d • (M.map g (b • (M.map f x : M.obj Y)) : M.obj Z) :=
          restrictionBaseChange_tmul M g d (b • (M.map f x : M.obj Y))
        have h4 : (M.map g (b • (M.map f x : M.obj Y)) : M.obj Z) =
            (R.map g).hom b • (M.map g (M.map f x) : M.obj Z) :=
          M.map_smul g b (M.map f x)
        have h5 : (M.map (f ≫ g) x : M.obj Z) = M.map g (M.map f x) := M.map_comp_apply f g x
        rw [h1, h2, h3, h4, h5, smul_smul]
        congr 1
        show (R.map g).hom b * d = d * (R.map g).hom b
        exact mul_comm _ _
  have hθ : Function.Bijective (LinearMap.lTensor (R.obj Z) θ) :=
    (LinearEquiv.lTensor (R.obj Z) (LinearEquiv.ofBijective θ hf)).bijective
  have hc : (⇑θg) ∘ ⇑(LinearMap.lTensor (R.obj Z) θ) = (⇑θfg) ∘ ⇑c := (funext key).symm
  have h' : Function.Bijective ((⇑θg) ∘ ⇑(LinearMap.lTensor (R.obj Z) θ)) := by
    rw [hc]; exact hfg.comp c.bijective
  exact (Function.Bijective.of_comp_iff _ hθ).mp h'

end Stacks.PresheafOfModules
