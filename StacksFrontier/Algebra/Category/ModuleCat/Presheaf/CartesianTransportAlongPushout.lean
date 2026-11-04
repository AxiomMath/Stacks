module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.Algebra.Category.Ring.PushoutTensorComparison
public import StacksFrontier.RingTheory.Descent.PushoutBaseChange
public import StacksFrontier.LinearAlgebra.TensorProduct.BaseChangeBijective

/-!
# Cartesianness transported across a pushout square of rings

Let `N` be a presheaf of modules over a presheaf of commutative rings `R` on `C`, and `M` one over
`R'` on `D`. Consider an arrow `φ : w₁ ⟶ w₂` of `C` and an arrow `ψ : x₁ ⟶ x₂` of `D`, ring maps
`αᵢ : R(wᵢ) ⟶ R'(xᵢ)` making the square

`R(w₂) ⟶ R(w₁)`, `R(w₂) ⟶ R'(x₂)`, `R(w₁) ⟶ R'(x₁)`, `R'(x₂) ⟶ R'(x₁)`

a pushout of commutative rings, and additive identifications `N(wᵢ) ≃ M(xᵢ)`, semilinear along
`αᵢ` and compatible with the restriction maps. If `M` is cartesian along `ψ` (its base change map
`R'(x₁) ⊗_{R'(x₂)} M(x₂) ⟶ M(x₁)` is bijective) then `N` is cartesian along `φ`.

This is the algebra of the flat base change of a direct image along a base change of affine
schemes: `R(w₁) ⊗_{R(w₂)} M(x₂) = R'(x₁) ⊗_{R'(x₂)} M(x₂)` across the pushout
(`Module.Descent.pushoutBaseChangeEquiv`).

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_pushout_transport`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v₁ u₁ v₂ u₂ r m

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {R : Cᵒᵖ ⥤ CommRingCat.{r}} {R' : Dᵒᵖ ⥤ CommRingCat.{r}}
  (N : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
  (M : PresheafOfModules.{max m r} (R' ⋙ forget₂ CommRingCat RingCat))

open scoped ChangeOfRings in
/-- **Cartesianness transported across a pushout square of rings.** Additive identifications
`N(wᵢ) ≃ M(xᵢ)`, semilinear along ring maps `αᵢ : R(wᵢ) ⟶ R'(xᵢ)` forming a pushout square with the
restrictions along `φ` and `ψ`, and compatible with the restriction maps, carry cartesianness of
`M` along `ψ` to cartesianness of `N` along `φ`. -/
theorem bijective_restrictionBaseChange_of_pushout_transport
    {w₁ w₂ : C} (φ : w₁ ⟶ w₂) {x₁ x₂ : D} (ψ : x₁ ⟶ x₂)
    (α₁ : R.obj (op w₁) ⟶ R'.obj (op x₁)) (α₂ : R.obj (op w₂) ⟶ R'.obj (op x₂))
    (hpo : IsPushout (R.map φ.op) α₂ α₁ (R'.map ψ.op))
    (e₁ : N.obj (op w₁) ≃+ M.obj (op x₁)) (e₂ : N.obj (op w₂) ≃+ M.obj (op x₂))
    (he₁ : ∀ (c : R.obj (op w₁)) (n : N.obj (op w₁)), e₁ (c • n) = α₁.hom c • e₁ n)
    (he₂ : ∀ (c : R.obj (op w₂)) (n : N.obj (op w₂)), e₂ (c • n) = α₂.hom c • e₂ n)
    (hnat : ∀ n : N.obj (op w₂), e₁ (N.map φ.op n) = M.map ψ.op (e₂ n))
    (hM : Function.Bijective (restrictionBaseChange M ψ.op)) :
    Function.Bijective (restrictionBaseChange N φ.op) := by
  let algB : Algebra (R.obj (op w₂)) (R.obj (op w₁)) := (R.map φ.op).hom.toAlgebra
  let algA : Algebra (R.obj (op w₂)) (R'.obj (op x₂)) := α₂.hom.toAlgebra
  let algD : Algebra (R.obj (op w₂)) (R'.obj (op x₁)) := (R.map φ.op ≫ α₁).hom.toAlgebra
  let algAD : Algebra (R'.obj (op x₂)) (R'.obj (op x₁)) := (R'.map ψ.op).hom.toAlgebra
  let algBD : Algebra (R.obj (op w₁)) (R'.obj (op x₁)) := α₁.hom.toAlgebra
  let modA : Module (R.obj (op w₂)) (M.obj (op x₂)) := Module.compHom _ α₂.hom
  let : IsScalarTower (R.obj (op w₂)) (R'.obj (op x₂)) (R'.obj (op x₁)) := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    show (R.map φ.op ≫ α₁).hom c = (α₂ ≫ R'.map ψ.op).hom c
    rw [hpo.w]
  let : IsScalarTower (R.obj (op w₂)) (R'.obj (op x₂)) (M.obj (op x₂)) :=
    ⟨fun c a z => mul_smul _ _ _⟩
  let e : (R'.obj (op x₂)) ⊗[R.obj (op w₂)] (R.obj (op w₁)) ≃ₗ[R.obj (op w₂)] R'.obj (op x₁) :=
    (TensorProduct.comm _ _ _).trans
      (CommRingCat.pushoutTensorLinearEquiv _ _ _ _ (R.map φ.op) α₂ α₁ (R'.map ψ.op) hpo)
  have he : ∀ (a : R'.obj (op x₂)) (b : R.obj (op w₁)),
      e (a ⊗ₜ b) = algebraMap (R'.obj (op x₂)) (R'.obj (op x₁)) a *
        algebraMap (R.obj (op w₁)) (R'.obj (op x₁)) b := by
    intro a b
    show CommRingCat.pushoutTensorLinearEquiv _ _ _ _ (R.map φ.op) α₂ α₁ (R'.map ψ.op) hpo
      (b ⊗ₜ a) = _
    rw [CommRingCat.pushoutTensorLinearEquiv_tmul]
    exact mul_comm _ _
  let κ : (R'.obj (op x₁)) ⊗[R'.obj (op x₂)] (M.obj (op x₂)) →ₗ[R'.obj (op x₁)]
      M.obj (op x₁) := (restrictionBaseChange M ψ.op).hom
  let ε := Module.Descent.pushoutBaseChangeEquiv e he (M := M.obj (op x₂))
  let g : (R.obj (op w₁)) ⊗[R.obj (op w₂)] (M.obj (op x₂)) →+ M.obj (op x₁) :=
    κ.toAddMonoidHom.comp ε.toLinearMap.toAddMonoidHom
  let f : (R.obj (op w₁)) ⊗[R.obj (op w₂)] (N.obj (op w₂)) →+ N.obj (op w₁) :=
    (restrictionBaseChange N φ.op).hom.toAddMonoidHom
  let eL : N.obj (op w₂) ≃ₗ[R.obj (op w₂)] M.obj (op x₂) :=
    { e₂ with map_smul' := he₂ }
  have key : ∀ (b : R.obj (op w₁)) (n : N.obj (op w₂)),
      g (b ⊗ₜ eL n) = e₁ (f (b ⊗ₜ n)) := by
    intro b n
    have h₁ : f (b ⊗ₜ n) = b • N.map φ.op n :=
      restrictionBaseChange_tmul N φ.op b n
    have h₂ : g (b ⊗ₜ eL n) = κ (α₁.hom b ⊗ₜ e₂ n) :=
      congrArg κ (Module.Descent.pushoutBaseChangeEquiv_tmul e he b (e₂ n))
    have h₃ : κ (α₁.hom b ⊗ₜ e₂ n) = α₁.hom b • M.map ψ.op (e₂ n) :=
      restrictionBaseChange_tmul M ψ.op (α₁.hom b) (e₂ n)
    rw [h₂, h₃, h₁]
    exact ((he₁ b (N.map φ.op n)).trans (congrArg (α₁.hom b • ·) (hnat n))).symm
  exact (TensorProduct.bijective_iff_of_tmul_comm eL e₁ key).2 (hM.comp ε.bijective)

end Stacks.PresheafOfModules
