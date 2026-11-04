module

public import Mathlib.CategoryTheory.HomCongr
public import StacksFrontier.Homology.DerivedCategory.ModelComparison

/-!
# Bijectivity of composition does not depend on the model of the derived category

For two choices `h₁ h₂` of the derived category of an abelian category `C`, a morphism of
complexes `g : A ⟶ B` and a complex `K`, composing with `Q.map g` is bijective on morphisms out
of `Q.obj K` in one model if and only if it is in the other. The two Hom maps are conjugate under
the comparison equivalence `StacksDraft.DerivedModel.modelEquiv h₁ h₂`, which commutes with the
localization functors (`StacksDraft.DerivedModel.modelCompQIso`).

## Main results

* `StacksDraft.DerivedModel.bijective_comp_Q_map_iff`: the transfer statement.
-/

@[expose] public section

open CategoryTheory

universe u v w z

namespace StacksDraft.DerivedModel

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Bijectivity of composition with `Q.map g` on morphisms out of `Q.obj K` is independent of
the model of the derived category.** -/
theorem bijective_comp_Q_map_iff (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)
    (K : CochainComplex C ℤ) {A B : CochainComplex C ℤ} (g : A ⟶ B) :
    Function.Bijective (fun x : (@DerivedCategory.Q C _ _ h₁).obj K ⟶
        (@DerivedCategory.Q C _ _ h₁).obj A => x ≫ (@DerivedCategory.Q C _ _ h₁).map g) ↔
      Function.Bijective (fun x : (@DerivedCategory.Q C _ _ h₂).obj K ⟶
        (@DerivedCategory.Q C _ _ h₂).obj A => x ≫ (@DerivedCategory.Q C _ _ h₂).map g) := by
  let α := modelCompQIso h₁ h₂
  let Θ : ∀ L : CochainComplex C ℤ, ((@DerivedCategory.Q C _ _ h₁).obj K ⟶
      (@DerivedCategory.Q C _ _ h₁).obj L) ≃ ((@DerivedCategory.Q C _ _ h₂).obj K ⟶
      (@DerivedCategory.Q C _ _ h₂).obj L) := fun L =>
    (modelEquiv h₁ h₂).fullyFaithfulFunctor.homEquiv.trans ((α.app K).homCongr (α.app L))
  have heq : (fun x : (@DerivedCategory.Q C _ _ h₁).obj K ⟶
        (@DerivedCategory.Q C _ _ h₁).obj A => x ≫ (@DerivedCategory.Q C _ _ h₁).map g) =
      (Θ B).symm ∘ (fun x : (@DerivedCategory.Q C _ _ h₂).obj K ⟶
        (@DerivedCategory.Q C _ _ h₂).obj A => x ≫ (@DerivedCategory.Q C _ _ h₂).map g) ∘
          Θ A := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, Equiv.eq_symm_apply]
    simp only [Θ, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply, Iso.homCongr_apply,
      Functor.map_comp, Category.assoc]
    congr 2
    exact α.hom.naturality g
  rw [heq, Equiv.comp_bijective, Equiv.bijective_comp]

end StacksDraft.DerivedModel
