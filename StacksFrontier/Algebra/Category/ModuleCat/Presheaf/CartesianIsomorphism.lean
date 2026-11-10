module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianComposition

/-!
# Cartesian presheaves of modules over isomorphisms and isomorphic arrows

Let `R` be a presheaf of commutative rings on a category `C` and `M` a presheaf of modules over
its underlying presheaf of rings. This file proves that `M` is cartesian over every isomorphism
of `Cᵒᵖ` (`Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_isIso`): over an isomorphism the
ring map is an isomorphism, so every element of `R Y ⊗[R X] M X` is of the form `1 ⊗ x`, and the
comparison sends `1 ⊗ x` to the restriction of `x`, which is a bijection. Consequently being
cartesian over a morphism depends only on its isomorphism class as an arrow
(`Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_arrow_iso`), by the stability of being
cartesian under composition.

## Main results

* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_isIso`
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_arrow_iso`
-/

@[expose] public section

open CategoryTheory
open scoped ChangeOfRings

universe u v r m

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
  (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))

/-- **A presheaf of modules is cartesian over every isomorphism.** -/
theorem isIso_restrictionBaseChange_of_isIso {X Y : Cᵒᵖ} (h : X ⟶ Y) [IsIso h] :
    IsIso (restrictionBaseChange.{u, v, r, m} M h) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map h).hom
  have hone : ∀ t : (ModuleCat.extendScalars (R.map h).hom).obj (M.obj X),
      ∃ x : M.obj X, t = (1 : R.obj Y) ⊗ₜ[R.obj X, (R.map h).hom] x := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul s x =>
      obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (R.map h)).2 s
      exact ⟨a • x, (congrArg (fun s : R.obj Y => s ⊗ₜ[R.obj X, (R.map h).hom] x)
        (mul_one ((R.map h).hom a)).symm).trans
          (TensorProduct.smul_tmul a (1 : R.obj Y) x)⟩
    | add t t' ht ht' =>
      obtain ⟨x, rfl⟩ := ht
      obtain ⟨x', rfl⟩ := ht'
      exact ⟨x + x', (TensorProduct.tmul_add _ _ _).symm⟩
  have hinv : ∀ {A B : Cᵒᵖ} (g : A ⟶ B) (g' : B ⟶ A), g ≫ g' = 𝟙 A → ∀ x : M.obj A,
      M.map g' (M.map g x) = x := fun g g' hg x =>
    (M.map_comp_apply g g' x).symm.trans ((M.congr_map_apply hg x).trans
      (by rw [M.map_id]; rfl))
  refine ⟨fun t t' htt' => ?_, fun y => ⟨(1 : R.obj Y) ⊗ₜ[R.obj X, (R.map h).hom] M.map (inv h) y,
    (restrictionBaseChange_one_tmul M h _).trans (hinv _ _ (IsIso.inv_hom_id h) y)⟩⟩
  obtain ⟨x, rfl⟩ := hone t
  obtain ⟨x', rfl⟩ := hone t'
  have e := ((restrictionBaseChange_one_tmul M h x).symm.trans htt').trans
    (restrictionBaseChange_one_tmul M h x')
  rw [← hinv _ _ (IsIso.hom_inv_id h) x, ← hinv _ _ (IsIso.hom_inv_id h) x', e]

/-- **Being cartesian over a morphism depends only on its isomorphism class as an arrow.** If
`f ≫ j = i ≫ f'` with `i` and `j` isomorphisms, `M` is cartesian over `f` as soon as it is
cartesian over `f'`. -/
theorem isIso_restrictionBaseChange_of_arrow_iso {X Y X' Y' : Cᵒᵖ} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (i : X ⟶ X') (j : Y ⟶ Y') [IsIso i] [IsIso j] (w : f ≫ j = i ≫ f')
    (h : IsIso (restrictionBaseChange.{u, v, r, m} M f')) :
    IsIso (restrictionBaseChange.{u, v, r, m} M f) := by
  have h₂ : IsIso (restrictionBaseChange.{u, v, r, m} M ((f ≫ j) ≫ inv j)) := by
    rw [w]
    exact isIso_restrictionBaseChange_comp M (i ≫ f') (inv j)
      (isIso_restrictionBaseChange_comp M i f' (isIso_restrictionBaseChange_of_isIso M i) h)
      (isIso_restrictionBaseChange_of_isIso M (inv j))
  rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h₂

end Stacks.PresheafOfModules

end
