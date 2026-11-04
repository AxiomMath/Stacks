module

public import StacksFrontier.CategoryTheory.Sites.Descent.OfBaseChange
public import StacksFrontier.CategoryTheory.Sites.Descent.SplitMemberDescent

/-!
# Effective descent along a family one member of which is a descent morphism

Let `F` be a pseudofunctor from `LocallyDiscrete Cᵒᵖ` to `Cat`, where `C` has fibre products,
and let `P` be a property of morphisms of `C` which is stable under base change and along each
of whose morphisms descent for `F` is effective. Then descent is effective along every family
`f i : X i ⟶ Y` one member `f i₀` of which has `P`.

This is the transitivity statement
`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_of_baseChange_unconditional`
applied to the
one-member family `{f i₀}`: every base change of the family `f` along a morphism factoring
through `f i₀` has a member with a section, so descent along it is effective by
`CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_pullback_snd_of_fac`.

## Main results

* `CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_of_mem`: descent along a family with
  a member having `P` is effective.

Nothing here carries a Stacks attribute: this is category-theoretic substrate for Stacks 0GFX.
-/

@[expose] public section

universe t v' u' v u

namespace CategoryTheory

open Limits

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

/-- **Effective descent along a family with a member having `P`.** Let `P` be stable under base
change, with descent effective along each one-member family `{h}` with `P h`. Then descent is
effective along every family one member of which has `P`. -/
theorem isEquivalence_toDescentData_of_mem (P : MorphismProperty C)
    [P.IsStableUnderBaseChange]
    (hP : ∀ ⦃X Y : C⦄ (h : X ⟶ Y), P h → (F.toDescentData (fun _ : Unit ↦ h)).IsEquivalence)
    {ι : Type t} {Y : C} {X : ι → C} (f : ∀ i, X i ⟶ Y) (i₀ : ι) (h₀ : P (f i₀)) :
    (F.toDescentData f).IsEquivalence := by
  refine isEquivalence_toDescentData_of_baseChange_unconditional f (fun _ : Unit ↦ f i₀)
    (hP _ h₀)
    (fun T t ↦ ?_)
    (fun _ ↦ DescentData.isEquivalence_toDescentData_pullback_snd_of_fac F f _ i₀ (𝟙 _)
      (Category.id_comp _))
    (fun _ _ ↦ ?_) (fun j k l _ _ x y hxy ↦ ?_)
  · have := hP _ (P.pullback_fst t (f i₀) h₀)
    exact ⟨.ofFullyFaithful _⟩
  · have := DescentData.isEquivalence_toDescentData_pullback_snd_of_fac F f
      (pullback.fst (f i₀) (f i₀) ≫ f i₀) i₀ (pullback.fst _ _) rfl
    exact ⟨.ofFullyFaithful _⟩
  · have := DescentData.isEquivalence_toDescentData_pullback_snd_of_fac F f
      (tripleProj₁ (fun _ : Unit ↦ f i₀) j k l ≫ f i₀) i₀ _ rfl
    exact eq_of_toDescentData_faithful _ hxy

end Pseudofunctor

end CategoryTheory

end
