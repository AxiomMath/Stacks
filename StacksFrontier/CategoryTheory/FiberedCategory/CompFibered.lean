module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksFrontier.CategoryTheory.FiberedCategory.StronglyCartesianComp

/-!
# A composite of fibred functors is fibred (Stacks 09WV)

Mathlib's `Functor.IsFibered p` says that every base morphism into the image of an object
admits a strongly cartesian lift along `p`.  Stacks 09WV asserts that this property is
stable under composition: if `F : A ⥤ B` and `G : B ⥤ C` are fibred, so is `F ⋙ G`.

## Main results

* `CategoryTheory.Functor.IsFibered.comp_functor`: a composite of fibred functors is fibred.

## Implementation notes

The name is `comp_functor` rather than `comp` because Mathlib's `Functor.IsFibered.comp` is a
different statement, about composing morphisms inside a single fibred functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {A B C : Type*} [Category A] [Category B] [Category C]

/-- A composite of fibred functors is fibred: if `F : A ⥤ B` and `G : B ⥤ C` are fibred, then so
is `F ⋙ G`. -/
@[stacks 09WV]
theorem IsFibered.comp_functor (F : A ⥤ B) (G : B ⥤ C)
    [F.IsFibered] [G.IsFibered] : (F ⋙ G).IsFibered := by
  refine IsFibered.of_exists_isStronglyCartesian fun a R f ↦ ?_
  obtain ⟨b, φ, hGc⟩ := IsPreFibered.exists_isCartesian' (p := G) (a := F.obj a) f
  obtain ⟨a', θ, hFc⟩ := IsPreFibered.exists_isCartesian' (p := F) (a := a) φ
  have : G.IsCartesian f φ := hGc
  have : F.IsCartesian φ θ := hFc
  have := IsFibered.isStronglyCartesian_of_isCartesian G f φ
  have := IsFibered.isStronglyCartesian_of_isCartesian F φ θ
  exact ⟨a', θ, IsStronglyCartesian.comp_functor F G f φ θ⟩

end CategoryTheory.Functor
