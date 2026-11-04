module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of a monomorphism along a morphism that factors through it

If `m : A ⟶ D` is a monomorphism and `f : B ⟶ D` factors as `g ≫ m`, then the pullback of `m`
along `f` is `B` itself: the second projection `B ×_D A ⟶ B` is an isomorphism, with inverse the
lift of `g` and the identity.

## Main results

* `CategoryTheory.Limits.isIso_pullback_snd_of_factors_through_mono`.

## Implementation notes

The inverse is `pullback.lift g (𝟙 B)`.  That it is a section of the second projection is the
defining property of the lift; that it is a retraction needs
`pullback.snd m f ≫ g = pullback.fst m f`, which holds after composing with the monomorphism `m`
because both sides then become the cartesian square's own commutation.
-/

@[expose] public section

namespace CategoryTheory.Limits

/-- If a monomorphism `m` is a factor of `f`, the second projection of the pullback of `m` along
`f` is an isomorphism. -/
theorem isIso_pullback_snd_of_factors_through_mono {C : Type*} [Category C] {A B D : C}
    (m : A ⟶ D) (f : B ⟶ D) [Mono m] [HasPullback m f] (g : B ⟶ A) (hg : g ≫ m = f) :
    IsIso (pullback.snd m f) := by
  have hcond : g ≫ m = 𝟙 B ≫ f := by rw [hg, Category.id_comp]
  refine ⟨pullback.lift g (𝟙 B) hcond, ?_, ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← cancel_mono m,
        Category.assoc, hg, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · rw [pullback.lift_snd]

end CategoryTheory.Limits

end
