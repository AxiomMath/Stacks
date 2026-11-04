module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Thickenings.Universal

/-!
# A morphism with a universal first-order thickening is formally unramified

If a morphism of schemes `h : Z ⟶ X` has a universal first-order thickening, then `h` is formally
unramified; this is the converse of the existence of a universal first-order thickening for a
formally unramified morphism. In particular the diagonal of such a morphism is an open immersion as
soon as the morphism is locally of finite type.

## Main results

* `Stacks.Thickenings.formallyUnramified_of_isUniversalFirstOrderThickening`: a morphism with
  a universal first-order thickening is formally unramified.
* `Stacks.Thickenings.isOpenImmersion_diagonal_of_isUniversalFirstOrderThickening`: the
  diagonal of such a morphism is an open immersion when the morphism is locally of finite type.

## References

* [Stacks Project, Tag 04F2](https://stacks.math.columbia.edu/tag/04F2)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- A morphism of schemes with a universal first-order thickening is formally unramified. -/
theorem formallyUnramified_of_isUniversalFirstOrderThickening {Z X Z' : Scheme.{u}} {h : Z ⟶ X}
    {i : Z ⟶ Z'} {h' : Z' ⟶ X} (hi : IsUniversalFirstOrderThickening h i h') :
    FormallyUnramified h := by
  have : IsClosedImmersion i := hi.isFirstOrderThickening.1
  refine FormallyUnramified.of_hom_ext h fun R A φ hφ hφ₂ g₁ g₂ hg hgh => ?_
  have hlift := hi.existsUnique_lift (Spec.map φ)
    (Stacks.Smooth.isFirstOrderThickening_specMap φ hφ hφ₂) (Spec.map φ ≫ g₁) (g₁ ≫ h)
    (Category.assoc _ _ _).symm
  refine (cancel_mono i).mp (hlift.unique ⟨(Category.assoc _ _ _).symm, ?_⟩ ⟨?_, ?_⟩)
  · rw [Category.assoc, hi.inclusion_toBase]
  · rw [← Category.assoc, ← hg, Category.assoc]
  · rw [Category.assoc, hi.inclusion_toBase, ← hgh]

/-- The diagonal of a morphism with a universal first-order thickening which is locally of
finite type is an open immersion. -/
theorem isOpenImmersion_diagonal_of_isUniversalFirstOrderThickening {Z X Z' : Scheme.{u}}
    {h : Z ⟶ X} {i : Z ⟶ Z'} {h' : Z' ⟶ X} (hi : IsUniversalFirstOrderThickening h i h')
    [LocallyOfFiniteType h] : IsOpenImmersion (pullback.diagonal h) :=
  have := formallyUnramified_of_isUniversalFirstOrderThickening hi
  inferInstance

end Stacks.Thickenings

end
