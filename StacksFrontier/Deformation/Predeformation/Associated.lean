module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# The functor associated to a predeformation category

The functor of isomorphism classes `isomorphismClasses` associated to a predeformation category
is a predeformation functor.

## Main results

* `Deformation.isPredeformationFunctor_isomorphismClasses`: the functor of isomorphism classes
  associated to a predeformation category is a predeformation functor.

## References

* [Stacks Project, Tag 06GT](https://stacks.math.columbia.edu/tag/06GT)
-/

@[expose] public section

namespace Deformation

/-! ### The associated functor of a predeformation category -/

section
open CategoryTheory
open CategoryTheory.Functor
universe u v w u₁ v₁

/-- The associated functor of isomorphism classes of a predeformation category is a
predeformation functor. -/
@[stacks 06GT]
public theorem isPredeformationFunctor_isomorphismClasses
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{v₁, u₁}
      (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p) :
    IsPredeformationFunctor
      (isomorphismClasses 𝓕 h𝓕.cofibered) := by
  obtain ⟨e⟩ := h𝓕.specialFiber
  have hall (x y : Fiber 𝓕.p (residueFieldObject Λ k)) : Nonempty (x ≅ y) :=
    ⟨e.unitIso.app x ≪≫
      e.inverse.mapIso (eqToIso (Subsingleton.elim (e.functor.obj x) (e.functor.obj y))) ≪≫
      (e.unitIso.app y).symm⟩
  change Nonempty (Unique ((isomorphismClassesData 𝓕 h𝓕.cofibered).classes.obj
    (residueFieldObject Λ k)))
  rw [(isomorphismClassesData 𝓕 h𝓕.cofibered).classes_eq (residueFieldObject Λ k)]
  exact ⟨⟨⟨Quotient.mk _ (e.inverse.obj (Discrete.mk PUnit.unit))⟩,
    fun q => Quotient.inductionOn q fun x => Quotient.sound (hall x _)⟩⟩

end

end Deformation
