module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.ExtendingFunctorsCategories.LeftExactness
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.ExtendingFunctorsCategories.RightExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the extension from finite modules

For Noetherian commutative rings `A` and `B`, an exact functor between the categories of finite
modules has an exact filtered-colimit-preserving extension to all modules. This is the two
halves of exactness put together: left exactness and right exactness of the extension are
proved separately.

## Main results

* `ModuleCat.FGFilteredColimitExtension.exactFunctor`: the extension of an exact functor is
  exact.

## Implementation notes

Exactness is Mathlib's `CategoryTheory.exactFunctor`, which combines preservation of finite
limits with preservation of finite colimits. The result applies to an arbitrary
filtered-colimit extension together with its specified identification on the finite modules.

## References

* [Stacks Project, Tag 0GP9](https://stacks.math.columbia.edu/tag/0GP9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat

/-- **Stacks Project, Tag 0GP9.** A filtered-colimit extension of an exact functor between
finite module categories over Noetherian rings is exact. -/
@[stacks 0GP9 "exactness"]
theorem FGFilteredColimitExtension.exactFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type w) [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{v} A ⥤ FGModuleCat.{v} B)
    (E : FGFilteredColimitExtension.{u, v, w} A B F)
    (hF : exactFunctor (FGModuleCat.{v} A) (FGModuleCat.{v} B) F) :
    exactFunctor (ModuleCat.{v} A) (ModuleCat.{v} B) E.functor := by
  rw [exactFunctor_iff] at hF ⊢
  let := hF.1
  let := hF.2
  exact ⟨fgFilteredColimitExtension_preservesFiniteLimits A B F E,
    FGFilteredColimitExtension.preservesFiniteColimits A B E⟩

end ModuleCat
