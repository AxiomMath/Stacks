module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# An object of the unbounded derived category is zero iff all its homology vanishes

Let `C` be an abelian category admitting a derived category. An object `X` of
`DerivedCategory C` is a zero object exactly when `Hⁿ(X) = 0` for every `n : ℤ`.

This is the object-level form of Mathlib's `DerivedCategory.isIso_iff`, which says that a
morphism of `DerivedCategory C` is an isomorphism exactly when it induces an isomorphism on
every homology object: an object is zero exactly when the unique morphism from it to a zero
object is an isomorphism, and the homology functors carry that morphism to the unique morphism
to an object that is again zero.

## Main results

* `CategoryTheory.Limits.isZero_iff_isIso_zero`: an object is zero iff the zero morphism from it
  to the zero object is an isomorphism.
* `DerivedCategory.isZero_iff_forall_isZero_homology`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u v' u'

/-- An object of a category with a zero object is zero precisely when the zero morphism from
it to the zero object is an isomorphism. -/
theorem CategoryTheory.Limits.isZero_iff_isIso_zero {D : Type u'} [Category.{v'} D]
    [HasZeroMorphisms D] [HasZeroObject D] (Y : D) : IsZero Y ↔ IsIso (0 : Y ⟶ 0) :=
  ⟨fun h => h.isIso (isZero_zero D) _,
    fun _ => IsZero.of_iso (isZero_zero D) (asIso (0 : Y ⟶ 0))⟩

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- An object of the unbounded derived category of an abelian category is a zero object
precisely when all of its homology objects are zero. -/
theorem isZero_iff_forall_isZero_homology (X : DerivedCategory C) :
    IsZero X ↔ ∀ n : ℤ, IsZero ((homologyFunctor C n).obj X) := by
  rw [isZero_iff_isIso_zero, isIso_iff]
  refine forall_congr' fun n => ?_
  rw [(homologyFunctor C n).map_zero]
  have hZ : IsZero ((homologyFunctor C n).obj (0 : DerivedCategory C)) :=
    (homologyFunctor C n).map_isZero (isZero_zero _)
  exact ⟨fun _ => IsZero.of_iso hZ (asIso (0 : (homologyFunctor C n).obj X ⟶ _)),
    fun h => h.isIso hZ 0⟩

end DerivedCategory

end
