module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# A nonzero object of the derived category has a nonzero cohomology object

An object of the derived category is zero exactly when all of its cohomology objects are zero.
This is `CategoryTheory.DerivedCategory.isIso_iff` — a morphism of the derived category is
invertible exactly when it is on every cohomology object — read at the zero endomorphism.

The contrapositive is the first line of the argument of [Stacks, Tag 0BQR]: a nonzero object of
`D_QCoh(𝒪_X)` has a nonzero cohomology *sheaf*, which is where the chart argument of that tag
starts.

## Main results

* `StacksDraft.DerivedCategoryHomology.isZero_iff_isIso_zero`: a zero object is one whose zero
  endomorphism is invertible.
* `StacksDraft.DerivedCategoryHomology.isZero_iff_forall_isZero_homology`.
* `StacksDraft.DerivedCategoryHomology.exists_nonzero_homology`.

## Implementation notes

`isZero_iff_isIso_zero` is stated over a category with zero morphisms and **not** over an abelian
one, because it is applied to an object of `DerivedCategory C`, which is triangulated and not
abelian.

The two derived-category statements carry a free `HasDerivedCategory` binder, so they hold at any
chosen model. This matters for [Stacks, Tag 0BQR], whose inputs are split between the locally
small model — where `D_QCoh(𝒪_X)` and [Stacks, Tag 08DB] live — and
`CategoryTheory.HasDerivedCategory.standard`, where the hypercohomology identification of
[Stacks, Tag 08JA] lives.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace StacksDraft.DerivedCategoryHomology

section ZeroMorphisms

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- **A zero object is one whose zero endomorphism is invertible.** This is
`CategoryTheory.Limits.isIsoZeroSelfEquiv` together with the characterisation of a zero object by
`𝟙 = 0`. -/
theorem isZero_iff_isIso_zero (Z : C) : IsZero Z ↔ IsIso (0 : Z ⟶ Z) :=
  ⟨fun h => (isIsoZeroSelfEquiv Z).symm ((IsZero.iff_id_eq_zero Z).1 h),
    fun h => (IsZero.iff_id_eq_zero Z).2 (isIsoZeroSelfEquiv Z h)⟩

end ZeroMorphisms

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- **An object of the derived category is zero exactly when all its cohomology objects are.**
`CategoryTheory.DerivedCategory.isIso_iff` at the zero endomorphism. -/
theorem isZero_iff_forall_isZero_homology (Z : DerivedCategory C) :
    IsZero Z ↔ ∀ p : ℤ, IsZero ((DerivedCategory.homologyFunctor C p).obj Z) := by
  rw [isZero_iff_isIso_zero, DerivedCategory.isIso_iff]
  refine forall_congr' fun p => ?_
  rw [isZero_iff_isIso_zero ((DerivedCategory.homologyFunctor C p).obj Z),
    Functor.map_zero (DerivedCategory.homologyFunctor C p) Z Z]

/-- **A nonzero object of the derived category has a nonzero cohomology object.** -/
theorem exists_nonzero_homology (Z : DerivedCategory C) (hZ : ¬ IsZero Z) :
    ∃ p : ℤ, ¬ IsZero ((DerivedCategory.homologyFunctor C p).obj Z) := by
  by_contra h
  exact hZ ((isZero_iff_forall_isZero_homology Z).2
    fun p => not_not.mp fun hp => h ⟨p, hp⟩)

end Derived

end StacksDraft.DerivedCategoryHomology

end
