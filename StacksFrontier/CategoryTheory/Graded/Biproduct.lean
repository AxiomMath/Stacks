module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Graded.Category

/-!
# Graded direct sums

A *graded direct sum* of two objects of a category graded over a ring `R` is a binary biproduct
whose two inclusions and two projections are homogeneous of degree zero. This is the direct-sum
axiom (A) for a differential graded category.

## Main definitions

* `CategoryTheory.GradedCategory.GradedBinaryBiproductData`: a chosen binary biproduct all four
  of whose structure morphisms are homogeneous of degree zero.

## Implementation notes

The underlying direct sum is Mathlib's `CategoryTheory.Limits.BinaryBiproductData`. Its binary
bicone has a point together with inclusions `inl`, `inr` and projections `fst`, `snd`; the four
added fields say precisely that these four morphisms lie in the degree-zero pieces of the
corresponding morphism modules.

## References

* [Stacks Project, Tag 09P2](https://stacks.math.columbia.edu/tag/09P2)
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.GradedCategory

universe w v u

/-- A chosen binary biproduct in a category graded over `R` whose inclusions and projections are
all homogeneous of degree zero. -/
@[stacks 09P2]
structure GradedBinaryBiproductData (R : Type w) [Ring R] {C : Type u} [Category.{v} C]
    [Preadditive C] [GradedCategory R C] (X Y : C) extends BinaryBiproductData X Y where
  /-- The inclusion of the first summand is homogeneous of degree zero. -/
  inl_mem : bicone.inl ∈ GradedCategory.grade (R := R) X bicone.pt 0
  /-- The inclusion of the second summand is homogeneous of degree zero. -/
  inr_mem : bicone.inr ∈ GradedCategory.grade (R := R) Y bicone.pt 0
  /-- The projection onto the first summand is homogeneous of degree zero. -/
  fst_mem : bicone.fst ∈ GradedCategory.grade (R := R) bicone.pt X 0
  /-- The projection onto the second summand is homogeneous of degree zero. -/
  snd_mem : bicone.snd ∈ GradedCategory.grade (R := R) bicone.pt Y 0

end CategoryTheory.GradedCategory
