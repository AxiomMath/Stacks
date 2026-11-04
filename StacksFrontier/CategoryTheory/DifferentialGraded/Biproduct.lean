module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.DGCategory

/-!
# Direct sums in a differential graded category

A *differential graded direct sum* of two objects of a differential graded category is a direct
sum whose four structure morphisms are homogeneous of degree zero and closed. This is the
condition under which a direct sum in the differential graded category induces direct sums in
its category of complexes and in its homotopy category, and it is axiom (A) in the construction
of the triangulated structure on the homotopy category.

## Main definitions

* `DGCategory.BinaryBiproductData`: a chosen differential graded direct sum of two objects.

## Implementation notes

The five equations are the ordinary direct-sum identities for the inclusions and projections.
Degree zero is enforced by the morphism types, and the four closure fields enforce that each
structure morphism is a cocycle. The data are expressed directly in `DGCategory`, so clients can
use its homogeneous composition and differential without transporting through another category.

## References

* [Stacks Project, Tag 09P4](https://stacks.math.columbia.edu/tag/09P4)
-/

@[expose] public section

namespace DGCategory

universe u v w

/-- A direct sum of `X` and `Y` in a differential graded category, with all inclusions and
projections closed and homogeneous of degree zero. -/
@[stacks 09P4]
public structure BinaryBiproductData {R : Type w} [CommRing R] (A : DGCategory.{v, u} R)
    (X Y : A.Obj) where
  /-- The direct-sum object. -/
  pt : A.Obj
  /-- Inclusion of the first summand. -/
  inl : A.Hom X pt 0
  /-- Inclusion of the second summand. -/
  inr : A.Hom Y pt 0
  /-- Projection onto the first summand. -/
  fst : A.Hom pt X 0
  /-- Projection onto the second summand. -/
  snd : A.Hom pt Y 0
  /-- The first inclusion is closed. -/
  inl_closed : A.d inl = 0
  /-- The second inclusion is closed. -/
  inr_closed : A.d inr = 0
  /-- The first projection is closed. -/
  fst_closed : A.d fst = 0
  /-- The second projection is closed. -/
  snd_closed : A.d snd = 0
  /-- The first projection retracts the first inclusion. -/
  inl_fst : A.comp (by rfl : (0 : ℤ) + 0 = 0) fst inl = A.id X
  /-- The first projection kills the second inclusion. -/
  inr_fst : A.comp (by rfl : (0 : ℤ) + 0 = 0) fst inr = 0
  /-- The second projection kills the first inclusion. -/
  inl_snd : A.comp (by rfl : (0 : ℤ) + 0 = 0) snd inl = 0
  /-- The second projection retracts the second inclusion. -/
  inr_snd : A.comp (by rfl : (0 : ℤ) + 0 = 0) snd inr = A.id Y
  /-- The two summands jointly span the direct-sum object. -/
  fst_inl_add_snd_inr :
    A.comp (by rfl : (0 : ℤ) + 0 = 0) inl fst + A.comp (by rfl : (0 : ℤ) + 0 = 0) inr snd =
      A.id pt

end DGCategory
