module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.CategoryTheory.Linear.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Graded categories

A category graded over a ring `R` is an `R`-linear category each of whose morphism modules is
decomposed into integer-indexed homogeneous pieces, with the identities homogeneous of degree
zero and composition adding degrees. Forgetting the differential of a differential graded
category leaves exactly this structure.

## Main definitions

* `CategoryTheory.GradedCategory`: the class of categories graded over a ring.

## Implementation notes

The underlying additive and `R`-linear structure is Mathlib's `CategoryTheory.Linear`. For each
pair of objects the homogeneous pieces are submodules equipped with a
`DirectSum.Decomposition`, so their direct sum really is the whole morphism module, not merely a
chosen family of homogeneous submodules. The two remaining fields express that identities have
degree zero and that composition preserves the grading; bilinearity of composition comes from
the linear structure.

## References

* [Stacks Project, Tag 09L2](https://stacks.math.columbia.edu/tag/09L2)
-/

@[expose] public section

namespace CategoryTheory

universe w v u

/-- A category graded over a ring `R`: every morphism module is the direct sum of its
integer-indexed homogeneous pieces, identities are homogeneous of degree zero, and composition
of morphisms of degrees `m` and `n` has degree `m + n`. -/
@[stacks 09L2]
class GradedCategory (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C]
    extends Linear R C where
  /-- The degree-`n` homogeneous morphisms from `X` to `Y`. -/
  grade (X Y : C) (n : ℤ) : Submodule R (X ⟶ Y)
  /-- Every morphism is uniquely a finite sum of homogeneous morphisms. -/
  decomposition (X Y : C) : DirectSum.Decomposition (grade X Y)
  /-- Identity morphisms have degree zero. -/
  id_mem (X : C) : 𝟙 X ∈ grade X X 0
  /-- Composition of homogeneous morphisms adds their degrees. -/
  comp_mem {X Y Z : C} {m n : ℤ} {g : Y ⟶ Z} {f : X ⟶ Y} :
    g ∈ grade Y Z m → f ∈ grade X Y n → f ≫ g ∈ grade X Z (m + n)

attribute [instance_reducible, instance] GradedCategory.decomposition

end CategoryTheory
