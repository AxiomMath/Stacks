module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Special cocontinuous functors

A functor between sites is special cocontinuous if it is cocontinuous and makes its source a dense
subsite of its target.

## Main definitions

* `IsSpecialCocontinuous`: the property of a functor `u : C ⥤ D` between sites of being a *special
  cocontinuous functor*.

## References

* [Stacks Project, Tag 03CG](https://stacks.math.columbia.edu/tag/03CG)
-/

@[expose] public section

open CategoryTheory

/-- A functor `u : C ⥤ D` from a site `(C, J)` to a site `(D, K)` is a *special cocontinuous
functor* if it is cocontinuous and makes `(C, J)` a dense subsite of `(D, K)`. -/
@[stacks 03CG]
def IsSpecialCocontinuous {C : Type*} [Category C] {D : Type*} [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) : Prop :=
  Functor.IsCocontinuous u J K ∧ u.IsDenseSubsite J K
