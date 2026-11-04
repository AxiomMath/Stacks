module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Vanishing in a filtered colimit of abelian groups

An element of a term of a filtered diagram of abelian groups which becomes zero in the colimit
is already zero in some later term.

## Main definitions

No new definitions are introduced.

## Main results

* `CategoryTheory.Limits.Concrete.addCommGrpCat_colimit_rep_eq_zero`: the `AddCommGrpCat`
  analogue of Mathlib's `CategoryTheory.Limits.Concrete.colimit_rep_eq_zero`, which is stated
  only for `ModuleCat`.

## Implementation notes

The proof is Mathlib's proof for `ModuleCat`: comparing the representative with the
representative `0` of the zero element through
`CategoryTheory.Limits.Concrete.colimit_rep_eq_iff_exists`. Nothing here is special to
`AddCommGrpCat` beyond the objects having a zero and the morphisms preserving it; Mathlib's
file records that a general version over `HasForget₂ C (ModuleCat R)` is still missing, which
is why this copy exists.

The index category is only assumed `Category.{r} J` with `J : Type w`; the diagram takes values
in `AddCommGrpCat.{max t w}`, as in Mathlib's statement, so that the filtered colimit exists in
the same universe. A diagram indexed by a large category has to be replaced by a cofinal small
one before this applies.

## References

* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
-/

@[expose] public section

universe t w r

open CategoryTheory

namespace CategoryTheory.Limits.Concrete

/-- If an element `x` of the `j`-th term of a filtered diagram of abelian groups is sent to `0`
in the colimit, then there is a map `i : j ⟶ j'` with `F.map i x = 0`. -/
theorem addCommGrpCat_colimit_rep_eq_zero {J : Type w} [Category.{r} J]
    (F : J ⥤ AddCommGrpCat.{max t w}) [PreservesColimit F (forget AddCommGrpCat)] [IsFiltered J]
    [HasColimit F] (j : J) (x : F.obj j) (hx : colimit.ι F j x = 0) :
    ∃ (j' : J) (i : j ⟶ j'), F.map i x = 0 := by
  rw [show 0 = colimit.ι F j 0 by simp, colimit_rep_eq_iff_exists] at hx
  obtain ⟨j', i, y, g⟩ := hx
  exact ⟨j', i, g ▸ by simp⟩

end CategoryTheory.Limits.Concrete

end
