module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# The elementwise filtered colimit of rings is a colimit in `CommRingCat`

`Stacks.IsStagesColimit` records, elementwise, that a type `T` is the filtered colimit of a system
of stages `G i` along given transition maps and maps to `T`. When the stages and `T` are
commutative rings, the transition maps form a functor `R : I ⥤ CommRingCat` on a directed
nonempty preorder and the maps to `T` form a cocone `c`, the elementwise statement says exactly
that `c` is a colimit cocone: its image in types is a filtered colimit (the two clauses are the
recognition criterion `CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'`), and the
forgetful functor reflects filtered colimits.

This is the form in which descent statements over a filtered colimit of rings (such as the
descent of perfect complexes, Stacks 0BC7) consume the ring of global functions of a limit of
algebraic spaces (Stacks 07SI).

## Main results

* `Stacks.IsStagesColimit.nonempty_isColimit`.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 0BC7](https://stacks.math.columbia.edu/tag/0BC7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks

/-- **An elementwise filtered colimit of commutative rings is a colimit in `CommRingCat`.** For a
functor `R` from a directed nonempty preorder to commutative rings and a cocone `c` on it, if
`c.pt` is the filtered colimit of the `R i` elementwise (`Stacks.IsStagesColimit` along `R.map`
and the legs of `c`), then `c` is a colimit cocone. -/
theorem IsStagesColimit.nonempty_isColimit {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (h : IsStagesColimit (G := fun i => R.obj i) (T := c.pt)
      (fun _ _ hij x => R.map (homOfLE hij) x) (fun i x => c.ι.app i x)) :
    Nonempty (IsColimit c) := by
  have : ReflectsColimitsOfShape I (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{u}) ?_⟩
  refine Types.FilteredColimit.isColimitOf' (R ⋙ forget CommRingCat.{u}) _ (fun x => ?_)
    (fun i x y hxy => ?_)
  · obtain ⟨i, s, hs⟩ := h.exists_stage x
    exact ⟨i, s, hs.symm⟩
  · obtain ⟨j, hij, hj⟩ := h.exists_trans_eq i x y hxy
    exact ⟨j, homOfLE hij, hj⟩

end Stacks
