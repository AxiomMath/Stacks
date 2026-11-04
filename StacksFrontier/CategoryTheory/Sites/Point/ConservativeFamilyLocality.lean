module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Point.Conservative
public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamily

/-!
# Having a conservative family of points is a local condition

Stacks 06UL says that a site has enough points as soon as some family of objects covers the
final object and each of the localizations at those objects has enough points. Mathlib's
`CategoryTheory.GrothendieckTopology.hasEnoughPoints_of_coversTop` states this for
`CategoryTheory.GrothendieckTopology.HasEnoughPoints`, whose conservative family is required
to be small; the source's own notion, which asks only for a conservative family, is
`CategoryTheory.GrothendieckTopology.HasConservativeFamily`, and the same statement for it is
proved here.

## Main results

* `CategoryTheory.GrothendieckTopology.HasConservativeFamily.of_coversTop`: Stacks 06UL for
  `CategoryTheory.GrothendieckTopology.HasConservativeFamily`.

## Implementation notes

The conservativity step, `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.of_coversTop`,
asks for no smallness of the families it is given, so dropping the smallness conjunct from both
sides costs nothing: the families are extracted from the hypothesis by
`CategoryTheory.GrothendieckTopology.hasConservativeFamily_iff_exists` and the resulting
pushed-forward family is handed back through the same equivalence. The index type of the
covering family is likewise unrestricted, whereas Mathlib's version needs it to be small.

## References

* [Stacks Project, Tag 06UL](https://stacks.math.columbia.edu/tag/06UL)
* [Stacks Project, Tag 00YK](https://stacks.math.columbia.edu/tag/00YK)
-/

@[expose] public section

universe w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  {I : Type*} (Ui : I → C)

/-- **Stacks 06UL** for `CategoryTheory.GrothendieckTopology.HasConservativeFamily`. If a family
of objects covers the final object and each localization at a member of the family has a
conservative family of points, then so does the site itself. -/
@[stacks 06UL]
theorem HasConservativeFamily.of_coversTop (hU : J.CoversTop Ui)
    (hP : ∀ i, (J.over (Ui i)).HasConservativeFamily.{w}) :
    J.HasConservativeFamily.{w} := by
  choose P hP using fun i ↦ (hasConservativeFamily_iff_exists (J.over (Ui i))).1 (hP i)
  exact (hasConservativeFamily_iff_exists J).2
    ⟨pointsOfLocalizations Ui P,
      ObjectProperty.IsConservativeFamilyOfPoints.of_coversTop Ui P hU hP⟩

end CategoryTheory.GrothendieckTopology

end
