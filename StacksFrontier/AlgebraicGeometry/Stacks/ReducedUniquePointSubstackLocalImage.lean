module

public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbeExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackExistence

/-!
# The reduced locally Noetherian one-point substack

Let `𝒵` be an algebraic stack over `S` which is reduced with a singleton space of points, that is,
which satisfies condition (1) of Stacks 06MN. Then there is a unique strictly full subcategory
`𝒵' ⊂ 𝒵` which is an algebraic stack satisfying the equivalent conditions of Stacks 06MP. This
file proves the existence, and existence and uniqueness together.

## Main results

* `AlgebraicGeometry.Stack.hasFullyFaithfulFinitePresentationPresentations`: the fully faithful
  presentation of a locally-of-finite-type field-valued point, in the spelling
  `AlgebraicGeometry.Stack.HasFullyFaithfulFinitePresentationPresentations`.
* `AlgebraicGeometry.Stack`
  `.exists_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint`: some
  strictly full subcategory of `𝒵` is such an algebraic stack.
* `AlgebraicGeometry.Stack`
  `.existsUnique_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint`:
  exactly one strictly full subcategory of `𝒵` is such an algebraic stack.

## Implementation notes

A strictly full subcategory of `𝒵` is an object property of `𝒵` closed under isomorphism, and the
predicate `AlgebraicGeometry.Stack.IsReducedLocallyNoetherianUniquePointSubstack` asks of it that
its full subcategory be an algebraic stack satisfying condition (2) of Stacks 06MP.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 06MN](https://stacks.math.columbia.edu/tag/06MN)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MR](https://stacks.math.columbia.edu/tag/06MR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fully faithful presentation of a locally-of-finite-type field-valued point.** An
algebraic stack over `S` receiving a 1-morphism from the algebraic stack of the spectrum of a field
which is locally of finite type receives a fully faithful 1-morphism from an algebraic stack
satisfying condition (2) of Stacks 06MP. -/
theorem hasFullyFaithfulFinitePresentationPresentations :
    HasFullyFaithfulFinitePresentationPresentations.{u, w} B S hS := by
  intro 𝒳 F f hlft _ _
  obtain ⟨𝒴, i, z, hfull, hfaithful, hlfp, hsurj, hflat, -⟩ :=
    hasFullyFaithfulFiniteTypeFieldPointPresentations.{u, w} B S hS 𝒳 F f hlft
  exact ⟨𝒴, i, hfull, hfaithful, F, z, hlfp, hsurj, hflat⟩

/-- Let `𝒵` be an algebraic stack over `S` which is reduced with a singleton space of points,
that is, which satisfies condition (1) of Stacks 06MN. Then some strictly full subcategory of `𝒵`
is an algebraic stack satisfying condition (2) of Stacks 06MP. -/
@[stacks 06MR "the existence of the substack, with the equivalent conditions of Stacks 06MP \
read as its condition (2)"]
theorem exists_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (h𝒵 : IsReducedWithUniquePoint B S hS 𝒵) :
    ∃ P : ObjectProperty 𝒵.val.val.obj,
      IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 P :=
  exists_isReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS
    (hasFullyFaithfulFinitePresentationPresentations.{u, w} B S hS) 𝒵 h𝒵

/-- Let `𝒵` be an algebraic stack over `S` which is reduced with a singleton space of points.
Then exactly one strictly full subcategory of `𝒵` is an algebraic stack satisfying condition (2)
of Stacks 06MP. -/
@[stacks 06MR "existence and uniqueness of the substack assembled, with the equivalent \
conditions of Stacks 06MP read as its condition (2)"]
theorem existsUnique_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (h𝒵 : IsReducedWithUniquePoint B S hS 𝒵) :
    ∃! P : ObjectProperty 𝒵.val.val.obj,
      IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 P := by
  obtain ⟨P, hP⟩ :=
    exists_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint.{u, w}
      B S hS 𝒵 h𝒵
  exact ⟨P, hP, fun Q hQ =>
    eq_of_isReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 h𝒵 hQ hP⟩

end AlgebraicGeometry.Stack

end
