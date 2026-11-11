module

public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbeExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackExistence

/-!
# The reduced locally Noetherian one-point substack

Let `𝒵` be an algebraic stack over `S` which is reduced with a singleton space of points, that is,
which satisfies condition (1) of Stacks 06MN. Then there is a unique strictly full subcategory
`𝒵' ⊂ 𝒵` which is an algebraic stack satisfying the equivalent conditions of Stacks 06MP, and the
inclusion `𝒵' ⟶ 𝒵` is a monomorphism of algebraic stacks. This file proves the existence, existence
and uniqueness together, and the full statement of Stacks 06MR.

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
* `AlgebraicGeometry.Stack`
  `.existsUnique_reducedLocallyNoetherianUniquePointSubstack_isMonomorphism`:
  **Stacks 06MR**, exactly one strictly full subcategory of `𝒵` is an algebraic stack satisfying
  both conditions of Stacks 06MP, and its inclusion is a monomorphism.

## Implementation notes

A strictly full subcategory of `𝒵` is an object property of `𝒵` closed under isomorphism, and the
predicate `AlgebraicGeometry.Stack.IsReducedLocallyNoetherianUniquePointSubstack` asks of it that
its full subcategory be an algebraic stack satisfying condition (2) of Stacks 06MP. The two
conditions of Stacks 06MP are equivalent (Stacks 06MP is proved in
`StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStackFinitePresentation`), and the full
statement records both of them for the subcategory it produces.

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
theorem exists_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (h𝒵 : IsReducedWithUniquePoint B S hS 𝒵) :
    ∃ P : ObjectProperty 𝒵.val.val.obj,
      IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 P :=
  exists_isReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS
    (hasFullyFaithfulFinitePresentationPresentations.{u, w} B S hS) 𝒵 h𝒵

/-- Let `𝒵` be an algebraic stack over `S` which is reduced with a singleton space of points.
Then exactly one strictly full subcategory of `𝒵` is an algebraic stack satisfying condition (2)
of Stacks 06MP. -/
theorem existsUnique_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (h𝒵 : IsReducedWithUniquePoint B S hS 𝒵) :
    ∃! P : ObjectProperty 𝒵.val.val.obj,
      IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 P := by
  obtain ⟨P, hP⟩ :=
    exists_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint.{u, w}
      B S hS 𝒵 h𝒵
  exact ⟨P, hP, fun Q hQ =>
    eq_of_isReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 h𝒵 hQ hP⟩

/-- **Stacks 06MR.** Let `𝒵` be an algebraic stack over `S` satisfying the equivalent conditions of
**Stacks 06MN**, read as its condition (1): `𝒵` is reduced and `|𝒵|` is a singleton. Then there is
a unique strictly full subcategory `𝒵' ⊂ 𝒵` which is an algebraic stack satisfying the equivalent
conditions of **Stacks 06MP**, that is, both condition (1), reduced, locally Noetherian with a
singleton space of points, and condition (2), a surjective flat 1-morphism locally of finite
presentation from the spectrum of a field; and the inclusion `𝒵' ⟶ 𝒵` is a monomorphism of
algebraic stacks in the sense of **Stacks 04ZW**.

Existence and uniqueness are
`existsUnique_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint`,
condition (1) of Stacks 06MP follows from condition (2) by the implication (2) ⟹ (1) of
Stacks 06MP, `isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation`, and the
monomorphy is `AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion`. -/
@[stacks 06MR]
theorem existsUnique_reducedLocallyNoetherianUniquePointSubstack_isMonomorphism
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (h𝒵 : IsReducedWithUniquePoint B S hS 𝒵) :
    ∃! P : ObjectProperty 𝒵.val.val.obj, P.IsClosedUnderIsomorphisms ∧
      ∃ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒵 P),
        IsReducedLocallyNoetherianWithUniquePoint B S hS
            (fullSubcategoryAlgebraicStack 𝒵 P hP) ∧
          HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS
            (fullSubcategoryAlgebraicStack 𝒵 P hP) ∧
          AlgebraicStacks.IsMonomorphism B S hS (fullSubcategoryInclusion 𝒵 P hP) := by
  obtain ⟨P, ⟨hiso, hP, hcov⟩, huniq⟩ :=
    existsUnique_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint.{u, w}
      B S hS 𝒵 h𝒵
  refine ⟨P, ⟨hiso, hP, ?_, hcov,
    AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion B S hS 𝒵 P hP⟩, ?_⟩
  · exact isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation.{u, w}
      B S hS _ hcov
  · rintro Q ⟨hQiso, hQ, -, hQcov, -⟩
    exact huniq Q ⟨hQiso, hQ, hQcov⟩

end AlgebraicGeometry.Stack

end
