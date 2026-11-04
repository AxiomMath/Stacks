module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack

/-!
# A strictly full subcategory with representable inclusion is algebraic

Let `𝒳` be an algebraic stack over `S` and let `P` be a property of its objects stable under
pullback (so that the full subcategory it cuts out is fibred in groupoids). If the inclusion of
that full subcategory into `𝒳` is representable by algebraic spaces, the full subcategory is
itself an algebraic stack: this is Stacks 05UM applied to the inclusion. If moreover the inclusion
is an open immersion, the full subcategory is an open substack of `𝒳` in the sense of Stacks 04YM,
part (1).

## Main results

In the namespace `AlgebraicGeometry.Stack`:

* `isAlgebraicStack_fullSubcategoryBased_of_isRepresentableByAlgebraicSpaces`: a strictly full
  subcategory whose inclusion is representable by algebraic spaces is an algebraic stack.
* `exists_openSubstack_of_isOpenImmersion`: a full subcategory whose inclusion is an open
  immersion is an open substack.

## References

* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A strictly full subcategory of an algebraic stack whose inclusion is representable by
algebraic spaces is an algebraic stack.** -/
theorem isAlgebraicStack_fullSubcategoryBased_of_isRepresentableByAlgebraicSpaces
    (𝒳 : AlgebraicStacks.{u, w} B S hS) {P : ObjectProperty 𝒳.val.val.obj}
    (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS (fullSubcategoryBasedInclusion 𝒳 P)) :
    IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P) :=
  isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS
    (fullSubcategoryFiberedInclusion 𝒳 hP) hrep 𝒳.property

/-- A property of the objects of an algebraic stack, stable under pullback, whose full
subcategory has inclusion representable by algebraic spaces and an open immersion, is the
property of an open substack. -/
theorem exists_openSubstack_of_isOpenImmersion
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (P : ObjectProperty 𝒳.val.val.obj)
    (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS (fullSubcategoryBasedInclusion 𝒳 P))
    (hopen : IsOpenImmersion B S hS (fullSubcategoryFiberedInclusion 𝒳 hP)) :
    ∃ U : OpenSubstack 𝒳, U.property = P :=
  ⟨⟨P, ⟨fun e h => hP e.inv h⟩,
    isAlgebraicStack_fullSubcategoryBased_of_isRepresentableByAlgebraicSpaces 𝒳 hP hrep,
    ⟨hrep, hopen⟩⟩, rfl⟩

end AlgebraicGeometry.Stack

end
