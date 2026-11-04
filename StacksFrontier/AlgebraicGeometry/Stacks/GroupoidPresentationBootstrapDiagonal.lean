module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatPresentationRepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentationBootstrap

/-!
# The bootstrap with the diagonal of the target proved rather than assumed

The assembly of [Stacks, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC) takes two inputs:
representability of the diagonal of the target, and a smooth surjective cover of the target by an
algebraic stack. The first is produced by
[Stacks, Tag 05XW](https://stacks.math.columbia.edu/tag/05XW) from the flat presentation that the
assembly already has, so it need not be assumed.

## Main results

* `Stacks.Stack.isAlgebraicStack_of_flatPresentation_of_bootstrap04S6` — Tag 06DC with the
  diagonal input proved, leaving the cover.

## Implementation notes

`AlgebraicGeometry.Stack.HasRepresentableDiagonal` and
`IsRepresentableByAlgebraicSpaces` of the diagonal based functor are definitionally equal, as
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff` records by `Iff.rfl`, so Tag 05XW's
conclusion fills the slot directly. `HasRelativeProperty` unfolds to the longhand the assembly
carries, so its surjectivity, flatness and finite-presentation arguments are projections of that
bundle. Two of Tag 05XW's universe parameters occur only in `IsLocalAtTarget` instance arguments
and are not fixed by the conclusion, so the application is pinned explicitly.

## References

* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
* [Stacks Project, Tag 05XW](https://stacks.math.columbia.edu/tag/05XW)
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06DC** with the diagonal of the target no longer assumed: it is produced from the
flat presentation by Stacks 05XW. What remains assumed is
the smooth surjective cover of `𝒴` by an algebraic stack. -/
theorem isAlgebraicStack_of_flatPresentation_of_bootstrap04S6
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : 𝒳 ⟶ 𝒴)
    (hstack : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳)
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hFprops : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map V.hom)
      (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B V.left.1 V.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor F))
        (presheafOfCategories (G ⋙ typeToCat)).p) →
      (let g := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)).hom
       Space.IsSurjective B S hS g ∧ Space.IsFlat B S hS g ∧
         Space.IsLocallyOfFinitePresentation B S hS g))
    (hcover : ∃ (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
      (q : 𝒲 ⟶ 𝒴) (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom),
      IsAlgebraicStack.{u, w} B S hS 𝒲.val ∧
        HasRelativeProperty.{u, u, u + 1, u} B S hS
          (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS)
          q hq) :
    IsAlgebraicStack.{u, w} B S hS 𝒴.val :=
  isAlgebraicStack_of_flatPresentation.{u, w} B S hS F hstack h𝒳 hF hFprops
    (hasRepresentableDiagonal_of_flatPresentation.{u, u + 1, u + 1} B S hS F hstack h𝒳 hF
      (fun V y hy G hG h => (hFprops V y hy G hG h).1)
      (fun V y hy G hG h => (hFprops V y hy G hG h).2.1)
      (fun V y hy G hG h => (hFprops V y hy G hG h).2.2))
    hcover


end AlgebraicGeometry.Stack

end
