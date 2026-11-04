module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Submersive
public import StacksFrontier.AlgebraicGeometry.Stacks.SubmersiveAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalTopologicalProperties

/-!
# Universally submersive representable 1-morphisms of algebraic stacks (Stacks 0CHX)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` representable by algebraic spaces.
**Stacks 0CHX** says that `f` is universally submersive — the relative property of Tag 04XB at
universal submersiveness of morphisms of algebraic spaces — exactly when, for every algebraic
stack `𝒵` over `𝒴`, the map `|𝒵 ×_𝒴 𝒳| → |𝒵|` on the points of Tag 04XG is submersive for the
topology of Tag 04XL.

## Main results

* `AlgebraicGeometry.Stack.representable_universallySubmersive_iff`: **Stacks 0CHX**.

## Implementation notes

This is the submersive instance of
`AlgebraicGeometry.Stack.relative_iff_forall_pointsMap_fst`, which carries the whole argument for
an abstract property of maps on point spaces; submersiveness satisfies its two closure conditions
by `AlgebraicGeometry.Stack.isConjInvariant_quotientMapProperty` and
`AlgebraicGeometry.Stack.isDescendable_quotientMapProperty`.

The relative side is written out in the unrolled form of Tag 04XB, as
`AlgebraicGeometry.Stack.UniversallyClosed` is.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06U6](https://stacks.math.columbia.edu/tag/06U6)
* [Stacks Project, Tag 0CHX](https://stacks.math.columbia.edu/tag/0CHX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CHX.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` representable by
algebraic spaces is universally submersive in the relative sense of Tag 04XB — every algebraic
space representing a base change of `f` along a scheme-valued point of `𝒴` has universally
submersive structural morphism — exactly when, for every algebraic stack `𝒵` over `𝒴`, the map
`|𝒵 ×_𝒴 𝒳| → |𝒵|` of topological spaces is submersive. -/
@[stacks 0CHX]
theorem representable_universallySubmersive_iff
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    (∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
        (_hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
        (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hT : IsAlgebraicSpace B U.left.1 U.left.2 T),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
            (CatFiberedInGroupoids.homFunctor f.hom))
          (presheafOfCategories (T ⋙ typeToCat)).p) →
        Space.UniversallySubmersive B S hS
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨T, hT⟩)).hom) ↔
      AlgebraicStacks.IsUniversallySubmersive B S hS f := by
  have := respectsIso_pointMapProperty B S hS quotientMapProperty.{u}
    isConjInvariant_quotientMapProperty
  have key := relative_iff_forall_pointsMap_fst B S hS quotientMapProperty.{u}
    isConjInvariant_quotientMapProperty isDescendable_quotientMapProperty f hf
  constructor
  · intro H 𝒵 g
    refine key.mp ?_ 𝒵 g
    intro U y hy T hT he
    exact (universally_iff_forall_space_baseChange B S hS _ _).mpr (H U y hy T hT he)
  · intro H U y hy T hT he
    exact (universally_iff_forall_space_baseChange B S hS
      (pointMapProperty B S hS quotientMapProperty.{u}) _).mp (key.mpr H U y hy T hT he)

end AlgebraicGeometry.Stack

end
