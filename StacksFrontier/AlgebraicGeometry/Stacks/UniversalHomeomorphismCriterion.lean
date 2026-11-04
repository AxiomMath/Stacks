module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalTopologicalProperties

/-!
# Representable universal homeomorphisms of algebraic stacks (Stacks 0CI6)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` representable by algebraic spaces.
**Stacks 0CI6** says that `f` is a universal homeomorphism — the relative property of Tag 04XB at
universal homeomorphisms of algebraic spaces — exactly when, for every algebraic stack `𝒵` over
`𝒴`, the map `|𝒵 ×_𝒴 𝒳| → |𝒵|` on the points of Tag 04XG is a homeomorphism for the topology of
Tag 04XL. The right-hand side is the absolute notion of Tag 0CI7.

## Main results

* `AlgebraicGeometry.Stack.representable_universalHomeomorphism_iff`: **Stacks 0CI6**.

## Implementation notes

This is the homeomorphism instance of
`AlgebraicGeometry.Stack.relative_iff_forall_pointsMap_fst`, which carries the whole argument for
an abstract property of maps on point spaces; being a homeomorphism satisfies its two closure
conditions by `AlgebraicGeometry.Stack.isConjInvariant_homeomorphProperty` and
`AlgebraicGeometry.Stack.isDescendable_homeomorphProperty`.

The relative side is written out in the unrolled form of Tag 04XB, as
`AlgebraicGeometry.Stack.UniversallyClosed` is.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 05Z5](https://stacks.math.columbia.edu/tag/05Z5)
* [Stacks Project, Tag 0CI6](https://stacks.math.columbia.edu/tag/0CI6)
* [Stacks Project, Tag 0CI7](https://stacks.math.columbia.edu/tag/0CI7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CI6.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` representable by
algebraic spaces is a universal homeomorphism in the relative sense of Tag 04XB — every algebraic
space representing a base change of `f` along a scheme-valued point of `𝒴` has structural
morphism a universal homeomorphism — exactly when, for every algebraic stack `𝒵` over `𝒴`, the
map `|𝒵 ×_𝒴 𝒳| → |𝒵|` of topological spaces is a homeomorphism. -/
@[stacks 0CI6]
theorem representable_universalHomeomorphism_iff
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
        Space.UniversalHomeomorphism B S hS
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨T, hT⟩)).hom) ↔
      AlgebraicStacks.UniversalHomeomorphism B S hS f := by
  have := respectsIso_pointMapProperty B S hS homeomorphProperty.{u}
    isConjInvariant_homeomorphProperty
  have key := relative_iff_forall_pointsMap_fst B S hS homeomorphProperty.{u}
    isConjInvariant_homeomorphProperty isDescendable_homeomorphProperty f hf
  exact ⟨fun H => key.mp fun U y hy T hT he =>
      (universally_iff_forall_space_baseChange B S hS _ _).mpr (H U y hy T hT he),
    fun H U y hy T hT he => (universally_iff_forall_space_baseChange B S hS
      (pointMapProperty B S hS homeomorphProperty.{u}) _).mp (key.mpr H U y hy T hT he)⟩

end AlgebraicGeometry.Stack

end
