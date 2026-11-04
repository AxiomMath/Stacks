module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection

/-!
# The self-intersection of a point of an algebraic stack is an algebraic space (Stacks 04T4 (1))

Let `S` be a scheme contained in a big fppf site `B`, let `𝒳` be an algebraic stack over `S`, let
`𝒰` be a category fibred in groupoids over the big fppf site of `S` which is representable by an
algebraic space, and let `f : 𝒰 ⟶ 𝒳` be a 1-morphism. Part (1) of Stacks 04T4 says that the
2-fibre product `ℛ = 𝒰 ×_{f, 𝒳, f} 𝒰` is again representable by an algebraic space.

The Stacks proof is two citations: the diagonal of `𝒳` is representable by algebraic spaces, so
Stacks 045G makes `f` representable by algebraic spaces, and then Stacks 0300 makes the 2-fibre
product representable by an algebraic space. What `045G` packages is the equivalence of its
eight conditions, and the composite the proof needs is the implication from condition (1) — a
representable diagonal, which is one of the defining clauses of
`AlgebraicGeometry.Stack.IsAlgebraicStack` — to condition (8), that the 2-fibre product over `𝒳`
of two categories fibred in groupoids representable by algebraic spaces is representable by an
algebraic space. Condition (8) instantiated at `𝒯₁ = 𝒯₂ = 𝒰` and `x = y = f` is the conclusion,
which is `AlgebraicGeometry.Stack.SelfIntersection.isRepresentableByAlgebraicSpace_relation`. This
file chains the seven equivalences of Stacks 045G into the single implication (1) ⟹ (8) and reads
part (1) off it.

## Main results

* `AlgebraicGeometry.Stack.hasAlgebraicSpaceProducts_of_hasRepresentableDiagonal`: the
  implication from condition (1) to condition (8) of Stacks 045G, the composite of the seven
  equivalences.
* `isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack`, in the namespace
  `AlgebraicGeometry.Stack.SelfIntersection`: **Stacks 04T4 (1)**.

## Implementation notes

Every intermediate condition of Stacks 045G beyond condition (4) carries universe parameters for
the two factors of the product it speaks about, and conditions (6) and (8) carry two such pairs
while conditions (5) and (7) carry one. Chaining them therefore leaves the second pair of a
condition (6) occurring strictly inside the chain undetermined, and the composite is rejected with
`contains universe level metavariables` rather than with anything that reads as a unification
failure. Each of the four links from condition (4) onwards is accordingly annotated explicitly.

Parts (2) and (3) of Stacks 04T4 are
`AlgebraicGeometry.Stack.SelfIntersection.tripleEquivComposable` and
`AlgebraicGeometry.Stack.SelfIntersection.composition`. Parts (4), (5) and (6) build the groupoid
in algebraic spaces on the representing spaces of `𝒰` and `ℛ`, the canonical 1-morphism out of its
quotient stack, and its full faithfulness; they are about the quotient stack `[U/R]` of a groupoid
in algebraic spaces (Stacks 044Q) and are not treated in this file.

## References

* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁ v₂ w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- **Stacks 045G, the implication from condition (1) to condition (8).** If the diagonal of a
category fibred in groupoids `𝒳` over the big fppf site of `S` is representable by algebraic
spaces, then the 2-fibre product over `𝒳` of any two categories fibred in groupoids representable
by algebraic spaces over `S` is representable by an algebraic space.

This is the composite of the seven equivalences of Stacks 045G. -/
theorem hasAlgebraicSpaceProducts_of_hasRepresentableDiagonal
    (h₁ : HasRepresentableDiagonal B S hS 𝒳) :
    HasAlgebraicSpaceProducts.{u, v, w, v₁, w₁, v₂, w₂} B S hS 𝒳 :=
  (isRepresentableFromAlgebraicSpaces_iff_hasAlgebraicSpaceProducts.{u, v, w, v₁, w₁, v₂, w₂}
      B S hS 𝒳).1
    ((hasAlgebraicSpaceRepresentableProducts_iff_isRepresentableFromAlgebraicSpaces.{u, v, w, v₁,
          w₁, v₂, w₂} B S hS 𝒳).1
      ((representableFromCategories_iff_algebraicSpaceProducts.{u, v, w, v₁, w₁, v₂, w₂}
          B S hS 𝒳).1
        ((hasAlgebraicSpaceSchemePointProducts_iff_isRepresentableFromRepresentableCategories.{u,
              v, w, v₁, w₁} B S hS 𝒳).1
          ((isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts B S hS 𝒳).1
            ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).1
              ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).1 h₁))))))

namespace SelfIntersection

variable (𝒰 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
variable (f : 𝒰.val ⥤ᵇ 𝒴.val)

/-- **Stacks 04T4 (1).** Let `𝒳` be an algebraic stack over `S` and let `f : 𝒰 ⟶ 𝒳` be a
1-morphism whose source is a category fibred in groupoids representable by an algebraic space over
`S`. Then the self-intersection `ℛ = 𝒰 ×_{f, 𝒳, f} 𝒰` is representable by an algebraic space.

The diagonal of an algebraic stack is representable by algebraic spaces, which is condition (1) of
Stacks 045G; condition (8) of Stacks 045G follows, and instantiated at `𝒯₁ = 𝒯₂ = 𝒰` and
`x = y = f` it is the conclusion. -/
@[stacks 04T4 "part (1): the relation is an algebraic space"]
theorem isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
    (h𝒴 : Stack.IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (h𝒰 : Stack.IsRepresentableByAlgebraicSpace B S hS 𝒰) :
    Stack.IsRepresentableByAlgebraicSpace B S hS (relation B S hS 𝒰 𝒴 f) :=
  isRepresentableByAlgebraicSpace_relation B S hS 𝒰 𝒴 f
    (hasAlgebraicSpaceProducts_of_hasRepresentableDiagonal.{u, u, u + 1, u, u, u, u} B S hS 𝒴
      (hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒴 h𝒴)) h𝒰

end SelfIntersection

end AlgebraicGeometry.Stack

end
