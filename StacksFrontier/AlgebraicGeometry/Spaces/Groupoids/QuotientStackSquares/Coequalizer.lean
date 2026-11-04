module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.Descent
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyGroupoid

/-!
# The quotient stack is a two-coequalizer of its presentation (Stacks 044U)

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `[U/R]` be its quotient stack (Stacks 044Q) and let
`π : 𝒮_U ⟶ [U/R]` be the canonical projection of Stacks 044R. Stacks 044S makes the square

    𝒮_R ---s---> 𝒮_U
     |            |
     t            π
     v            v
    𝒮_U ---π---> [U/R]

2-commute, and Stacks 044U is the universal property of that square: given a stack in groupoids
`X` over the big fppf site, a 1-morphism `f : 𝒮_U ⟶ X` and a 2-morphism `β : s ∘ f ⟶ t ∘ f`
satisfying the composition cocycle of Stacks 044T, the 1-morphism `f` descends to `[U/R]`.

The descent itself is
`AlgebraicGeometry.Stack.quotientStack_desc_of_extendsAlongStackification`, which carries the
construction on the hypothesis that 1-morphisms out of the presentation of the quotient extend
along the stackification, and `AlgebraicGeometry.Stack.quotientStack_desc` is the tagged
unconditional form. This file discharges that hypothesis from the universal property of the
stackification, Stacks 0436, under the unbundled reading of "stack in groupoids", which is
weaker than the bundled hypothesis the unconditional form takes.

## Main results

* `AlgebraicGeometry.Stack.exists_extension_quotientStack`: every 1-morphism out of the
  presentation `[U/_pR]` that the quotient stack stackifies extends along the stackification map
  to a 1-morphism out of `[U/R]`, with a 2-isomorphism filling the triangle whose components are
  vertical over the site. This is Stacks 0436 for the pair
  `AlgebraicGeometry.Stack.toQuotientStack` and `X`.

## Implementation notes

"Stack in groupoids" is spelled, as in
`StacksFrontier/CategoryTheory/Sites/Stackification/UniversalPropertyGroupoid.lean`, as
`CategoryTheory.Functor.IsFiberedInGroupoids` (Stacks 003S) together with
`CategoryTheory.Functor.IsStack` (Stacks 026F) — reading (3) of Stacks 02ZJ. The other rendering,
`CategoryTheory.Functor.IsStackInGroupoids` (Stacks 02ZI), is not used: only the implication
026F ⟹ 02ZI is available in the tree, the converse needing fibre products in the base, so
assuming 02ZI would not deliver the sieve-indexed descent that Stacks 0435 consumes.

The morphism universe of the total category of `X` is `u + 1`, one above the morphism universe of
the big fppf site. That is not a restriction that can be relaxed here, and not an artefact of the
hypotheses: the quotient stack is the stackification of a fibration whose objects live in
`Type (u + 1)`, the three-stage construction of Stacks 02ZN requires its input to have objects and
morphisms in a common universe, and so `AlgebraicGeometry.Stack.quotientPrestack` raises the
morphisms of the pointwise groupoid fibration to `u + 1` and `[U/R]` inherits them. Stacks 0435,
and with it Stacks 0436, shares one morphism universe between the three total categories it
speaks about — the *base* morphism universe is independent, which is what lets the universal
property reach a quotient stack at all. Hence any target of the extension has morphisms in
`u + 1`. A target whose morphisms lie in `u`, which is where
`AlgebraicGeometry.Stack.fibredCategory` and `AlgebraicGeometry.Stack.AlgebraicStacks` put them,
is reached only through a universe-raising transport of the stack condition along
`CategoryTheory.ULiftHom`, and the transport of Stacks 042W in the tree
(`CategoryTheory.BasedCategory.Equivalence.isStack`) is stated for two based categories with the
*same* morphism universe, so it does not apply to such a lift. Nothing of Stacks 044U is lost:
its hypotheses and conclusion are universe-polymorphic in the source, and the quotient stack
itself is a stack in groupoids at morphism universe `u + 1`.

## References

* [Stacks Project, Tag 0435](https://stacks.math.columbia.edu/tag/0435)
* [Stacks Project, Tag 0436](https://stacks.math.columbia.edu/tag/0436)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 044T](https://stacks.math.columbia.edu/tag/044T)
* [Stacks Project, Tag 044U](https://stacks.math.columbia.edu/tag/044U)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u t

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}
  (G : GroupoidInAlgebraicSpaces C S hS B)
  (X : BasedCategory.{u + 1, t, u, u + 1} (BigFppfOver C S hS))

/-- **Stacks 0436 for the quotient stack.** Let `G` be a groupoid in algebraic spaces and let `X`
be a stack in groupoids over the big fppf site. Every 1-morphism from the presentation
`AlgebraicGeometry.Stack.quotientPrestack` of the quotient stack to `X` extends along the
stackification map `AlgebraicGeometry.Stack.toQuotientStack` to a 1-morphism `[U/R] ⟶ X`, with a
2-isomorphism filling the triangle each of whose components lies over an identity of the site.

This is the universal property of the stackification at the hypotheses the quotient stack
supplies: that the presentation and the quotient are fibred in groupoids, that the quotient is a
stack, and the two clauses of Stacks 02ZN exhibiting the quotient as the stackification of the
presentation. -/
theorem exists_extension_quotientStack
    (hX : X.p.IsFiberedInGroupoids)
    (hXs : X.p.IsStack (BigFppfOver.topology C S hS))
    (g₀ : BasedFunctor (quotientPrestack G) X) :
    ∃ (g : BasedFunctor (quotientStack G) X)
      (η : toQuotientStack G ⋙ g.toFunctor ≅ g₀.toFunctor),
      ∀ x : (quotientPrestack G).obj,
        X.p.IsHomLift (𝟙 ((quotientPrestack G).p.obj x)) (η.hom.app x) :=
  ⟨⟨Functor.Stackification.extendGroupoid (isFiberedInGroupoids_quotientPrestack G)
      (isFiberedInGroupoids_quotientStack G) (isStack_quotientStack G) hX hXs
      (isFibredOneMorphism_toQuotientStack G).comp_eq g₀.w
      (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G),
    Functor.Stackification.extendGroupoid_comp_eq (isFiberedInGroupoids_quotientPrestack G)
      (isFiberedInGroupoids_quotientStack G) (isStack_quotientStack G) hX hXs
      (isFibredOneMorphism_toQuotientStack G).comp_eq g₀.w
      (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G)⟩,
    Functor.Stackification.unitGroupoid (isFiberedInGroupoids_quotientPrestack G)
      (isFiberedInGroupoids_quotientStack G) (isStack_quotientStack G) hX hXs
      (isFibredOneMorphism_toQuotientStack G).comp_eq g₀.w
      (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G),
    fun x => Functor.Stackification.isHomLift_unitGroupoid_app
      (isFiberedInGroupoids_quotientPrestack G) (isFiberedInGroupoids_quotientStack G)
      (isStack_quotientStack G) hX hXs (isFibredOneMorphism_toQuotientStack G).comp_eq g₀.w
      (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G) x⟩

end AlgebraicGeometry.Stack

end
