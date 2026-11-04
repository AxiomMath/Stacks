module

public import Mathlib.Topology.Homeomorph.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjective
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# Universal homeomorphisms of algebraic stacks (Stacks 0CI7)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is a *universal homeomorphism* when for
every 1-morphism `g : 𝒵 ⟶ 𝒴` of algebraic stacks the induced map `|𝒵 ×_𝒴 𝒳| → |𝒵|` of
topological spaces is a homeomorphism.

## Main definitions

* `AlgebraicGeometry.Stack.UniversalHomeomorphism`: **Stacks 0CI7**.

## Main results

* `AlgebraicGeometry.Stack.universallyInjective_of_universalHomeomorphism`: a universal
  homeomorphism is universally injective in the sense of **Stacks 0CI2**.

## Implementation notes

The quantifier runs over *every* 1-morphism `g : 𝒵 ⟶ 𝒴` with `𝒵` an algebraic stack over `S`,
not over schemes or algebraic spaces only, and the base change is not a chosen model: as in
`AlgebraicGeometry.Stack.UniversallyInjective`, the condition is asked of every 2-commutative
square over the cospan `(g, f)` which is a 2-fibre product in the sense of **Stacks 003Q**
(`CategoryTheory.Bicategory.IsTwoFibreProduct`), at its projection `fst` to `𝒵`. So the
condition is independent of the model, a consumer may instantiate it at whichever model it
already has, and verifying it means verifying it at every model — which is what makes it usable
as a hypothesis in the base-change and descent arguments with no transport step.

The point sets and the map between them are those of **Stacks 04XG** in the form
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap`, and the topologies are the ones
**Stacks 04XL** characterises, in the constructed form
`AlgebraicGeometry.Stack.pointTopology`. Both topologies are supplied explicitly rather than by
instance resolution, because `AlgebraicGeometry.Stack.pointTopology` is a `def` and not an
instance; `AlgebraicGeometry.Stack.chosenPointTopologyFamily_topology_eq` identifies it with the
topology the existence statement of Stacks 04XL chooses.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0CI2](https://stacks.math.columbia.edu/tag/0CI2)
* [Stacks Project, Tag 0CI7](https://stacks.math.columbia.edu/tag/0CI7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CI7.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is a *universal
homeomorphism* if for every 1-morphism `g : 𝒵 ⟶ 𝒴` of algebraic stacks over `S` and every
2-fibre product of `(g, f)` the map `|𝒵 ×_𝒴 𝒳| → |𝒵|` induced by the projection to `𝒵` is a
homeomorphism. -/
@[stacks 0CI7]
abbrev UniversalHomeomorphism {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (𝒵 : AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴) (P : Bicategory.TwoCommSq g f),
    Bicategory.IsTwoFibreProduct P →
      @IsHomeomorph _ _ (pointTopology B S hS P.pt.val) (pointTopology B S hS 𝒵.val)
        (AlgebraicStacks.pointsMap B S hS P.fst)

/-- **A universal homeomorphism of algebraic stacks over `S` is universally injective.** Each
base change is injective on points because it is a homeomorphism there. -/
theorem universallyInjective_of_universalHomeomorphism
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : UniversalHomeomorphism B S hS f) : UniversallyInjective B S hS f := by
  intro 𝒵 g P hP
  let _ := pointTopology B S hS P.pt.val
  let _ := pointTopology B S hS 𝒵.val
  exact (hf 𝒵 g P hP).injective

end AlgebraicGeometry.Stack

end
