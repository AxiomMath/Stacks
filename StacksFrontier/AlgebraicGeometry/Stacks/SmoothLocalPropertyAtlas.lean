module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# The four atlas criteria for a smooth-local property of an algebraic stack (Stacks 04YF, 04YG)

Let `P` be a property of schemes local in the smooth topology. Stacks 04YF compares four ways of
asking that an algebraic stack `𝒳` over `S` has `P`:

* there is **some** smooth surjective presentation of `𝒳` by a scheme whose underlying scheme has
  `P`;
* **every** smooth scheme chart of `𝒳` has `P`;
* there is **some** smooth surjective presentation of `𝒳` by an algebraic space with the
  étale-local property `P` of Stacks 03E6;
* **every** smooth algebraic-space chart of `𝒳` has the étale-local property `P`.

This file introduces the four predicates themselves, which are the vocabulary the comparison is
phrased in. The comparisons are the covering set of the tag and are not proved here, so nothing
in this file carries `@[stacks 04YF]`.

Stacks 04YG *defines* "`𝒳` has property `P`" to be any one of those four conditions. The
existential scheme criterion is the form taken here, so it carries that tag.

## Main definitions

* `AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas`: the existential scheme criterion, and
  **Stacks 04YG**, the definition of an algebraic stack having a smooth-local property.
* `AlgebraicGeometry.Stack.HasPropertyOnEverySchemeChart`: the universal scheme criterion.
* `AlgebraicGeometry.Stack.HasPropertyOnSomeSpaceAtlas`: the existential algebraic-space criterion.
* `AlgebraicGeometry.Stack.HasPropertyOnEverySpaceChart`: the universal algebraic-space criterion.
* `AlgebraicGeometry.Stack.isLocal_etale`: a smooth-local property of schemes is étale-local.

## Implementation notes

A scheme over `S` enters as the algebraic stack `AlgebraicGeometry.Stack.schemeStack` it
represents, and an algebraic space over `S` as `AlgebraicGeometry.Stack.algebraicSpaceStack`,
rather than as an arbitrary equivalent presentation; both are the canonical objects of
`AlgebraicGeometry.Stack.AlgebraicStacks` the library already has.

Smoothness and surjectivity of the presentation are the notions for 1-morphisms of algebraic
stacks, `AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth` (**Stacks 075U**) and
`AlgebraicGeometry.Stack.IsSurjective` (**Stacks 04ZS**) — not the relative notions of
Stacks 04XB, which are what the smooth-diagram test inside Stacks 075U itself uses.

On the algebraic-space side the property asked of the chart is the étale-local property
`AlgebraicGeometry.Space.HasEtaleLocalProperty` of **Stacks 03E6**, since an algebraic space has
no underlying scheme. That predicate wants `P` to be local for the étale precoverage, which
`isLocal_etale` supplies from smooth locality: an étale morphism of schemes is smooth, so the
étale precoverage is contained in the smooth one and
`CategoryTheory.ObjectProperty.IsLocal.of_le` applies.

## References

* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (P : ObjectProperty Scheme.{u})
  [P.IsLocal (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]

/-- A property of schemes local in the smooth topology is local in the étale topology, because
an étale morphism of schemes is smooth and so the étale precoverage is contained in the smooth
one. This is what lets a smooth-local property be asked of an algebraic space through
`AlgebraicGeometry.Space.HasEtaleLocalProperty` (**Stacks 03E6**). -/
instance isLocal_etale : P.IsLocal Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le
    (Scheme.precoverage_mono (P := (@Etale : MorphismProperty Scheme.{u}))
      (Q := (@Smooth : MorphismProperty Scheme.{u}))
      (fun _ _ f hf => by
        let _ : Etale f := hf
        infer_instance))

/-- **The existential scheme criterion of Stacks 04YF**, and **Stacks 04YG**: the algebraic
stack `𝒳` *has property* `P` when it admits a smooth surjective 1-morphism from the algebraic
stack of a scheme over `S` whose underlying scheme has `P`.

Stacks 04YG defines "`𝒳` has `P`" by any of the four equivalent conditions of Stacks 04YF; this
is the first of them, and the comparisons of Stacks 04YF identify it with the other three. -/
@[stacks 04YG]
abbrev HasPropertyOnSomeSchemeAtlas (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ (U : BigFppfOver B S hS) (f : schemeStack B S hS U ⟶ 𝒳),
    IsSurjective B S hS f ∧
      AlgebraicStacks.IsSmooth B S hS f ∧
        P ((BigFppfOver.toScheme B S hS).obj U)

/-- **The universal scheme criterion of Stacks 04YF.** Every smooth 1-morphism to the algebraic
stack `𝒳` from the algebraic stack of a scheme over `S` has source whose underlying scheme
has `P`. Surjectivity is not required of a chart. -/
abbrev HasPropertyOnEverySchemeChart (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∀ (U : BigFppfOver B S hS) (f : schemeStack B S hS U ⟶ 𝒳),
    AlgebraicStacks.IsSmooth B S hS f →
      P ((BigFppfOver.toScheme B S hS).obj U)

/-- **The existential algebraic-space criterion of Stacks 04YF.** The algebraic stack `𝒳` admits a
smooth surjective 1-morphism from the algebraic stack of an algebraic space over `S` having the
étale-local property `P` of **Stacks 03E6**. -/
abbrev HasPropertyOnSomeSpaceAtlas (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (f : algebraicSpaceStack B S hS F hF ⟶ 𝒳),
    IsSurjective B S hS f ∧
      AlgebraicStacks.IsSmooth B S hS f ∧
        Space.HasEtaleLocalProperty B S hS F P

/-- **The universal algebraic-space criterion of Stacks 04YF.** Every smooth 1-morphism to the
algebraic stack `𝒳` from the algebraic stack of an algebraic space over `S` has source with the
étale-local property `P` of **Stacks 03E6**. Surjectivity is not required of a chart. -/
abbrev HasPropertyOnEverySpaceChart (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (f : algebraicSpaceStack B S hS F hF ⟶ 𝒳),
    AlgebraicStacks.IsSmooth B S hS f →
      Space.HasEtaleLocalProperty B S hS F P

end AlgebraicGeometry.Stack

end
