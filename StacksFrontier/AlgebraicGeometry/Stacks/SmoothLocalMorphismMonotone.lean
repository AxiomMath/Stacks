module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse

/-!
# Monotonicity of the smooth-diagram criterion (Stacks 06PS, 0DNP)

**Stacks 06PS** observes that an implication between two properties of morphisms of algebraic
spaces over `S` induces the same implication for 1-morphisms of algebraic stacks over `S`:
the smooth-diagram criterion of **Stacks 06FM** is monotone in the property it tests.

**Stacks 0DNP** is one application: a smooth 1-morphism of algebraic stacks over `S` is locally
of finite presentation, because a smooth morphism of algebraic spaces is locally of finite
presentation (**Stacks 04AJ**).

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_mono`: **Stacks 06PS**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth`:
  **Stacks 0DNP**.

## Implementation notes

Monotonicity is stated at condition (2) of Stacks 06FM — the existential criterion
`AlgebraicGeometry.Stack.HasPropertyOnSomeSmoothDiagram`, which is Definition 06FN — and needs
no hypothesis on either property: one re-reads the same diagram with the same top horizontal
morphism, whose source and target are algebraic spaces, so the implication applies to it
directly. Stacks 06PS asks in addition that both properties be smooth local on the
source-and-target, which is what makes the notion well defined; the statement here drops both,
and specialising it at smooth-local properties recovers the source's assertion.

Stacks 075U is condition (2) at smoothness, on the nose, whereas Stacks 06Q2 part (1) is the
*universal* criterion at local finite presentation, so Stacks 0DNP is monotonicity followed by
the round trip `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some`
(**Stacks 06FM**), whose smooth-locality hypothesis is the local-finite-presentation case of
**Stacks 06FC**. This is the same round trip the sister statements
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_comp` (Stacks 06Q3) and
`...isLocallyOfFiniteType_comp` (Stacks 06FT) make.

`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isSmooth` needs no hypothesis that its
source and target be algebraic spaces, so the two hypotheses the monotonicity statement offers
are discharged by underscores.

## References

* [Stacks Project, Tag 04AJ](https://stacks.math.columbia.edu/tag/04AJ)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FN](https://stacks.math.columbia.edu/tag/06FN)
* [Stacks Project, Tag 06PS](https://stacks.math.columbia.edu/tag/06PS)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- **Stacks 06PS.** An implication between two properties of morphisms of algebraic spaces
over `S` induces the same implication for 1-morphisms of algebraic stacks over `S`: the
existential smooth-diagram criterion of Stacks 06FM is monotone in the property it tests.

The same diagram witnesses both: its top horizontal morphism is a morphism of algebraic spaces
and has the first property, hence the second. -/
@[stacks 06PS]
theorem hasPropertyOnSomeSmoothDiagram_mono
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P P' : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hPP' : ∀ {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B S hS U → IsAlgebraicSpace B S hS V →
      ∀ (g : U ⟶ V), P g → P' g)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS P f) :
    HasPropertyOnSomeSmoothDiagram B S hS P' f := by
  obtain ⟨U, V, hU, hV, a, b, h, hcomm, ha, hsurj, hb, hP⟩ := hf
  exact ⟨U, V, hU, hV, a, b, h, hcomm, ha, hsurj, hb, hPP' hU hV h hP⟩

namespace AlgebraicStacks

/-- **Stacks 0DNP.** A smooth 1-morphism of algebraic stacks over `S` is locally of finite
presentation.

Stacks 075U is the existential smooth-diagram criterion at smoothness of morphisms of algebraic
spaces, which is locally of finite presentation by **Stacks 04AJ**; monotonicity (Stacks 06PS)
gives the existential criterion at local finite presentation, and the round trip of
Stacks 06FM — whose smooth-locality hypothesis is the local-finite-presentation case of
Stacks 06FC — gives the universal criterion, which is Stacks 06Q2 part (1). -/
@[stacks 0DNP]
theorem isLocallyOfFinitePresentation_of_isSmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsSmooth B S hS f) :
    IsLocallyOfFinitePresentation B S hS f :=
  (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      𝒳.property 𝒴.property f.hom).2
    (Stack.hasPropertyOnSomeSmoothDiagram_mono B S hS _ _
      (fun _ _ _ hg => Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hg)
      f.hom hf)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
