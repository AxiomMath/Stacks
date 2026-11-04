module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCompGeneral

/-!
# Flat composition for 1-morphisms of categories fibred in groupoids (Stacks 06PX)

Stacks 06PX says that a composite of flat 1-morphisms of algebraic stacks over `S` is flat; that
statement is `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_comp`, proved in
`StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp`. This module proves the same
thing one level of generality up: for 1-morphisms of arbitrary categories fibred in groupoids
over the big fppf site of `S`, flatness being read as the smooth-diagram criterion of
**Stacks 06FM** at flatness of morphisms of algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_isFlat_comp`: flatness in the sense of
  the existential smooth-diagram criterion of **Stacks 06FM** is stable under composition, with
  no hypothesis on the three categories fibred in groupoids.

## Implementation notes

Flatness of a 1-morphism of algebraic stacks is condition (2) of Stacks 06FM at flatness of
morphisms of algebraic spaces — written out longhand in `AlgebraicGeometry.Stack`
`.AlgebraicStacks.IsFlat` (**Stacks 06PW**), with the identification recorded by
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram` — so this is
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp_of_precomp` (**Stacks 06FP**) at
that property, exactly as the sibling Stacks 06PY is Stacks 06FQ at it. Its three hypotheses on
the property are discharged by `AlgebraicGeometry.Space.isFlat_comp` (**Stacks 03MN**) alone,
twice: once as composition-stability and once, together with
`AlgebraicGeometry.Space.isFlat_of_isSmooth` (**Stacks 04TA**), as stability under precomposition
with a smooth morphism; and by `AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange`
(**Stacks 03MO**).

The statement for arbitrary categories fibred in groupoids is separated out and left untagged:
Stacks 06PX is about algebraic stacks, so the tag belongs on the algebraic-stack form, but the
consumers of flatness of a 1-morphism *out of a represented category* — the flat objects of
**Stacks 0787**, whose source is `AlgebraicGeometry.Stack.schemeFibredCategory` and not an
algebraic stack in the library's sense — need the general one, and nothing is gained by making
them exhibit the represented category as an algebraic stack first. That is also why the form of
Stacks 06FP used here is the one asking nothing of the categories fibred in groupoids.

## References

* [Stacks Project, Tag 03MN](https://stacks.math.columbia.edu/tag/03MN)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 04TA](https://stacks.math.columbia.edu/tag/04TA)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FP](https://stacks.math.columbia.edu/tag/06FP)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A composite of flat 1-morphisms of categories fibred in groupoids is flat**, flatness being
the existential smooth-diagram criterion of **Stacks 06FM** at flatness of morphisms of algebraic
spaces over `S`. This is
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp_of_precomp` (**Stacks 06FP**) at
that property. -/
theorem hasPropertyOnSomeSmoothDiagram_isFlat_comp
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ k => Space.IsFlat B S hS k) f)
    (hg : HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ k => Space.IsFlat B S hS k) g) :
    HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ k => Space.IsFlat B S hS k) (f ≫ g) :=
  have : (spaceProperty B S hS
      (fun _ _ k => Space.IsFlat B S hS k)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  hasPropertyOnSomeSmoothDiagram_comp_of_precomp B S hS (fun _ _ k => Space.IsFlat B S hS k)
    (fun hX hY hZ p q hp hq =>
      Space.isFlat_comp B S hS hX hY hZ p q (Space.isFlat_of_isSmooth B S hS p hp) hq)
    (Space.isFlat_comp B S hS) f g hf hg

end AlgebraicGeometry.Stack

end
