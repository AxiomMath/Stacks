module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedComposition

/-!
# Composition of proper 1-morphisms of algebraic stacks (Stacks 0CL7)

**Stacks 0CL7** asserts that a composition of proper 1-morphisms of algebraic stacks over `S` is
proper.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_comp`: **Stacks 0CL7**.

## Implementation notes

Properness of **Stacks 0CL5** is the conjunction of separatedness (**Stacks 04YW**), finite type
(**Stacks 06FS**, part (2)) and universal closedness (**Stacks 0513**, part (2)), so the assertion
is the conjunction of the three conjuncts' own composition stability — **Stacks 050K**,
**Stacks 06FT** and **Stacks 0515** — which is the source's own proof. Each of the three is
already available at exactly the shape the conjunction needs, for arbitrary 1-morphisms of
algebraic stacks and with no representability hypothesis, so the proof is the triple of them:
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_comp`, `...isFiniteType_comp` and
`...universallyClosed_comp`.

The three conjuncts carry the keys of their own tags and not of this one; **Stacks 0CL7** has a
single conclusion and its attribute sits on the single theorem below.

This is the composition assertion for properness of an *arbitrary* 1-morphism of algebraic
stacks. It is not the Stacks 04XY composition assertion for the relative properness
`AlgebraicGeometry.Stack.IsProper` of a 1-morphism representable by algebraic spaces, nor
`AlgebraicGeometry.Space.isProper_comp` for morphisms of algebraic spaces; those are statements
about a different kind of morphism and are distinguished by namespace, exactly as
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_comp` is distinguished from
`AlgebraicGeometry.Space.universallyClosed_comp`.

The companion assertion for base change is
`AlgebraicGeometry.Stack.AlgebraicStacks.isProper_baseChange` (**Stacks 0CL6**), which decomposes
over the same three conjuncts.

## References

* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 0515](https://stacks.math.columbia.edu/tag/0515)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FT](https://stacks.math.columbia.edu/tag/06FT)
* [Stacks Project, Tag 0CL5](https://stacks.math.columbia.edu/tag/0CL5)
* [Stacks Project, Tag 0CL7](https://stacks.math.columbia.edu/tag/0CL7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CL7.** A composition of proper 1-morphisms of algebraic stacks over `S` is proper:
if `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` are proper, then so is `f ≫ g`.

Properness is separatedness, finite type and universal closedness (Stacks 0CL5), and the three
conjuncts compose by **Stacks 050K**, **Stacks 06FT** and **Stacks 0515** respectively, which is
the source's own proof. -/
@[stacks 0CL7]
theorem isProper_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsProper B S hS f) (hg : IsProper B S hS g) :
    IsProper B S hS (f ≫ g) :=
  ⟨isSeparated_comp B S hS f g hf.1 hg.1,
    isFiniteType_comp B S hS f g hf.2.1 hg.2.1,
    universallyClosed_comp B S hS f g hf.2.2 hg.2.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
