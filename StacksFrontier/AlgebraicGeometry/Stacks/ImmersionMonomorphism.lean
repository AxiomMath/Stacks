module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe

/-!
# An immersion of algebraic stacks is a monomorphism

An immersion of algebraic stacks is a monomorphism. Both notions are the Section 04XB relative
property of a 1-morphism representable by algebraic spaces: an immersion is Stacks 04YL part (3), a
monomorphism is Stacks 04ZW.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_of_isImmersion`: an immersion of
  algebraic stacks is a monomorphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasRelativeProperty_monomorphisms_of_isImmersion`:
  the same conclusion read through `AlgebraicGeometry.Stack.HasRelativeProperty` (Stacks 03YK) at
  `CategoryTheory.MorphismProperty.monomorphisms`.

## Implementation notes

Representability by algebraic spaces is the first conjunct of both notions. The structural morphism
of a representing algebraic space is a morphism of presheaves, which is the form in which
`AlgebraicGeometry.Space.mono_of_isImmersion` concludes, while
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` asks for monomorphy in the category of
algebraic spaces over `S`; the two readings agree by parts (1) and (2) of Stacks 042M,
`AlgebraicGeometry.Space.mono_hom_iff_mono`.

The second result is stated separately because it is not available unconditionally.
`AlgebraicGeometry.Stack.HasRelativeProperty` takes locality of the property at the target for the
fppf precoverage as an instance argument, and for the monomorphisms of algebraic spaces over `S`
that is Stacks 042D, a result this library does not have; it is therefore a hypothesis rather than
a looked-up instance. The first result needs no such hypothesis:
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` is the body of
`AlgebraicGeometry.Stack.HasRelativeProperty` at the monomorphisms written out, so it is the same
proposition with the unavailable hypothesis dropped.

## References

* [Stacks Project, Tag 042D](https://stacks.math.columbia.edu/tag/042D)
* [Stacks Project, Tag 042M](https://stacks.math.columbia.edu/tag/042M)
* [Stacks Project, Tag 042R](https://stacks.math.columbia.edu/tag/042R)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- An immersion of algebraic stacks over `S` is a monomorphism. -/
@[stacks 0504]
theorem isMonomorphism_of_isImmersion (f : 𝒳 ⟶ 𝒴) (hf : IsImmersion B S hS f) :
    IsMonomorphism B S hS f :=
  ⟨hf.1, fun U y hy F hF he =>
    (Space.mono_hom_iff_mono B S hS _).1
      (Space.mono_of_isImmersion B S hS (hf.2 U y hy F hF he))⟩

/-- An immersion of algebraic stacks over `S` has the relative property
`AlgebraicGeometry.Stack.HasRelativeProperty` (Stacks 03YK) at
`CategoryTheory.MorphismProperty.monomorphisms`, given that the monomorphisms of algebraic spaces
over `S` are local at the target for the fppf precoverage. -/
theorem hasRelativeProperty_monomorphisms_of_isImmersion
    [(MorphismProperty.monomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (f : 𝒳 ⟶ 𝒴) (hf : IsImmersion B S hS f) :
    Stack.HasRelativeProperty B S hS
      (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS)) f.hom hf.1 :=
  (isMonomorphism_of_isImmersion B S hS f hf).2

end AlgebraicGeometry.Stack.AlgebraicStacks

end
