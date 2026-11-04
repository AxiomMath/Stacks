module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism

/-!
# The versal situation (Stacks 0DQU)

Stacks 0DQU is the standing situation of the section on versal rings: an algebraic stack `𝒳`
locally of finite type over a locally Noetherian scheme `S`. Every statement about versal rings
and deformation categories at the finite-type field-valued points of `𝒳` is made in it, so it is
recorded here as a structure packaging the base, the stack and the two finiteness hypotheses.

## Main definitions

* `AlgebraicGeometry.Stack.VersalSituation`: **Stacks 0DQU**.

## Implementation notes

Being an algebraic stack is carried by membership in the 2-category
`AlgebraicGeometry.Stack.AlgebraicStacks` of **Stacks 03YP**, so it is not a separate field. The
big fppf site `B` and its containment of `S` are what that 2-category is indexed by, and are
therefore fields too.

Local finite type is `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFiniteType`
(**Stacks 06FS**, part (1)) of the canonical 1-morphism
`AlgebraicGeometry.Stack.structureMorphism` from `𝒳` to the algebraic stack represented by `S`,
which is the structure morphism whose properties **Stacks 050D** reads off; that the target is an
algebraic stack at all is **Stacks 026O** for the big fppf site of a scheme, proved alongside
**Stacks 03YS**, part (3).

Local Noetherianness of the base is an instance-implicit field, so that it is available by
instance search wherever the situation is in context; `attribute [instance]` on the projection is
what makes that work for a field of a structure.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 0DQU](https://stacks.math.columbia.edu/tag/0DQU)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- **Stacks 0DQU.** The versal situation: an algebraic stack locally of finite type over a
locally Noetherian scheme. -/
@[stacks 0DQU]
structure VersalSituation where
  /-- The big fppf site in which the stack is represented. -/
  B : BigFppfSite.{u}
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The base belongs to the big site. -/
  hS : B.Contains S
  /-- The algebraic stack over the base. -/
  𝒳 : AlgebraicStacks.{u, w} B S hS
  /-- The base is locally Noetherian. -/
  [locallyNoetherian : IsLocallyNoetherian S]
  /-- The structure morphism of the stack to the base is locally of finite type. -/
  locallyFiniteType : AlgebraicStacks.IsLocallyOfFiniteType B S hS (structureMorphism B S hS 𝒳)

attribute [instance] VersalSituation.locallyNoetherian

end AlgebraicGeometry.Stack

end
