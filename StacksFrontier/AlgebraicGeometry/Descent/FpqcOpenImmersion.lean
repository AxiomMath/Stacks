module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget

/-!
# Being an open immersion is fpqc local on the base

A morphism of schemes is an *open immersion* when it induces an isomorphism onto an open
subscheme of its target. This file shows that the property is local on the target for the fpqc
precoverage: a morphism is an open immersion as soon as its base changes along the members of
one fpqc covering of the target are.

## Main results

* `Stacks.Descent.isOpenImmersion_isLocalAtTarget_fpqc`: being an open immersion is fpqc local
  on the base.

## Implementation notes

The three inputs that `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` asks of a morphism
property are all available for open immersions: Zariski locality on the target and stability
under base change are instances carried by `AlgebraicGeometry.IsOpenImmersion`, and descent
along surjective flat quasi-compact morphisms is
`AlgebraicGeometry.IsOpenImmersion.instDescendsAlong…`. Only the application of the criterion
was missing, so the content of the file is that application; the mathematics is in the inputs.

The statement is given at the same shape as the companion statements for flatness, local
finite presentation and quasi-finiteness — `MorphismProperty.IsLocalAtTarget P
Scheme.fpqcPrecoverage` — so that a consumer which has one of those in hand can use this one
without a translation step.

## References

* [Stacks Project, Tag 02L3](https://stacks.math.columbia.edu/tag/02L3)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-- **Stacks Project, Tag 02L3.** Being an open immersion is fpqc local on the base: `f` is an
open immersion if and only if its base change along every member of an fpqc covering of its
target is one. -/
@[stacks 02L3,
  ega "IV 2.7.1" "descent direction of (x)",
  sga "1 VIII 5.5" "open-immersion clause",
  sga "4 IV 8.5.5"]
instance isOpenImmersion_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@IsOpenImmersion : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  isLocalAtTarget_fpqcPrecoverage _

end Stacks.Descent

end
