module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.LocalDescription
public import StacksFrontier.RingTheory.CompleteIntersection.QuasiFinite

/-!
# The canonical diagram of Tag 0FL9 for a quasi-finite algebra

Remark 0FL9 states its construction for a *quasi-finite* `A`-algebra `B` presented as
`A[x₁, …, xₙ]/(f₁, …, fₙ)`. Quasi-finiteness enters only to make such a presentation a relative
global complete intersection, which is what `Stacks.DeRham.cotangentDiagram` and
`Stacks.DeRham.presentationFunnyMap` assume:
`Algebra.Presentation.instIsRelativeGlobalCompleteIntersectionOfQuasiFinite` supplies that
hypothesis by instance search from `Algebra.QuasiFinite A B`, so the source's case is an instance
of those constructions rather than a separate statement.

This file records the displayed diagram of the remark, `Stacks.DeRham.cotangentDiagram`, as part
of Tag 0FL9: the structure `Stacks.DeRham.CotangentDiagram` is the type of such diagrams, and
`cotangentDiagram` is the witness, so the diagram is exhibited and not just described.

## References

* [Stacks Project, Tag 0FL9](https://stacks.math.columbia.edu/tag/0FL9)
-/

@[expose] public section

namespace Stacks.DeRham

add_to_stacks 0FL9 "the displayed diagram itself, instantiated at a square presentation which is a \
  relative global complete intersection: the short exact sequence \
  0 -> B (x)_A Omega_{A/Z} -> B (x)_P Omega_{P/Z} -> Omega_{P/A} (x)_P B -> 0 of B-modules \
  whose outer terms are free of rank n, the two-term complex out of the conormal module into \
  it, the commuting square identifying that complex with the cotangent complex of the \
  presentation, and the identification of the cokernel with Omega_{B/Z} under which the \
  base-change map from Omega_{A/Z} becomes the quotient map. The type of such diagrams is the \
  structure Stacks.DeRham.CotangentDiagram; this is the witness, so the diagram is exhibited \
  and not just described" Stacks.DeRham.cotangentDiagram

end Stacks.DeRham

end
