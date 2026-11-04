module

public import StacksFrontier.AlgebraicGeometry.InternalHomLocalKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveExtensionGate.Basic

/-!
# The reflexive hull of a coherent module is coherent and reflexive

[Stacks, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH) refers to Lemma
[0AY4](https://stacks.math.columbia.edu/tag/0AY4) for two facts about the reflexive hull
`F^{∨∨}` of a coherent module `F` on an integral locally Noetherian scheme: that it is coherent,
and that it is reflexive.  Both follow in one step each from the local kernel presentation of
[Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ), through which
`Stacks.AlgebraicGeometry.InternalHomLocalKernel.isCoherent_dualSheaf` gives coherence of a dual.

## Main results

* `isCoherent_reflexiveHull`: the reflexive hull of a coherent module on a locally Noetherian
  scheme is coherent.  Integrality is not used.
* `isReflexive_reflexiveHull`: on an integral locally Noetherian scheme the reflexive hull of a
  coherent module is reflexive.

## Implementation notes

Coherence is coherence of a dual applied twice, since `F^{∨∨} = (F^∨)^∨`; reflexivity is
`Stacks.AlgebraicGeometry.ReflexiveStalkCriterion.isCoherent_and_isReflexive_dualSheaf` applied
to `F^∨`, with its coherence-of-duals hypothesis discharged by the same theorem.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 0AY4](https://stacks.math.columbia.edu/tag/0AY4)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexiveHull

universe u

namespace Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension

variable {X : Scheme.{u}}

/-- **The reflexive hull of a coherent module on a locally Noetherian scheme is coherent.**
This is coherence of a dual (Stacks Tag 01Y2 at target the structure sheaf) applied twice.
Integrality of `X` is not used. -/
theorem isCoherent_reflexiveHull [IsLocallyNoetherian X] (F : X.Modules)
    (hF : F.IsCoherent) : (reflexiveHull F).IsCoherent :=
  InternalHomLocalKernel.isCoherent_dualSheaf (dualSheaf F)
    (InternalHomLocalKernel.isCoherent_dualSheaf F hF)

/-- **The reflexive hull of a coherent module on an integral locally Noetherian scheme is
reflexive.**  This is the sheaf-level reflexivity of a dual, applied to `F^∨`, with its
coherence-of-duals hypothesis discharged. -/
theorem isReflexive_reflexiveHull [IsIntegral X] [IsLocallyNoetherian X] (F : X.Modules)
    (hF : F.IsCoherent) : IsReflexive (reflexiveHull F) :=
  (ReflexiveStalkCriterion.isCoherent_and_isReflexive_dualSheaf
    (fun G hG => InternalHomLocalKernel.isCoherent_dualSheaf G hG) (dualSheaf F)
    (InternalHomLocalKernel.isCoherent_dualSheaf F hF)).2

end Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension

end
