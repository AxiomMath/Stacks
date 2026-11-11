module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOfComplex
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleSupportSerreFull
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.RingTheory.Dualizing.CanonicalModuleDepth
public import StacksFrontier.Topology.Dimension.DimensionFunctionConnected
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection

/-!
# Serre's condition for the dualizing module of a dualizing complex

Let `X` be a connected Noetherian scheme with a dualizing complex `K` and let `ω` be the
associated dualizing module, the cohomology sheaf of `K` in the leftmost degree in which `K` has
nonvanishing cohomology (`Stacks.Duality.IsDualizingModuleOf`). This file records the `(S₂)`
clause of [Stacks, Tag 0AWK] on its own: `ω` satisfies Serre's condition `(S₂)`.

## Main results

* `Stacks.Duality.IsDualizingModuleOf.sheafHasPropertySk_two` — **[Stacks, Tag 0AWK]**, the
  `(S₂)` clause.

## Implementation notes

The statement is read off
`Stacks.Duality.IsDualizingModuleOf.supp_eq_and_isCoherent_and_sheafHasPropertySk_two`, which
proves all the assertions of [Stacks, Tag 0AWK] together. There the stalk of `ω` at every point
is shown either to vanish or to be the canonical module of the local ring
(`Stacks.Duality.IsDualizingModuleOf.stalk_dichotomy`), and `(S₂)` follows from the depth bound
`Dualizing.min_two_le_depth_canonicalModule` for the canonical module of a Noetherian local ring.
Serre's condition is `AlgebraicGeometry.SheafHasPropertySk` of [Stacks, Tag 0341].

## References

* [Stacks Project, Tag 0AWK](https://stacks.math.columbia.edu/tag/0AWK)
* [Stacks Project, Tag 0AWE](https://stacks.math.columbia.edu/tag/0AWE)
* [Stacks Project, Tag 0341](https://stacks.math.columbia.edu/tag/0341)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w

namespace Stacks.Duality

/-- **Stacks Project, Tag 0AWK**, the `(S₂)` clause. The dualizing module of a dualizing complex
on a connected Noetherian scheme satisfies Serre's condition `(S₂)`. -/
@[stacks 0AWK "the (S₂) clause"]
public theorem IsDualizingModuleOf.sheafHasPropertySk_two {X : Scheme.{u}} [IsNoetherian X]
    [ConnectedSpace X] [HasDerivedCategory.{w} X.Modules] {ω : X.Modules}
    {K : DerivedCategory X.Modules} {n : ℤ} (h : IsDualizingModuleOf ω K n) :
    SheafHasPropertySk X ω 2 :=
  h.supp_eq_and_isCoherent_and_sheafHasPropertySk_two.2.2

end Stacks.Duality

end
