module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStackKolmogorov
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.Topology.Sober.Defs

/-!
# The points of a decent locally Noetherian algebraic stack (Stacks 0GW8)

Let `𝒳` be a decent, locally Noetherian algebraic stack over `S`. Then the space of points
`|𝒳|` of Stacks 04XL is a sober, locally Noetherian topological space: every irreducible
closed subset of it has a *unique* generic point, and every one of its points has a Noetherian
open neighbourhood.

Soberness in the sense of Stacks 004X is `StacksSober`, which `stacksSober_iff_t0_and_quasiSober`
splits as `T0Space` together with `QuasiSober`. The quasi-sober half is Stacks 0GVX and the
locally Noetherian half is Stacks 0DQI, part (1); both read local Noetherianity of `𝒳` as the
smooth-local atlas condition of Stacks 04YF at `AlgebraicGeometry.IsLocallyNoetherian`, and
neither uses decency. The Kolmogorov half is Stacks 0GW7 and uses decency alone.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.stacksSober_and_isLocallyNoetherianSpace_points`:
  **Stacks 0GW8**.

## Implementation notes

The Kolmogorov half is `AlgebraicGeometry.Stack.t0Space_points_of_isDecent`, applied to the
fibred category underlying `𝒳` and to its algebraicity witness. Decency enters the statement as
`hdecent`, because the statement is about decent stacks, and feeds that lemma and nothing else.

Local Noetherianity is not stated over a named predicate "locally Noetherian algebraic stack",
for the reason recorded in `StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack`:
Stacks 04YG has no library site, and the existential atlas condition of Stacks 04YF is what the
proofs of Stacks 0DQI and Stacks 0GVX consume.

The topology of Stacks 04XL on the point space is a local instance here, as it is in the source
of Stacks 0GW7, so that `StacksSober` and `IsLocallyNoetherianSpace` read directly; it is not a
global instance.

## References

* [Stacks Project, Tag 004X](https://stacks.math.columbia.edu/tag/004X)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 0DQI](https://stacks.math.columbia.edu/tag/0DQI)
* [Stacks Project, Tag 0GVX](https://stacks.math.columbia.edu/tag/0GVX)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
* [Stacks Project, Tag 0GW7](https://stacks.math.columbia.edu/tag/0GW7)
* [Stacks Project, Tag 0GW8](https://stacks.math.columbia.edu/tag/0GW8)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

open TopologicalSpace

attribute [local instance] pointTopology

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GW8.** The space of points of Stacks 04XL of a decent, locally Noetherian
algebraic stack over `S` is a sober, locally Noetherian topological space.

Soberness is Kolmogorov together with quasi-soberness. The Kolmogorov half is Stacks 0GW7,
which decency supplies; the quasi-sober half is Stacks 0GVX and local Noetherianity of the
space is Stacks 0DQI, part (1), both from the locally Noetherian smooth chart of Stacks 04YF. -/
@[stacks 0GW8]
theorem stacksSober_and_isLocallyNoetherianSpace_points
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hdecent : Stack.IsDecent B S hS 𝒳.val)
    (hN : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳) :
    StacksSober (Stack.points B S hS 𝒳.val.val 𝒳.val.property) ∧
      IsLocallyNoetherianSpace (Stack.points B S hS 𝒳.val.val 𝒳.val.property) :=
  ⟨stacksSober_iff_t0_and_quasiSober.mpr
      ⟨Stack.t0Space_points_of_isDecent.{u, w} B S hS 𝒳.val 𝒳.property hdecent,
        quasiSober_points_of_isLocallyNoetherian B S hS 𝒳 hN⟩,
    isLocallyNoetherianSpace_points_of_isLocallyNoetherian B S hS 𝒳 hN⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
