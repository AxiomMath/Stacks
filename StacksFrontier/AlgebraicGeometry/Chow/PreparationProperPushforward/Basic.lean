module

public import Mathlib.Topology.Spectral.Prespectral
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.LocallyFiniteImage
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-compact images of locally finite families

For a spectral map to a prespectral space, the closures of the images of a locally finite
family of subsets form a locally finite family. This applies in particular to a quasi-compact
morphism of schemes, and is the topological input to the construction of proper pushforward of
cycles.

## Main results

* `locallyFinite_closure_image_of_quasiCompact` — the root-namespace spelling of
  `Stacks.Chow.locallyFinite_closure_image_of_isSpectralMap`, which is where Stacks 02R2 is
  registered and where the proof lives.

## Implementation notes

The Chow situation, local finite type assumptions, and closedness assumptions on the original
subsets are unnecessary for the topological argument. A quasi-compact scheme morphism is a
spectral map, and the underlying topological space of a scheme is prespectral. The collection
is represented by a family of sets and Mathlib's `LocallyFinite` predicate. Since the
statement mentions no scheme, it is placed in the root namespace alongside Mathlib's
`LocallyFinite` and `IsSpectralMap` API rather than in `AlgebraicGeometry`.

## References

* [Stacks Project, Tag 02R2](https://stacks.math.columbia.edu/tag/02R2)
-/

@[expose] public section

universe u v w

/-- Under a spectral map to a prespectral space, the closures of the images of a locally finite
family of subsets are locally finite.

This is the root-namespace spelling of `Stacks.Chow.locallyFinite_closure_image_of_isSpectralMap`
of `StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.LocallyFiniteImage`, which carries
Stacks 02R2 and holds the proof. The name is kept because it is applied unqualified, at the
root, from outside the library. -/
theorem locallyFinite_closure_image_of_quasiCompact
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace Y] (f : X → Y) (hf : IsSpectralMap f)
    {I : Type w} (Z : I → Set X)
    (hZ_locallyFinite : LocallyFinite Z) :
    LocallyFinite (fun i ↦ closure (f '' Z i)) :=
  Stacks.Chow.locallyFinite_closure_image_of_isSpectralMap f hf Z hZ_locallyFinite
