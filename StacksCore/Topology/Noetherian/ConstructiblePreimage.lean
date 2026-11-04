module

public import Mathlib.Topology.Constructible

/-!
# Preimages of constructible sets

## Main results

* `isConstructibleSet_preimage` (Stacks 053Y): for a continuous map `f : X → Y` from a Noetherian
  space and `E ⊆ Y` constructible, the preimage `f ⁻¹' E` is constructible.

Constructibility uses Mathlib's `Topology.IsConstructible`. In a Noetherian space, every
subset is retrocompact, so Mathlib's preimage theorem applies to any continuous map.

## References

* [Stacks Project, Tag 053Y](https://stacks.math.columbia.edu/tag/053Y)
-/

@[expose] public section

/-- **Stacks 053Y.** Let `f : X → Y` be a continuous map from a Noetherian topological space. If
`E ⊆ Y` is constructible in `Y`, then `f ⁻¹' E` is constructible in `X`: preimages preserve opens,
and retrocompactness is automatic in a Noetherian space. -/
@[stacks 053Y]
theorem isConstructibleSet_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace X]
    {f : X → Y} (hf : Continuous f) {E : Set Y}
    (hE : Topology.IsConstructible E) :
    Topology.IsConstructible (f ⁻¹' E) :=
  hE.preimage hf fun _ _ _ ↦ fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _
