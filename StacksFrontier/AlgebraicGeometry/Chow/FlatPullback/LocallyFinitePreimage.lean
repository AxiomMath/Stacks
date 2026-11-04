module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Sets.Closeds
public import StacksCore.Tactic.StacksAttribute

/-!
# Local finiteness is inherited by inverse images

Let `f : X ⟶ Y` be a morphism of schemes and let `{Z_i}_{i ∈ I}` be a locally finite collection
of closed subsets of `Y`. Then `{f^{-1}(Z_i)}_{i ∈ I}` is a locally finite collection of closed
subsets of `X` (Stacks 02R9). This is `LocallyFinite.preimage_continuous` applied to the
continuous map underlying `f`; this file registers the tag there and records the statement for
the supports of a family of quasi-coherent ideal sheaves.

## Main results

* `Stacks.Chow.locallyFinite_support_comap`: if the supports of a family of quasi-coherent ideal
  sheaves on `Y` are locally finite, so are the supports of their inverse images on `X`.

## Implementation notes

The hypothesis of Stacks 02R9 that `X` and `Y` be locally of finite type over a base is not
imposed: the statement concerns the underlying topological spaces only.

## References

* [Stacks Project, Tag 02R9](https://stacks.math.columbia.edu/tag/02R9)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

add_to_stacks 02R9 "the inverse image of a locally finite collection of subsets along a \
continuous map is locally finite" LocallyFinite.preimage_continuous

/-- If the supports of a family `W` of quasi-coherent ideal sheaves form a locally finite
collection on `Y`, so do the supports of the inverse images `(W i).comap f` on `X`. -/
theorem locallyFinite_support_comap {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*}
    (W : ι → Y.IdealSheafData) (hW : LocallyFinite fun i ↦ ((W i).support : Set Y)) :
    LocallyFinite fun i ↦ (((W i).comap f).support : Set X) := by
  simpa only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] using
    hW.preimage_continuous f.continuous

end Stacks.Chow

end
