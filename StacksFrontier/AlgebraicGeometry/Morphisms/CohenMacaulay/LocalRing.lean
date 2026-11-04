module

public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Dualizing.DepthLemmas.Ext
public import StacksFrontier.RingTheory.Depth.AlgebraMap
import StacksFrontier.RingTheory.Depth.RingEquiv

/-!
# Transport of Cohen–Macaulayness between local rings

A Noetherian local ring is Cohen–Macaulay exactly when it is a maximal Cohen–Macaulay module
over itself, and Cohen–Macaulayness only depends on the isomorphism class of the ring.

## Main results

* `isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay` identifies
  `IsCohenMacaulayLocalRing R` with `Module.IsMaximalCohenMacaulay R R`.
* `isCohenMacaulayLocalRing_iff_of_ringEquiv` transports Cohen–Macaulayness along a ring
  isomorphism of Noetherian local rings.
* `Module.depth_eq_depth_self_of_surjective_algebraMap`: for a surjective algebra map `A → B` of
  local rings, the depth of `B` along the maximal ideal of `A` is the self-depth of `B`.

## Implementation notes

`IsCohenMacaulayLocalRing` is defined as equality of the depth *supremum* with the support
dimension, whereas `Module.IsMaximalCohenMacaulay` uses `Module.depth`. The two agree because
the maximal ideal of a local ring does not annihilate the ring.

## References

* [Stacks Project, Tag 00N8](https://stacks.math.columbia.edu/tag/00N8)
-/

@[expose] public section

open RingTheory.Sequence

/-- A Noetherian local ring is Cohen–Macaulay exactly when it is a maximal Cohen–Macaulay
module over itself. -/
public theorem isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay (R : Type*) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] :
    IsCohenMacaulayLocalRing R ↔ Module.IsMaximalCohenMacaulay R R := by
  rw [isCohenMacaulayLocalRing_iff_isCohenMacaulayModule_self,
    IsCohenMacaulayModule, Module.IsMaximalCohenMacaulay]
  show Module.depthSup R (IsLocalRing.maximalIdeal R) R = Module.supportDim R R ↔ _
  rw [Module.supportDim_self_eq_ringKrullDim, Module.depthSup_eq_iSup,
    Module.depth, ite_eq_right (by simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top)]

/-- Cohen–Macaulayness of a Noetherian local ring depends only on its isomorphism class. -/
public theorem isCohenMacaulayLocalRing_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsCohenMacaulayLocalRing A ↔ IsCohenMacaulayLocalRing B := by
  rw [isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay A,
    isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay B]
  exact Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv e

/-- For a surjective algebra map between local rings, the depth of the target along the maximal
ideal of the source agrees with its own self-depth. -/
public theorem Module.depth_eq_depth_self_of_surjective_algebraMap {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Module.depth A (IsLocalRing.maximalIdeal A) B =
      Module.depth B (IsLocalRing.maximalIdeal B) B := by
  let _ : IsScalarTower A B B := IsScalarTower.of_algebraMap_eq' rfl
  rw [Module.depth_eq_depth_map_algebraMap (A := A) (B := B) hsurj,
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj]

