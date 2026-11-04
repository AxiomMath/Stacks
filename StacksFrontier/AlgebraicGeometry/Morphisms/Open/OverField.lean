module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# A scheme over a field is universally open over that field

The structure morphism `X ⟶ Spec k` of a scheme over a field is universally open: every base
change of it is an open map on underlying spaces. In particular, for a field extension `K / k`
the projection `X_K ⟶ X` of the base change is open.

## Main results

* `AlgebraicGeometry.universallyOpen_of_field` — the statement itself.
* `AlgebraicGeometry.isOpenMap_pullback_fst_specMap_algebraMap` — the projection `X_K ⟶ X` of the
  base change along a field extension is open.

## Implementation notes

`Spec k` is an integral scheme with a one-point underlying space, and Mathlib has the instance
making every morphism to such a scheme universally open; it reduces to the openness of
`Spec (R ⊗_k S) ⟶ Spec R` over a field. So both results below follow from instances.

## References

* [Stacks Project, Tag 0383](https://stacks.math.columbia.edu/tag/0383)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Let `k` be a field and let `X` be a scheme over `k`. The structure morphism `X ⟶ Spec k` is
universally open. -/
@[stacks 0383]
public theorem universallyOpen_of_field (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : UniversallyOpen f :=
  inferInstance

/-- For a field extension `K / k` and a scheme `X` over `k`, the projection `X_K ⟶ X` of the base
change is an open map: it is a base change of the universally open `Spec K ⟶ Spec k`. -/
public theorem isOpenMap_pullback_fst_specMap_algebraMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    IsOpenMap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isOpenMap

end AlgebraicGeometry

end
