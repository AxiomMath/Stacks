module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint

/-!
# Finite type at every point is locally of finite type

A morphism of schemes that is of finite type at every point of its source is locally of finite
type.

## Main results

* `AlgebraicGeometry.LocallyOfFiniteType.of_forall_finiteTypeAt`: a morphism of schemes of finite
  type at every point of its source is locally of finite type.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes that is of finite type at every point of its source is locally of finite
type. -/
theorem LocallyOfFiniteType.of_forall_finiteTypeAt {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ x : X, finiteTypeAt f x) : LocallyOfFiniteType f :=
  (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType) (Q := @RingHom.FiniteType)
    (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).left).mpr h

end AlgebraicGeometry
