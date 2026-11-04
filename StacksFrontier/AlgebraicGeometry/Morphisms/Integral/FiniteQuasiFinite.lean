module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite morphisms are quasi-finite

A finite morphism of schemes is quasi-finite: it is of finite type (locally of finite type and
quasi-compact) and locally quasi-finite.

## Main results

* `AlgebraicGeometry.quasiFinite_of_isFinite`: a finite morphism is quasi-finite.

## Implementation notes

A quasi-finite morphism is expressed by the three unbundled conditions `LocallyOfFiniteType`,
`QuasiCompact` and `LocallyQuasiFinite`. Each is supplied by a Mathlib instance for finite
morphisms.

## References

* [Stacks Project, Tag 02NU](https://stacks.math.columbia.edu/tag/02NU)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A finite morphism of schemes is quasi-finite: it is locally of finite type, quasi-compact
and locally quasi-finite. -/
@[stacks 02NU]
theorem quasiFinite_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] :
    (LocallyOfFiniteType f ∧ QuasiCompact f) ∧ LocallyQuasiFinite f :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end AlgebraicGeometry
