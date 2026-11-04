module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute

/-!
# Locally finite type morphisms over locally Noetherian schemes

A morphism which is locally of finite type over a locally Noetherian scheme is
quasi-separated.

## Main results

* `AlgebraicGeometry.quasiSeparated_of_locallyOfFiniteType`: a morphism locally of finite type
  with locally Noetherian target is quasi-separated.

## References

* [Stacks Project, Tag 01T7](https://stacks.math.columbia.edu/tag/01T7)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- A morphism locally of finite type over a locally Noetherian scheme is quasi-separated. -/
@[stacks 01T7]
instance quasiSeparated_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] : QuasiSeparated f := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  infer_instance

end AlgebraicGeometry
