module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Finite presentation over locally Noetherian schemes

Over a locally Noetherian base, a morphism locally of finite type is locally of finite
presentation, and a morphism of finite type is of finite presentation.

## Main results

* `AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType`
  upgrades local finite type to local finite presentation over a locally Noetherian scheme.
* `AlgebraicGeometry.finitePresentation_of_finiteType` upgrades finite type to finite
  presentation over a locally Noetherian scheme.

## Implementation notes

The first part is Mathlib's instance between its morphism-property typeclasses. In the second
part, finite type is represented by `LocallyOfFiniteType` and `QuasiCompact`.

## References

* [Stacks Project, Tag 01TX](https://stacks.math.columbia.edu/tag/01TX)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory LocallyOfFiniteType

universe u

add_to_stacks 01TX "part (1)"
  AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType
add_to_sga "1 IX 4.10" "more general"
  AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType
add_to_sga "1 IX 4.12" "partial"
  AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType
add_to_sga "1 IX 4.7" "partial"
  AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType
add_to_sga "3 V 6.1" "partial"
  AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType

/-- **Stacks Project, Tag 01TX, part (2).** A morphism of finite type over a locally Noetherian
scheme is of finite presentation. -/
@[stacks 01TX "part (2)"]
theorem finitePresentation_of_finiteType {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] :
    AlgebraicGeometry.FinitePresentation f :=
  ⟨inferInstance, inferInstance, by
    let _ := isLocallyNoetherian f; infer_instance⟩

end AlgebraicGeometry
