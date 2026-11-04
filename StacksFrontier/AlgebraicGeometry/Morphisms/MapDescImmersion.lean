module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The comparison of fibre products over two bases

Let `f : X ⟶ T` and `g : Y ⟶ T` be morphisms of schemes and let `h : T ⟶ S`. The canonical
morphism `X ×[T] Y ⟶ X ×[S] Y`, written `CategoryTheory.Limits.pullback.mapDesc f g h`, is a
base change of the diagonal `T ⟶ T ×[S] T` of `h`
(`AlgebraicGeometry.pullback_map_diagonal_isPullback`). Every property of the diagonal that is
stable under base change is therefore inherited by it: since a diagonal is always an immersion,
the comparison morphism is an immersion; if `h` is separated it is a closed immersion; and if `h`
is quasi-separated it is quasi-compact.

## Main results

* `AlgebraicGeometry.isImmersion_pullbackMapDesc`: the comparison morphism is an immersion.
* `AlgebraicGeometry.isClosedImmersion_pullbackMapDesc`: it is a closed immersion if `h` is
  separated.
* `AlgebraicGeometry.quasiCompact_pullbackMapDesc`: it is quasi-compact if `h` is
  quasi-separated.

## Implementation notes

The first two statements are Mathlib's instances on `pullback.mapDesc`, restated here as named
theorems; the third is deduced in the same way, from the quasi-compactness of the diagonal of a
quasi-separated morphism and the stability of quasi-compact morphisms under base change.

## References

* [Stacks Project, Tag 01KR](https://stacks.math.columbia.edu/tag/01KR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y T S : Scheme.{u}} (f : X ⟶ T) (g : Y ⟶ T) (h : T ⟶ S)

/-- The canonical morphism `X ×[T] Y ⟶ X ×[S] Y` is an immersion. -/
@[stacks 01KR "immersion"]
theorem isImmersion_pullbackMapDesc : IsImmersion (pullback.mapDesc f g h) :=
  inferInstance

/-- If `h : T ⟶ S` is separated, the canonical morphism `X ×[T] Y ⟶ X ×[S] Y` is a closed
immersion. -/
@[stacks 01KR "closed immersion if T → S is separated"]
theorem isClosedImmersion_pullbackMapDesc [IsSeparated h] :
    IsClosedImmersion (pullback.mapDesc f g h) :=
  inferInstance

/-- If `h : T ⟶ S` is quasi-separated, the canonical morphism `X ×[T] Y ⟶ X ×[S] Y` is
quasi-compact, being a base change of the quasi-compact diagonal of `h`. -/
@[stacks 01KR "quasi-compact if T → S is quasi-separated"]
theorem quasiCompact_pullbackMapDesc [QuasiSeparated h] :
    QuasiCompact (pullback.mapDesc f g h) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (pullback_map_diagonal_isPullback f g h)
    inferInstance

end AlgebraicGeometry
