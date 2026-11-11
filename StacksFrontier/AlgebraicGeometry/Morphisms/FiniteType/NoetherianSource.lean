module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# A scheme of finite type over a Noetherian scheme is Noetherian

If `f : X ⟶ S` is locally of finite type and `S` is locally Noetherian, then `X` is locally
Noetherian; if moreover `f` is quasi-compact and `S` is Noetherian, then `X` is Noetherian.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_of_locallyOfFiniteType` — the source of a morphism locally
  of finite type to a locally Noetherian scheme is locally Noetherian; together with
  `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType` (the Noetherian case) this is Tag 01T6.
* `AlgebraicGeometry.isLocallyNoetherian_of_isFinite` and
  `AlgebraicGeometry.isNoetherian_of_isFinite` — the two cases for a finite morphism.

## Implementation notes

The locally Noetherian case is Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`; it is restated below as
`isLocallyNoetherian_of_locallyOfFiniteType` so that the Stacks attribute sits on a declaration
of this library. Compactness of the source is the only thing the
Noetherian case adds: `IsNoetherian` is `IsLocallyNoetherian` together with `CompactSpace`, and the
latter comes from quasi-compactness of `f` over a compact target, by Mathlib's
`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`. The Noetherian case, with `f`
quasi-compact and locally of finite type (that is, of finite type) and `S` Noetherian, is
`AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`, stated and tagged in
`StacksFrontier/AlgebraicGeometry/SchemeTheoreticImage/Basic.lean`; it is not restated here.

A finite morphism is locally of finite type (`AlgebraicGeometry.IsFinite`'s instance of
`LocallyOfFiniteType`) and quasi-compact, so both cases apply to it with no further argument.

## References

* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

add_to_stacks 01T6 "locally Noetherian case: `f` locally of finite type, `S` locally Noetherian"
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
add_to_ega "I 6.3.7" "more general" AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
add_to_ega "II 7.4.1" "partial" AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
add_to_ega "IV 1.3.3" AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
add_to_ega "IV 1.3.5" "identity base change"
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
add_to_ega "IV 4.7.3" "partial" AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian

/-- **Stacks 01T6, locally Noetherian case.** If `f : X ⟶ S` is locally of finite type and `S` is
locally Noetherian, then `X` is locally Noetherian. This restates Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`; the Noetherian case is
`AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`. -/
@[stacks 01T6 "locally Noetherian case: `f` locally of finite type, `S` locally Noetherian"]
theorem isLocallyNoetherian_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian f

/-- The source of a finite morphism with locally Noetherian target is locally Noetherian. -/
theorem isLocallyNoetherian_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [IsLocallyNoetherian S] : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian f

/-- The source of a finite morphism with Noetherian target is Noetherian. -/
theorem isNoetherian_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [IsNoetherian S] : IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

end AlgebraicGeometry

end
