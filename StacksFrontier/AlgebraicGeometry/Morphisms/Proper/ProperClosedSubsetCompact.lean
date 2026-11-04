module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset

/-!
# Closed subsets proper over a quasi-compact base are compact

Let `f : X ⟶ S` be a morphism of schemes which is locally of finite type and let `Z` be a
closed subset of `X` which is proper over `S` in the sense of
`AlgebraicGeometry.IsProperOver`. If `S` is quasi-compact then `Z` is compact.

The Stacks Project uses this without comment whenever the base is Noetherian; a Noetherian
scheme is quasi-compact by definition, so `AlgebraicGeometry.IsNoetherian S` supplies the
`CompactSpace S` hypothesis below by instance resolution and no separate statement is needed
for that case.

## Main results

* `AlgebraicGeometry.compactSpace_subscheme_of_isProperOver`: the reduced induced closed
  subscheme on a closed subset proper over a quasi-compact base has compact underlying space.
* `AlgebraicGeometry.isCompact_of_isProperOver`: a closed subset proper over a quasi-compact
  base is compact.

## Implementation notes

`AlgebraicGeometry.IsProperOver f Z` is properness of the structure morphism of the reduced
induced closed subscheme cut out by `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Z`,
and a proper morphism is universally closed, hence quasi-compact. So that subscheme is
quasi-compact over a quasi-compact base, hence has compact underlying space by
`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`. The subset `Z` is then the range
of the closed immersion out of that subscheme — this is
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι` together with
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal` — and the range of a
continuous map out of a compact space is compact.

The hypothesis is stated as `CompactSpace S` rather than as quasi-compactness of the structure
morphism of `S`: for a scheme the two agree, by
`AlgebraicGeometry.compactSpace_iff_quasiCompact`, and `CompactSpace` is the form that both
`AlgebraicGeometry.IsNoetherian` and `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`
speak in.

## References

* [Stacks Project, Tag 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [CompactSpace S] (Z : Closeds X)

/-- The reduced induced closed subscheme on a closed subset proper over a quasi-compact base
has compact underlying space.

Properness of a closed subset is properness of that subscheme over the base, a proper morphism
is quasi-compact, and a scheme quasi-compact over a quasi-compact scheme is quasi-compact. -/
public theorem compactSpace_subscheme_of_isProperOver (hZ : IsProperOver f Z) :
    CompactSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  have : IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f) := hZ
  QuasiCompact.compactSpace_of_compactSpace
    ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f)

/-- A closed subset of a scheme which is proper over a quasi-compact base is compact.

The closed subset is the range of the closed immersion out of its reduced induced closed
subscheme, and that subscheme has compact underlying space by
`AlgebraicGeometry.compactSpace_subscheme_of_isProperOver`. -/
public theorem isCompact_of_isProperOver (hZ : IsProperOver f Z) : IsCompact (Z : Set X) := by
  have := compactSpace_subscheme_of_isProperOver f Z hZ
  have hrange : (Z : Set X) =
      Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rw [hrange]
  exact isCompact_range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.continuous

end AlgebraicGeometry

end
