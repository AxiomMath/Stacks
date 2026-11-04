module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reduction of a scheme is universally homeomorphic to the scheme

The canonical closed immersion from the reduction of a scheme to the scheme is a universal
homeomorphism.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_nilradical_subschemeι`: the canonical morphism from
  the reduction of a scheme is a universal homeomorphism.

## Implementation notes

The reduction is the closed subscheme cut out by the nilradical ideal sheaf. The criterion
`AlgebraicGeometry.universalHomeomorphism_iff_integral_universallyInjective_surjective` reduces
the claim to surjectivity, which holds because
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι` identifies the range of the inclusion
with the support of the ideal sheaf and `AlgebraicGeometry.Scheme.support_nilradical` identifies
that support with the whole space. The conclusion is an instance, so it is available to any use
of the canonical map.

## References

* [Stacks Project, Tag 054M](https://stacks.math.columbia.edu/tag/054M)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The reduction of a scheme is universally homeomorphic to the scheme through its canonical
closed immersion. -/
@[stacks 054M, ega "IV 2.4.8" "(ii) univ. homeo"]
instance universalHomeomorphism_nilradical_subschemeι (X : Scheme.{u}) :
    UniversalHomeomorphism X.nilradical.subschemeι :=
  (universalHomeomorphism_iff_integral_universallyInjective_surjective _).2
    ⟨inferInstance, inferInstance, by
      simp [surjective_iff, ← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
        Scheme.support_nilradical]⟩

end AlgebraicGeometry

end
