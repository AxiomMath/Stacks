module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjUniversallyClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtaleChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Space

/-!
# The relative Proj of an algebraic space is universally closed

In Situation 0849 let `π : Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of Stacks 084C,
`AlgebraicGeometry.Space.RelativeProjSituation.π`. This file proves Stacks 084H: if
`𝒪_X → 𝒜₀` is integral and `𝒜` is of finite type as an `𝒜₀`-algebra, then `π` is universally
closed.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.universallyClosed_π`:
  **Stacks 084H.**

## Implementation notes

**The hypotheses.** Integrality of `𝒪_X → 𝒜₀` (Stacks 0820, 0821) and finite type of `𝒜` over
`𝒜₀` are conditions on a quasi-coherent algebra on an algebraic space that are read étale
locally: on the restriction `g^*𝒜` to every étale scheme point `g : U ⟶ X`. That restriction is
the one of Stacks 084B (`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints`), and
the conditions on it are the affine-local conditions of the case of schemes,
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.IsIntegralInDegreeZero` and
`…SheafGradedAlgebra.IsFiniteTypeOverDegreeZero`; the reading at every étale point is
`AlgebraicGeometry.Space.RelativeProjSituation.HoldsAtEtalePoints`. The restriction `g^*𝒜` is
that of the re-presentation of `𝒜` with sections in the universe `u`, identified with `𝒜`
sectionwise by `AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebraEquiv`.

**The proof** is the source's. Choose a surjective étale scheme point `g : U ⟶ X`. By Stacks 084B
the base change of `π` along `g` is the structure morphism of `Proj_U(g^*𝒜)`, universally closed
by the case of schemes, Stacks 07ZZ
(`Stacks.AlgebraicGeometry.RelativeProjUniversallyClosed.universallyClosed_toBase`), and
universal closedness descends along `g` by Stacks 03IT; the last two steps are
`AlgebraicGeometry.Space.RelativeProjPoints.universallyClosed_of_etalePoint`.

## References

* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 0821](https://stacks.math.columbia.edu/tag/0821)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 084H](https://stacks.math.columbia.edu/tag/084H)
* [Stacks Project, Tag 03IT](https://stacks.math.columbia.edu/tag/03IT)
* [Stacks Project, Tag 07ZZ](https://stacks.math.columbia.edu/tag/07ZZ)
-/

@[expose] public section

universe u m

open CategoryTheory
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace AlgebraicGeometry.Space

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- **Stacks 084H.** In Situation 0849, if `𝒪_X → 𝒜₀` is integral and `𝒜` is of finite type as
an `𝒜₀`-algebra, the structure morphism `π : Proj_X(𝒜) ⟶ X` of the relative homogeneous spectrum
is universally closed.

Both hypotheses are read étale locally, on the restriction `g^*𝒜` of Stacks 084B to every étale
scheme point `g` of `X` (taken through the `u`-small re-presentation of `𝒜`, identified with `𝒜`
by `smallAlgebraEquiv`); by `holdsAtEtalePoints_isIntegralInDegreeZero_iff` and
`holdsAtEtalePoints_isFiniteTypeOverDegreeZero_iff` it suffices at one surjective étale scheme
point. -/
@[stacks 084H]
theorem universallyClosed_π
    (hint : s.HoldsAtEtalePoints SheafGradedAlgebra.IsIntegralInDegreeZero)
    (hft : s.HoldsAtEtalePoints SheafGradedAlgebra.IsFiniteTypeOverDegreeZero) :
    UniversallyClosed s.site s.base s.containsBase s.π.hom := by
  rw [s.π_hom]
  obtain ⟨T, g, hgEt, hgSurj⟩ := RelativeProjPoints.exists_etalePoint s.space.property
  exact s.relativeProjPoints.universallyClosed_of_etalePoint s.space.property T g hgEt hgSurj
    (Stacks.AlgebraicGeometry.RelativeProjUniversallyClosed.universallyClosed_toBase _
      (hint T g hgEt) (hft T g hgEt))

end RelativeProjSituation

end AlgebraicGeometry.Space

end
