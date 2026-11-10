module

public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Dimension.DimensionLEOne
import StacksCore.Tactic.StacksAttribute

/-!
# H-projectivity in dimension at most one

A proper scheme of dimension at most one over a field `k` is H-projective over `k`. That a
separated finite type scheme of dimension at most one over `k` is an open subscheme of an
H-projective one, missing only finitely many closed points, is [Stacks, Tag 0BXV],
`Stacks.CurveProjectiveCompletion.exists_projective_completion_of_dimension_le_one` in
`StacksFrontier/AlgebraicGeometry/Variety/Curve/ProjectiveCompletion.lean`.

The statement here rests on [Stacks, Tag 0A25]: a separated finite type scheme of dimension at
most one over a field is H-quasi-projective, i.e. admits a quasi-compact immersion into `ℙⁿ_k`
over `Spec k`.

For a proper `X` the immersion is automatically closed, because `ℙⁿ_k` is separated over `k`, so
the immersion is itself proper and hence has closed image; this is the characterisation of
H-projectivity as H-quasi-projectivity together with properness, [Stacks, Tag 0BCL].

## Main results

* `AlgebraicGeometry.isProjectiveMorphism_of_topologicalKrullDim_le_one`: a proper scheme of
  topological Krull dimension at most one over a field is H-projective over that field.
  [Stacks, Tag 0A26] itself is registered at
`Stacks.HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one`
  in `StacksFrontier/AlgebraicGeometry/HQuasiProjectiveDimensionOne/Basic.lean`.

## Implementation notes

H-projectivity is `AlgebraicGeometry.IsProjectiveMorphism`, the predicate of [Stacks, Tag 01W8]:
a closed immersion into `ℙⁿ` over the base for some `n`. H-quasi-projectivity is
`AlgebraicGeometry.IsHQuasiProjective`, the predicate of [Stacks, Tag 01VW].

Dimension is the Krull dimension `topologicalKrullDim` of the underlying topological space,
valued in `WithBot ℕ∞`.

The proof is the unconditional Tag 0A26,
`Stacks.HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one`
itself.

## References

* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 0BXV](https://stacks.math.columbia.edu/tag/0BXV)
* [Stacks Project, Tag 0A25](https://stacks.math.columbia.edu/tag/0A25)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 01R7](https://stacks.math.columbia.edu/tag/01R7)
* [Stacks Project, Tag 01RB](https://stacks.math.columbia.edu/tag/01RB)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01T1](https://stacks.math.columbia.edu/tag/01T1)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Proper schemes of dimension at most one -/

/-- A proper scheme over a field `k` whose topological Krull dimension is at most one is
H-projective over `k`.

This is [Stacks, Tag 0A26],
`Stacks.HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one`
itself. -/
public theorem isProjectiveMorphism_of_topologicalKrullDim_le_one
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    IsProjectiveMorphism f :=
  Stacks.HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one
    f hdim

end AlgebraicGeometry


end
