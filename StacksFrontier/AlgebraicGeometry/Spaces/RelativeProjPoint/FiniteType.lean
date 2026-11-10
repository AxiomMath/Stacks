module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtaleChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Space

/-!
# The relative Proj of an algebraic space is of finite type

In Situation 0849 let `π : Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of Stacks 084C,
`AlgebraicGeometry.Space.RelativeProjSituation.π`. This file proves Stacks 084G: if `𝒜` is of
finite type as a sheaf of `𝒪_X`-algebras, then `π` is of finite type.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.isFiniteType_π`: **Stacks 084G.**

## Implementation notes

**The hypothesis.** Finite type of a quasi-coherent `𝒪_X`-algebra on an algebraic space is read
étale locally: on the restriction `g^*𝒜` to every étale scheme point `g : U ⟶ X`, which is the
restriction of Stacks 084B (`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints`).
On it the condition is the affine-local finite type condition of the case of schemes,
`Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType`: every point of `U` has an affine
neighbourhood over which the graded ring of sections of `g^*𝒜` is a finite type algebra over the
functions. The reading at every étale point is
`AlgebraicGeometry.Space.RelativeProjSituation.HoldsAtEtalePoints`, the reading Stacks 084F and
084H use for their conditions. The restriction `g^*𝒜` is that of the re-presentation of `𝒜` with
sections in the universe `u`, identified with `𝒜` sectionwise by
`AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebraEquiv`.

**The proof** is the source's. Being of finite type is being locally of finite type and
quasi-compact. Choose a surjective étale scheme point `g : U ⟶ X`. By Stacks 084B the base change
of `π` along `g` is the structure morphism of `Proj_U(g^*𝒜)`, which is locally of finite type and
quasi-compact by the case of schemes, Stacks 07ZY
(`Stacks.AlgebraicGeometry.RelativeProjFiniteType.locallyOfFiniteType_toBase` and
`…quasiCompact_toBase`); both properties descend along `g`, by Stacks 040Y and 03KG
(`AlgebraicGeometry.Space.RelativeProjPoints.isLocallyOfFiniteType_of_etalePoint` and
`…isQuasiCompact_of_etalePoint`).

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 084G](https://stacks.math.columbia.edu/tag/084G)
* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
-/

@[expose] public section

universe u m

namespace AlgebraicGeometry.Space

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- **Stacks 084G.** In Situation 0849, if `𝒜` is of finite type as a sheaf of `𝒪_X`-algebras,
the structure morphism `π : Proj_X(𝒜) ⟶ X` of the relative homogeneous spectrum is of finite
type.

The hypothesis is read étale locally, on the restriction `g^*𝒜` of Stacks 084B to every étale
scheme point `g` of `X` (taken through the `u`-small re-presentation of `𝒜`, identified with `𝒜`
by `smallAlgebraEquiv`); by `holdsAtEtalePoints_isFiniteType_iff` it suffices at one surjective
étale scheme point. -/
@[stacks 084G]
theorem isFiniteType_π
    (hft : s.HoldsAtEtalePoints Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType) :
    IsFiniteType s.site s.base s.containsBase s.π.hom := by
  rw [s.π_hom]
  obtain ⟨T, g, hgEt, hgSurj⟩ := RelativeProjPoints.exists_etalePoint s.space.property
  exact ⟨s.relativeProjPoints.isLocallyOfFiniteType_of_etalePoint T g hgEt hgSurj
      (Stacks.AlgebraicGeometry.RelativeProjFiniteType.locallyOfFiniteType_toBase _
        (hft T g hgEt)),
    s.relativeProjPoints.isQuasiCompact_of_etalePoint s.isAlgebraicSpace_relativeProjFunctor
      s.space.property T g hgEt hgSurj
      (Stacks.AlgebraicGeometry.RelativeProjFiniteType.quasiCompact_toBase _ (hft T g hgEt))⟩

end RelativeProjSituation

end AlgebraicGeometry.Space

end
