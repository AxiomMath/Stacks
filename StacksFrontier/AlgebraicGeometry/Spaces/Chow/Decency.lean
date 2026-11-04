module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Setup
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableImpliesFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointSpaceSober

/-!
# A good algebraic space is decent, and its point space is sober

The base algebraic space of Situation 0EDT is quasi-separated, and a good algebraic space over
it has a quasi-separated structure morphism; so a good algebraic space is itself
quasi-separated, and therefore decent. Consequently its point space is sober, which is what
licenses the choice of a generic point of an irreducible closed subset of `|X|` throughout the
theory of cycles.

## Main results

* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.isAbsolutelyQuasiSeparated_of_isGood`: a
  good algebraic space is quasi-separated.
* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.isDecentSpace_of_isGood`: a good
  algebraic space is decent.
* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.stacksSober_points_of_isGood`:
  **Stacks 0EDU**, the point space of a good algebraic space is sober.

## Implementation notes

Decency is reached along the chain of conditions of Stacks 03JX. Quasi-separatedness of the
space itself is Stacks 04ZH part (2) applied to the quasi-separated structure morphism and the
quasi-separated base, which is why the situation carries the membership of the terminal scheme
in the site: the absolute separation conditions of Stacks 03BS are formed after relocalizing
over it. From there the implications are `(η) ⇒ (ζ) ⇒ (ε) ⇒ (δ) ⇒ (γ)`, each of them already
in the library, and `(γ)` is decency by
`AlgebraicGeometry.Space.isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint`.

Soberness in the sense of the Stacks Project — every irreducible closed subset has a *unique*
generic point — is `TopologicalSpace.StacksSober`, which splits as `T0Space` together with
`QuasiSober` by `TopologicalSpace.stacksSober_iff_t0_and_quasiSober`. Both factors are
available for a decent algebraic space, the first by Stacks 03K3 and the second by Stacks 03K6.

## References

* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03K3](https://stacks.math.columbia.edu/tag/03K3)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDU](https://stacks.math.columbia.edu/tag/0EDU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A good algebraic space over the base of Situation 0EDT is quasi-separated: its structure
morphism is quasi-separated and the base is quasi-separated, so Stacks 04ZH part (2)
applies. -/
theorem BaseSpaceDimensionSituation.isAbsolutelyQuasiSeparated_of_isGood (f : X ⟶ D.space)
    (hgood : D.IsGood f) :
    IsAbsolutelyQuasiSeparated D.site D.base D.base_mem D.terminal_mem X :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated (B := D.site) (S := D.base)
    (hS := D.base_mem) (hZ := D.terminal_mem) (hF := hgood.1) (hG := D.quasiSeparated)
    (hf := hgood.2.1)

/-- A good algebraic space over the base of Situation 0EDT is decent.

It is quasi-separated, hence Zariski locally quasi-separated, hence very reasonable, hence
reasonable, hence satisfies condition `(γ)` of Stacks 03JX, which is decency. -/
theorem BaseSpaceDimensionSituation.isDecentSpace_of_isGood (f : X ⟶ D.space)
    (hgood : D.IsGood f) :
    IsDecentSpace D.site D.base D.base_mem X :=
  (isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint D.site D.base D.base_mem X
      hgood.1).mpr
    (hasFiniteChartAndRelationFibersAtEveryPoint_of_isReasonableSpace D.site D.base D.base_mem
      X hgood.1
      (isReasonableSpace_of_isVeryReasonableSpace D.site D.base D.base_mem X hgood.1
        (isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated D.site D.base
          D.base_mem D.terminal_mem X hgood.1
          (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated
            (B := D.site) (S := D.base) (hS := D.base_mem) (hZ := D.terminal_mem) (X := X)
            (hX := hgood.1) (h := D.isAbsolutelyQuasiSeparated_of_isGood f hgood)))))

/-- **Stacks 0EDU.** The point space of a good algebraic space over the base of Situation 0EDT
is sober: every irreducible closed subset of it has a unique generic point.

A good algebraic space is decent, and the point space of a decent algebraic space is
Kolmogorov by Stacks 03K3 and quasi-sober by Stacks 03K6. -/
@[stacks 0EDU]
theorem BaseSpaceDimensionSituation.stacksSober_points_of_isGood (f : X ⟶ D.space)
    (hgood : D.IsGood f) :
    StacksSober (points D.site D.base D.base_mem X) :=
  stacksSober_iff_t0_and_quasiSober.mpr
    ⟨t0Space_points_of_isDecentSpace D.site D.base D.base_mem hgood.1
        (D.isDecentSpace_of_isGood f hgood),
      quasiSober_points_of_isDecentSpace D.site D.base D.base_mem hgood.1
        (D.isDecentSpace_of_isGood f hgood)⟩

end AlgebraicGeometry.Space

end
