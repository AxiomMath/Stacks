module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartComparisonMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMap
public import StacksCore.Tactic.StacksAttribute

/-!
# The three equivalent conditions of Stacks 0DJ8

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian diagram of schemes, let `K` be an object of `D(𝒪_X)`, let `K'` be an object of
`D(𝒪_{X'})` and let `φ : L(g')^*K ⟶ K'`. Stacks 0DJ8 asserts the equivalence of

1. the pointwise maps of Stacks 0DJ7 are isomorphisms at every point of `X'` and in every degree;
2. the comparison map of every Cartesian affine-open chart is an isomorphism;
3. the comparison map is an isomorphism for a family of Cartesian affine-open charts whose opens
   `U'` cover `X'`.

This module carries the part of that equivalence which uses nothing about the comparison map
beyond its chart-locality: granted the per-chart criterion that condition (2) at one chart is
exactly condition (1) at the points of that chart's open `U'`, the three conditions are
equivalent. The implication (2) ⟹ (3) needs no criterion at all and is
`AlgebraicGeometry.exists_coveringFamily_isIso_comparison`; the other two implications are read
off the criterion at a chart containing the given point.

## Main results

* `AlgebraicGeometry.baseChange_tfae_of_chartCriterion`: the three-way equivalence, granted the
  per-chart criterion.

## Implementation notes

The criterion is a hypothesis: the result below is Stacks 0DJ8 conditional on it.

The criterion is stated for every chart at once rather than chart by chart because the
implication (1) ⟹ (2) quantifies over charts while (3) ⟹ (1) quantifies over points, and a
single hypothesis serves both.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 0DJ8, granted the per-chart criterion.** If, on every Cartesian affine-open chart,
invertibility of the chart comparison map is equivalent to invertibility of the pointwise maps of
Stacks 0DJ7 at the points of that chart's open `U'`, then the three conditions of Stacks 0DJ8 are
equivalent.

The step (2) ⟹ (3) is `AlgebraicGeometry.exists_coveringFamily_isIso_comparison` and uses no
criterion; (1) ⟹ (2) applies the criterion at an arbitrary chart, and (3) ⟹ (1) applies it at a
chart of the covering family containing the given point. -/
public theorem baseChange_tfae_of_chartCriterion {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K')
    (hchart : ∀ ch : BaseChangeChart f g f' g',
      IsIso (ch.comparison K K' φ) ↔
        ∀ (y : Spec ch.A') (n : ℤ),
          IsIso (baseChangeCohomologyMap f g f' g' sq.w K K' φ (ch.incU' y) n)) :
    List.TFAE
      [∀ (x' : X') (i : ℤ), IsIso (baseChangeCohomologyMap f g f' g' sq.w K K' φ x' i),
       ∀ ch : BaseChangeChart f g f' g', IsIso (ch.comparison K K' φ),
       ∃ 𝒞 : Set (BaseChangeChart f g f' g'),
         (∀ ch ∈ 𝒞, IsIso (ch.comparison K K' φ)) ∧
           ∀ x' : X', ∃ ch ∈ 𝒞, ∃ y : Spec ch.A', ch.incU' y = x'] := by
  tfae_have 1 → 2 := fun h ch => (hchart ch).mpr fun y n => h (ch.incU' y) n
  tfae_have 2 → 3 := fun h => exists_coveringFamily_isIso_comparison sq K K' φ h
  tfae_have 3 → 1 := by
    rintro ⟨𝒞, h𝒞, hcover⟩ x' n
    obtain ⟨ch, hch, y, hy⟩ := hcover x'
    exact hy ▸ (hchart ch).mp (h𝒞 ch hch) y n
  tfae_finish

end AlgebraicGeometry

end
