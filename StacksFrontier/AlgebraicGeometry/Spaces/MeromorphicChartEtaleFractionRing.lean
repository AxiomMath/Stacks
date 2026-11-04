module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicChartFunctionField
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingEtaleChart

/-!
# Reading a meromorphic function of a chart in `Q(𝒪_{X, x̄})`, naturally in the chart

Let `X` be an algebraic space over a scheme `S` satisfying the two standing hypotheses of
Stacks 0EN6, let `x̄` be a geometric point of `X` and let `(V, v)` be a small étale neighbourhood
of `x̄` whose scheme is integral and affine. Composing the identification of `𝒦_X(V)` with the
function field of the chart scheme with the canonical map of Stacks 05VP gives a ring homomorphism

`𝒦_X(V) ⟶ Q(𝒪_{X, x̄})`

which is **unchanged by refining the chart**.

## Main definitions

* `AlgebraicGeometry.Space.chartMeromorphicToEtaleFractionRing`: the reading
  `𝒦_X(V) ⟶ Q(𝒪_{X, x̄})`, the composite of the identification of `𝒦_X(V)` with the function
  field of the chart scheme (`AlgebraicGeometry.Space.chartMeromorphicFunctionFieldEquiv`) with
  the canonical map of Stacks 05VP read on fractions
  (`AlgebraicGeometry.Space.functionFieldToEtaleFractionRing`).

## Main results

* `AlgebraicGeometry.Space.chartMeromorphicToEtaleFractionRing_algebraMap`: on a regular
  function the reading is the germ at `v`, pushed into `𝒪_{X, x̄}` by the canonical map of
  Stacks 05VP.
* `AlgebraicGeometry.Space.chartMeromorphicToEtaleFractionRing_restrict`: **the reading is
  natural in the chart.** Restricting a meromorphic function of a coarse chart `W` to a small
  étale neighbourhood `(V, v)` of `x̄` lying over `W` and reading it there gives the same element
  of `Q(𝒪_{X, x̄})` as reading it at `W` with the lift of `x̄` that the morphism induces.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] nonempty_top_chartScheme
attribute [local instance] chartMeromorphicFunctionAlgebra chartFunctionFieldAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- Restriction along a morphism of charts commutes with the canonical map `𝒪_X ⟶ 𝒦_X`. -/
theorem meromorphicFunctionSheaf_map_algebraMap {U U' : SmallEtale B S hS X.1} (k : U' ⟶ U)
    (a : (structurePresheaf B S hS X.1).obj (op U)) :
    ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map k.op).hom
        (algebraMap ((structurePresheaf B S hS X.1).obj (op U))
          ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) a) =
      algebraMap ((structurePresheaf B S hS X.1).obj (op U'))
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U'))
        ((structurePresheaf B S hS X.1).map k.op a) :=
  (ConcreteCategory.congr_hom
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.naturality k.op) a).symm

variable (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)

/-- The reading `𝒦_X(V) ⟶ Q(𝒪_{X, x̄})` of a meromorphic function of an integral affine étale
chart `V` of `X`: the identification of `𝒦_X(V)` with the function field of the chart scheme
(`AlgebraicGeometry.Space.chartMeromorphicFunctionFieldEquiv`) followed by the canonical map of
Stacks 05VP (`AlgebraicGeometry.Space.functionFieldToEtaleFractionRing`). -/
def chartMeromorphicToEtaleFractionRing {x : GeometricPoint B S hS X.1}
    (V : SmallEtaleNeighborhood x)
    [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    (hV : IsAffine (chartScheme V.chart)) :
    (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V.chart) →+*
      FractionRing (etaleLocalRing B S hS X.1 x : Type (u + 1)) :=
  (functionFieldToEtaleFractionRing B S hS X.1 X.2 V).comp
    (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V.chart hV).toAlgHom.toRingHom

/-- The reading of a regular function is its germ at the chart point, pushed into `𝒪_{X, x̄}` by
the canonical map of Stacks 05VP and then into its fractions. -/
theorem chartMeromorphicToEtaleFractionRing_algebraMap {x : GeometricPoint B S hS X.1}
    (V : SmallEtaleNeighborhood x)
    [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    (hV : IsAffine (chartScheme V.chart))
    (a : (structurePresheaf B S hS X.1).obj (op V.chart)) :
    chartMeromorphicToEtaleFractionRing B S hS X hwa hfin V hV
        (algebraMap ((structurePresheaf B S hS X.1).obj (op V.chart))
          ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V.chart)) a) =
      algebraMap (etaleLocalRing B S hS X.1 x : Type (u + 1))
          (FractionRing (etaleLocalRing B S hS X.1 x : Type (u + 1)))
        (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 V
          ((chartScheme V.chart).presheaf.germ ⊤ (chartPoint B S hS X.1 V) trivial a)) := by
  show functionFieldToEtaleFractionRing B S hS X.1 X.2 V
      (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V.chart hV
        (algebraMap ((structurePresheaf B S hS X.1).obj (op V.chart))
          ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V.chart)) a)) = _
  rw [chartMeromorphicFunctionFieldEquiv_algebraMap, ←
    AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField
      (X := chartScheme V.chart) (U := ⊤) (x := chartPoint B S hS X.1 V) trivial a,
    functionFieldToEtaleFractionRing_algebraMap]

/-- The reading of a meromorphic function of a chart in `Q(𝒪_{X, x̄})` is unchanged by refining
the chart: a meromorphic function of an étale chart `W` of `X` restricted to a small étale
neighbourhood `(V, v)` of `x̄` lying over `W` and read there gives the same element of
`Q(𝒪_{X, x̄})` as reading it at `W` with the lift of `x̄` that the morphism induces. -/
theorem chartMeromorphicToEtaleFractionRing_restrict {x : GeometricPoint B S hS X.1}
    (V : SmallEtaleNeighborhood x) (W : SmallEtale B S hS X.1) (k : V.chart ⟶ W)
    (hcomm : V.chart.obj.hom ≫ 𝟙 X.1 =
      yoneda.map ((SmallEtale.toOver B S hS X.1).map k) ≫ W.obj.hom)
    [AlgebraicGeometry.IsIntegral (chartScheme V.chart)]
    [AlgebraicGeometry.IsIntegral (chartScheme
      (targetNeighborhood B S hS V W ((SmallEtale.toOver B S hS X.1).map k) hcomm).chart)]
    (hV : IsAffine (chartScheme V.chart))
    (hW : IsAffine (chartScheme
      (targetNeighborhood B S hS V W ((SmallEtale.toOver B S hS X.1).map k) hcomm).chart))
    (m : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op W)) :
    chartMeromorphicToEtaleFractionRing B S hS X hwa hfin V hV
        (((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map k.op).hom m) =
      chartMeromorphicToEtaleFractionRing B S hS X hwa hfin
        (targetNeighborhood B S hS V W ((SmallEtale.toOver B S hS X.1).map k) hcomm) hW m := by
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin W hW
  have key : (chartMeromorphicToEtaleFractionRing B S hS X hwa hfin V hV).comp
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map k.op).hom =
      chartMeromorphicToEtaleFractionRing B S hS X hwa hfin
        (targetNeighborhood B S hS V W ((SmallEtale.toOver B S hS X.1).map k) hcomm) hW := by
    refine IsLocalization.ringHom_ext ((structurePresheaf B S hS X.1).obj (op W))⁰
      (RingHom.ext fun a => ?_)
    refine Eq.trans ?_ (chartMeromorphicToEtaleFractionRing_algebraMap B S hS X hwa hfin
      (targetNeighborhood B S hS V W ((SmallEtale.toOver B S hS X.1).map k) hcomm) hW a).symm
    simp only [RingHom.comp_apply, meromorphicFunctionSheaf_map_algebraMap,
      chartMeromorphicToEtaleFractionRing_algebraMap]
    congr 1
    refine Eq.trans ?_ (RingHom.congr_fun
      (chartLocalRingToEtaleLocalRing_comp_stalkMap B S hS X.1 X.2 V W
        ((SmallEtale.toOver B S hS X.1).map k) hcomm) _)
    exact congrArg (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 V)
      (Scheme.Hom.germ_stalkMap_apply _ ⊤ (chartPoint B S hS X.1 V) trivial a).symm
  exact RingHom.congr_fun key m

end AlgebraicGeometry.Space

end
