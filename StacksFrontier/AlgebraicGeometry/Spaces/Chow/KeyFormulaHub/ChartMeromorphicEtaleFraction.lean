module

public import StacksFrontier.AlgebraicGeometry.SpecTotalFractionRing
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicChartFunctionField
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal

/-!
# Meromorphic functions on an affine chart, read in the étale local ring

Let `X` be an algebraic space satisfying the two hypotheses of Stacks 0EN6, part (2), let `x̄` be
a geometric point of `X` and let `(V, v)` be a small étale neighbourhood of `x̄` with affine
scheme. The meromorphic functions `𝒦_X(V)` are the total ring of fractions of `𝒪_X(V)`, and the
germ map `𝒪_X(V) → 𝒪_{X, x̄}` carries nonzerodivisors to nonzerodivisors, so it extends to a map
`𝒦_X(V) → Q(𝒪_{X, x̄})`. This file defines it and records its naturality in the
neighbourhood.

No integrality of the chart is assumed: a chart of an integral algebraic space need not be
integral, so the function-field reading
`AlgebraicGeometry.Space.chartMeromorphicToEtaleFractionRing` of
`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicChartEtaleFractionRing.lean`, which asks for an
integral chart, does not apply; on an integral affine chart the two readings agree, both being the
localization of the germ map.

## Main definitions

* `AlgebraicGeometry.Space.affineChartMeromorphicToEtaleFractionRing`: the map
  `𝒦_X(V) → Q(𝒪_{X, x̄})`.

## Main results

* `AlgebraicGeometry.Space.affineChartMeromorphicToEtaleFractionRing_algebraMap`: on a regular
  function it is the germ.
* `AlgebraicGeometry.Space.affineChartMeromorphicToEtaleFractionRing_map`: it is compatible with a
  morphism of small étale neighbourhoods.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicFunctionAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (F : AlgebraicSpaces B S hS)

/-- On an affine chart the germ at a geometric point carries nonzerodivisors of the regular
functions to nonzerodivisors of the étale local ring: the germ in the ordinary local ring is a
localization map, and the canonical map of Stacks 05VP is flat. -/
theorem etaleLocalRingGerm_mem_nonZeroDivisors {x : GeometricPoint B S hS F.1}
    (N : SmallEtaleNeighborhood x) (hN : IsAffine (chartScheme N.chart))
    {a : (structurePresheaf B S hS F.1).obj (op N.chart)}
    (ha : a ∈ ((structurePresheaf B S hS F.1).obj (op N.chart))⁰) :
    etaleLocalRingGerm B S hS F.1 x (op N) a ∈ ((etaleLocalRing B S hS F.1 x : Type (u + 1)))⁰ := by
  rw [← chartLocalRingToEtaleLocalRing_germ B S hS F.1 F.2 N a]
  exact chartLocalRingToEtaleLocalRing_mem_nonZeroDivisors B S hS F.1 F.2 N
    (Scheme.nonZeroDivisors_le_comap_germ_top (chartScheme N.chart) _ ha)

variable (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS F, localRingDimension B S hS z = 0)
  (hfin : HasLocallyFiniteIrreducibleComponents B S hS F.1)

/-- **A meromorphic function on an affine chart, read in the étale local ring.** For a small
étale neighbourhood `(V, v)` of a geometric point `x̄` with affine scheme, the map
`𝒦_X(V) → Q(𝒪_{X, x̄})` extending the germ map `𝒪_X(V) → 𝒪_{X, x̄}`: `𝒦_X(V)` is the total
ring of fractions of `𝒪_X(V)` by Stacks 0EN6, part (2). -/
def affineChartMeromorphicToEtaleFractionRing {x : GeometricPoint B S hS F.1}
    (N : SmallEtaleNeighborhood x) (hN : IsAffine (chartScheme N.chart)) :
    (meromorphicFunctionSheaf B S hS F.1 F.2).obj.obj (op N.chart) →+*
      FractionRing (etaleLocalRing B S hS F.1 x : Type (u + 1)) :=
  haveI := isFractionRing_meromorphicFunctionSheaf_obj B S hS F hwa hfin N.chart hN
  IsLocalization.lift (M := ((structurePresheaf B S hS F.1).obj (op N.chart))⁰)
    (g := (algebraMap (etaleLocalRing B S hS F.1 x : Type (u + 1))
      (FractionRing (etaleLocalRing B S hS F.1 x : Type (u + 1)))).comp
        (etaleLocalRingGerm B S hS F.1 x (op N)))
    fun y ↦ IsLocalization.map_units _
      ⟨_, etaleLocalRingGerm_mem_nonZeroDivisors B S hS F N hN y.2⟩

/-- On a regular function the map `𝒦_X(V) → Q(𝒪_{X, x̄})` is the germ. -/
theorem affineChartMeromorphicToEtaleFractionRing_algebraMap {x : GeometricPoint B S hS F.1}
    (N : SmallEtaleNeighborhood x) (hN : IsAffine (chartScheme N.chart))
    (a : (structurePresheaf B S hS F.1).obj (op N.chart)) :
    affineChartMeromorphicToEtaleFractionRing B S hS F hwa hfin N hN
        (algebraMap _ ((meromorphicFunctionSheaf B S hS F.1 F.2).obj.obj (op N.chart)) a) =
      algebraMap (etaleLocalRing B S hS F.1 x : Type (u + 1))
        (FractionRing (etaleLocalRing B S hS F.1 x : Type (u + 1)))
        (etaleLocalRingGerm B S hS F.1 x (op N) a) :=
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS F hwa hfin N.chart hN
  IsLocalization.lift_eq _ _

/-- **Naturality in the neighbourhood.** Restricting a meromorphic function along a morphism of
small étale neighbourhoods with affine schemes does not change its reading in `Q(𝒪_{X, x̄})`. -/
theorem affineChartMeromorphicToEtaleFractionRing_map {x : GeometricPoint B S hS F.1}
    {N N' : SmallEtaleNeighborhood x} (m : N' ⟶ N) (hN : IsAffine (chartScheme N.chart))
    (hN' : IsAffine (chartScheme N'.chart))
    (φ : (meromorphicFunctionSheaf B S hS F.1 F.2).obj.obj (op N.chart)) :
    affineChartMeromorphicToEtaleFractionRing B S hS F hwa hfin N' hN'
        (((meromorphicFunctionSheaf B S hS F.1 F.2).obj.map m.hom.op).hom φ) =
      affineChartMeromorphicToEtaleFractionRing B S hS F hwa hfin N hN φ := by
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS F hwa hfin N.chart hN
  refine RingHom.congr_fun (IsLocalization.ringHom_ext
    ((structurePresheaf B S hS F.1).obj (op N.chart))⁰
    (j := (affineChartMeromorphicToEtaleFractionRing B S hS F hwa hfin N' hN').comp
      ((meromorphicFunctionSheaf B S hS F.1 F.2).obj.map m.hom.op).hom)
    (k := affineChartMeromorphicToEtaleFractionRing B S hS F hwa hfin N hN)
    (RingHom.ext fun a ↦ ?_)) φ
  have hnat := ConcreteCategory.congr_hom
    ((toMeromorphicFunctionSheaf B S hS F.1 F.2).hom.naturality m.hom.op) a
  show affineChartMeromorphicToEtaleFractionRing B S hS F hwa hfin N' hN'
      (((meromorphicFunctionSheaf B S hS F.1 F.2).obj.map m.hom.op).hom
        (((toMeromorphicFunctionSheaf B S hS F.1 F.2).hom.app (op N.chart)).hom a)) =
    affineChartMeromorphicToEtaleFractionRing B S hS F hwa hfin N hN
      (algebraMap _ ((meromorphicFunctionSheaf B S hS F.1 F.2).obj.obj (op N.chart)) a)
  refine (congrArg (affineChartMeromorphicToEtaleFractionRing B S hS F hwa hfin N' hN')
      hnat.symm).trans
      ?_
  refine (affineChartMeromorphicToEtaleFractionRing_algebraMap B S hS F hwa hfin N' hN' _).trans ?_
  refine Eq.trans ?_ (affineChartMeromorphicToEtaleFractionRing_algebraMap B S hS F hwa hfin N hN
      a).symm
  exact congrArg (algebraMap _ _) (RingHom.congr_fun (etaleLocalRingGerm_comp_map B S hS m) a)

end AlgebraicGeometry.Space

end
