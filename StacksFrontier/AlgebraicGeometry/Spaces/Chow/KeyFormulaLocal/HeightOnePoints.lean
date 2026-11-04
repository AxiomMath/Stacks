module

public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorChartPointNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPushforwardFibreLength
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction

/-!
# Height-one primes of a chart local ring and the prime divisors through a point

Let `X` be a decent algebraic space, `W` an étale scheme chart of `X` and `u` a point of the
scheme of `W` over a point `ζ ∈ |X|`. The third step of the proof of Stacks 0EQV sums over the
height-one primes `𝔮` of `A = 𝒪_{W, u}` and needs to know what they are on `X`: each lies over
the generic point of a prime divisor `Z` of `X` through `ζ`, and every prime divisor through `ζ`
is reached by at least one of them. This file proves both, at the level of points of the chart
scheme and at the level of the primes of `A`.

The primes of `A` are the points of `W` specializing to `u`
(`AlgebraicGeometry.Scheme.range_fromSpecStalk`), the height of a prime is the coheight of the
point (`Stacks.Chow.coheight_fromSpecStalk_eq_height`), and the coheight of a point of the chart
is the codimension of the closure of its image in `|X|` (Stacks 04NA and 0ED1). The map from the
chart to `|X|` is continuous and generalizing (Stacks 03K2), which carries specializations in
both directions.

## Main results

* `AlgebraicGeometry.Space.generalizingMap_chartSchemeToPoints`: generizations lift along a
  chart.
* `AlgebraicGeometry.Space.coheight_eq_codimension_chartSchemeToPoints`: the coheight of a point
  of a chart is the codimension of the closure of its image.
* `AlgebraicGeometry.Space.exists_primeDivisor_of_coheight_eq_one_of_specializes` and
  `AlgebraicGeometry.Space.exists_specializes_coheight_eq_one_of_mem_support`: the coheight-one
  generizations of `u` lie over the generic points of the prime divisors through `ζ`, and each of
  those is reached.
* `AlgebraicGeometry.Space.exists_primeDivisor_of_heightOnePrime` and
  `AlgebraicGeometry.Space.exists_heightOnePrime_of_mem_support`: the same for the height-one
  primes of `𝒪_{W, u}`, in the indexing `{𝔮 : Ideal A // 𝔮.IsPrime ∧ 𝔮.height = 1}` of the
  reciprocity law `AlgebraicGeometry.sum_ord_heightOneSymbol_eq_zero` (Stacks 0EAW).

In a locally finite family of subsets of `|X|` only finitely many members contain `ζ`; that is
Mathlib's `LocallyFinite.point_finite` and needs no restatement.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0ED1](https://stacks.math.columbia.edu/tag/0ED1)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)

include hX hdec in
/-- **Generizations lift along an étale chart of a decent space** (Stacks 03K2): the map from
the scheme of an étale chart to `|X|` is generalizing. -/
theorem generalizingMap_chartSchemeToPoints (W : SmallEtale B S hS X) :
    GeneralizingMap (chartSchemeToPoints B S hS X W) := by
  have h : chartSchemeToPoints B S hS X W = pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X).obj W)) W.obj.hom ∘
        (schemePointsHomeomorph B S hS ((SmallEtale.toOver B S hS X).obj W)).symm := by
    funext x
    exact chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X W x
  rw [h]
  exact ((schemePointsHomeomorph B S hS _).symm.isOpenEmbedding.generalizingMap).comp
    (generalizingMap_pointsMap_of_isDecentSpace B S hS X hX hdec _ W.obj.hom W.property)

include hX hdec in
/-- **The coheight of a point of a chart is the codimension of the closure of its image.** For
an étale chart `W` of a decent algebraic space and a point `q` of its scheme, the coheight of `q`
in the specialization order is the codimension (Stacks 02I3) of the closure of its image in
`|X|`: both are the dimension of the local ring of `X` at the image (Stacks 02IZ, 04NA, 0ED1). -/
theorem coheight_eq_codimension_chartSchemeToPoints (W : SmallEtale B S hS X)
    (q : chartScheme W) :
    Order.coheight q = codimension (closureSingleton (chartSchemeToPoints B S hS X W q)) := by
  have h1 := ringKrullDim_stalk_eq_coheight q
  have h2 := localRingDimension_eq_of_chartPoint B S hS hX
    ((SmallEtale.toOver B S hS X).obj W) W.obj.hom W.property q _
    (chartPoint_chartSchemeToPoints B S hS ⟨X, hX⟩ W q)
  have h3 := codimension_eq_localRingDimension B S hS hX hdec
    (closureSingleton (chartSchemeToPoints B S hS X W q)) (chartSchemeToPoints B S hS X W q)
    (by rw [coe_closureSingleton]; exact isGenericPoint_closure)
  rw [h3]
  exact WithBot.coe_injective (h1.symm.trans h2.symm)

include hX hdec in
/-- **A coheight-one generization of a chart point lies over the generic point of a prime
divisor through the image of that point.** -/
theorem exists_primeDivisor_of_coheight_eq_one_of_specializes (W : SmallEtale B S hS X)
    {q u : chartScheme W} (hqu : q ⤳ u) (hq : Order.coheight q = 1) :
    ∃ Z : PrimeDivisor B S hS X,
      Z.genericPoint B S hS X = chartSchemeToPoints B S hS X W q ∧
        chartSchemeToPoints B S hS X W u ∈ Z.support B S hS X := by
  obtain ⟨Z, hZ⟩ := exists_primeDivisor_genericPoint_eq_chartSchemeToPoints B S hS hX hdec W q hq
  refine ⟨Z, hZ, (Z.isGenericPoint_genericPoint B S hS X).specializes_iff_mem.mp ?_⟩
  rw [hZ]
  exact hqu.map (continuous_chartSchemeToPoints B S hS W)

include hX hdec in
/-- **Every prime divisor through the image of a chart point is reached by a coheight-one
generization of it.** If the image of `u` in `|X|` lies on the prime divisor `Z`, some point
`q ⤳ u` of the chart of coheight one maps to the generic point of `Z`. -/
theorem exists_specializes_coheight_eq_one_of_mem_support (W : SmallEtale B S hS X)
    (u : chartScheme W) (Z : PrimeDivisor B S hS X)
    (hZ : chartSchemeToPoints B S hS X W u ∈ Z.support B S hS X) :
    ∃ q : chartScheme W, q ⤳ u ∧ Order.coheight q = 1 ∧
      chartSchemeToPoints B S hS X W q = Z.genericPoint B S hS X := by
  obtain ⟨q, hqu, hq⟩ := generalizingMap_chartSchemeToPoints B S hS hX hdec W
    ((Z.isGenericPoint_genericPoint B S hS X).specializes hZ)
  refine ⟨q, hqu, ?_, hq⟩
  rw [coheight_eq_codimension_chartSchemeToPoints B S hS hX hdec W q, hq]
  exact Z.codimension_genericPoint B S hS X

include hX hdec in
/-- **A height-one prime of a chart local ring lies over the generic point of a prime divisor
through the image of the point.** For a height-one prime `𝔮` of `𝒪_{W, u}`, the point of `W` it
cuts out maps to the generic point of a prime divisor `Z` of `X` whose points contain the image
of `u`. -/
theorem exists_primeDivisor_of_heightOnePrime (W : SmallEtale B S hS X) (u : chartScheme W)
    (𝔮 : {𝔮 : Ideal ((chartScheme W).presheaf.stalk u) // 𝔮.IsPrime ∧ 𝔮.height = 1}) :
    ∃ Z : PrimeDivisor B S hS X,
      Z.genericPoint B S hS X =
          chartSchemeToPoints B S hS X W (Stacks.Chow.intermediatePointOfHeightOnePrime u 𝔮) ∧
        chartSchemeToPoints B S hS X W u ∈ Z.support B S hS X := by
  refine exists_primeDivisor_of_coheight_eq_one_of_specializes B S hS hX hdec W
    (Stacks.Chow.specializes_intermediatePointOfHeightOnePrime u 𝔮) ?_
  exact (Stacks.Chow.coheight_fromSpecStalk_eq_height u ⟨𝔮.1, 𝔮.2.1⟩).trans 𝔮.2.2

include hX hdec in
/-- **Every prime divisor through the image of a chart point is reached by a height-one prime of
the local ring.** If the image of `u` in `|X|` lies on the prime divisor `Z`, some height-one
prime `𝔮` of `𝒪_{W, u}` cuts out a point of `W` mapping to the generic point of `Z`. -/
theorem exists_heightOnePrime_of_mem_support (W : SmallEtale B S hS X) (u : chartScheme W)
    (Z : PrimeDivisor B S hS X)
    (hZ : chartSchemeToPoints B S hS X W u ∈ Z.support B S hS X) :
    ∃ 𝔮 : {𝔮 : Ideal ((chartScheme W).presheaf.stalk u) // 𝔮.IsPrime ∧ 𝔮.height = 1},
      chartSchemeToPoints B S hS X W (Stacks.Chow.intermediatePointOfHeightOnePrime u 𝔮) =
        Z.genericPoint B S hS X := by
  obtain ⟨q, hqu, hq, hqZ⟩ :=
    exists_specializes_coheight_eq_one_of_mem_support B S hS hX hdec W u Z hZ
  obtain ⟨p, rfl⟩ := Stacks.Chow.exists_fromSpecStalk_eq hqu
  have hp : p.asIdeal.height = 1 :=
    (Stacks.Chow.coheight_fromSpecStalk_eq_height u p).symm.trans hq
  exact ⟨⟨p.asIdeal, p.isPrime, hp⟩, hqZ⟩

end AlgebraicGeometry.Space

end
