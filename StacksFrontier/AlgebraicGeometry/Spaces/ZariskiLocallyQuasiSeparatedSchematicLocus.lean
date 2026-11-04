module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableImpliesFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae

/-!
# The schematic locus and the point space of a Zariski locally quasi-separated algebraic space

A Zariski locally quasi-separated algebraic space over a scheme `S` is decent, and therefore
its schematic locus is a dense open subspace which is a scheme and its space of points is
sober. For a quasi-separated algebraic space the points of codimension `0` are exactly the
generic points of the irreducible components of its point space. Throughout, the terminal
scheme is assumed to be an object of the site (`hZ`).

## Main results

* `AlgebraicGeometry.Space.isDecentSpace_of_isZariskiLocallyQuasiSeparatedOver`: a Zariski
  locally quasi-separated algebraic space is decent.
* `AlgebraicGeometry.Space.denseRange_schematicLocus_of_isZariskiLocallyQuasiSeparatedOver`:
  the schematic locus of such a space is dense in its space of points.
* `AlgebraicGeometry.Space.stacksSober_points_of_isZariskiLocallyQuasiSeparatedOver`: the point
  space of such a space is sober, with
  `AlgebraicGeometry.Space.t0Space_points_of_isZariskiLocallyQuasiSeparatedOver` and
  `AlgebraicGeometry.Space.quasiSober_points_of_isZariskiLocallyQuasiSeparatedOver` its two
  halves.
* `AlgebraicGeometry.Space.localRingDimension_eq_zero_iff_mem_genericPoints_of_quasiSeparated`:
  a point of a quasi-separated algebraic space has a local ring of dimension zero exactly when it
  is a generic point of an irreducible component of the point space.

## References

* [Stacks Project, Tag 004X](https://stacks.math.columbia.edu/tag/004X)
* [Stacks Project, Tag 02X5](https://stacks.math.columbia.edu/tag/02X5)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
* [Stacks Project, Tag 06NJ](https://stacks.math.columbia.edu/tag/06NJ)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 03W7](https://stacks.math.columbia.edu/tag/03W7)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 0ADC](https://stacks.math.columbia.edu/tag/0ADC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ

/-- A Zariski locally quasi-separated algebraic space over `S` is decent: each of its points
is the class of a quasi-compact monomorphism from the spectrum of a field. -/
theorem isDecentSpace_of_isZariskiLocallyQuasiSeparatedOver
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsZariskiLocallyQuasiSeparatedOver B S hS F) :
    IsDecentSpace B S hS F :=
  (isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS F hF).2
    (hasFiniteChartAndRelationFibersAtEveryPoint_of_isReasonableSpace B S hS F hF
      (isReasonableSpace_of_isVeryReasonableSpace B S hS F hF
        (isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ F hF
          (((isZariskiLocallyQuasiSeparatedOver_tfae B S hS hZ F hF).out 1 2).mp hqs))))

/-- The schematic locus of a Zariski locally quasi-separated algebraic space over `S` is dense
in its space of points; so that space has a dense open subspace which is a scheme. -/
@[stacks 06NH "density"]
theorem denseRange_schematicLocus_of_isZariskiLocallyQuasiSeparatedOver
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsZariskiLocallyQuasiSeparatedOver B S hS F) :
    DenseRange (pointsMap B S hS (schematicLocus B S hS F).toFunctor
      (schematicLocus B S hS F).ι) := by
  obtain ⟨G, hGopen, hGrep, hGdense⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS hF
      (isDecentSpace_of_isZariskiLocallyQuasiSeparatedOver B S hS hZ F hF hqs)
  exact hGdense.mono (range_pointsMap_ι_le_schematicLocus B S hS G hGopen hGrep)

/-- Two points of the space of points of a Zariski locally quasi-separated algebraic space over
`S` which are topologically indistinguishable are equal. -/
@[stacks 06NJ "Kolmogorov property"]
theorem t0Space_points_of_isZariskiLocallyQuasiSeparatedOver
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsZariskiLocallyQuasiSeparatedOver B S hS F) :
    T0Space (points B S hS F) :=
  t0Space_points_of_isDecentSpace B S hS hF
    (isDecentSpace_of_isZariskiLocallyQuasiSeparatedOver B S hS hZ F hF hqs)

/-- Every irreducible closed subset of the space of points of a Zariski locally quasi-separated
algebraic space over `S` is the closure of one of its points. -/
@[stacks 06NJ "generic points of irreducible closed subsets"]
theorem quasiSober_points_of_isZariskiLocallyQuasiSeparatedOver
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsZariskiLocallyQuasiSeparatedOver B S hS F) :
    QuasiSober (points B S hS F) :=
  quasiSober_points_of_isDecentSpace B S hS hF
    (isDecentSpace_of_isZariskiLocallyQuasiSeparatedOver B S hS hZ F hF hqs)

/-- The space of points of a Zariski locally quasi-separated algebraic space over `S` is sober:
every irreducible closed subset of it has a unique generic point. -/
@[stacks 06NJ]
theorem stacksSober_points_of_isZariskiLocallyQuasiSeparatedOver
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsZariskiLocallyQuasiSeparatedOver B S hS F) :
    StacksSober (points B S hS F) :=
  stacksSober_points_of_isDecentSpace B S hS hF
    (isDecentSpace_of_isZariskiLocallyQuasiSeparatedOver B S hS hZ F hF hqs)

/-- A quasi-separated algebraic space over `S` is Zariski locally quasi-separated over `S`. -/
theorem isZariskiLocallyQuasiSeparatedOver_of_quasiSeparated
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F) :
    IsZariskiLocallyQuasiSeparatedOver B S hS F :=
  ((isZariskiLocallyQuasiSeparatedOver_tfae B S hS hZ F hF).out 2 1).mp
    (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS F hZ hF hqs)

/-- A point of a quasi-separated algebraic space over `S` has a local ring of dimension zero —
equivalently, is a point of codimension `0` — exactly when it is a generic point of an
irreducible component of the space of points. -/
@[stacks 0ADC "the equivalence of conditions (1), (2) and (3)"]
theorem localRingDimension_eq_zero_iff_mem_genericPoints_of_quasiSeparated
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F) (x : points B S hS F) :
    localRingDimension B S hS x = 0 ↔ x ∈ genericPoints (points B S hS F) :=
  (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hF
    (isDecentSpace_of_isZariskiLocallyQuasiSeparatedOver B S hS hZ F hF
      (isZariskiLocallyQuasiSeparatedOver_of_quasiSeparated B S hS hZ F hF hqs)) x).symm

end AlgebraicGeometry.Space

end
