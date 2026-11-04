module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReduced

/-!
# Geometrically reduced algebraic spaces over a perfect field

Over a perfect field `k` — for instance any field of characteristic zero — reducedness is
already geometric: an algebraic space over `k` whose étale local ring at a geometric point
above `x` is reduced is geometrically reduced at `x`, and a reduced algebraic space over `k`
is geometrically reduced over `k`.

## Main results

* `AlgebraicGeometry.Space.isReduced_of_isReduced_strictHenselization`: a local ring with a
  reduced strict henselization is reduced.
* `AlgebraicGeometry.Space.isReduced_chartStalk_of_isReduced_etaleLocalRing`: reducedness of
  the étale local ring of an algebraic space at a geometric point passes to the ordinary local
  ring of a scheme chart carrying that point.
* `AlgebraicGeometry.Space.isGeometricallyReducedAt_of_isReduced_etaleLocalRing` is Stacks
  0E02 part (1). Part (2) is already in the library as
  `AlgebraicGeometry.Space.isGeometricallyReduced_of_isReduced`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReducedFieldExtension`, where the
  `@[stacks 0E02 "part (2)"]` attribute has been placed on it.

## Implementation notes

Part (1) is reduced to the scheme statement Stacks 020I over a scheme chart, using the
criterion of Stacks 0DMR that an algebraic space is geometrically reduced at a point exactly
when some étale scheme chart is geometrically reduced at a point above it.

Its hypothesis is about the étale local ring `𝒪_{X, x̄}` rather than the ordinary
local ring, so it has to be moved to a chart first. By Stacks 04KF the étale local ring is the
strict henselization of the local ring of a chart carrying `x̄`, and a local ring whose strict
henselization is reduced is reduced because the strict henselization is faithfully flat over
it, hence injective on it. The chart used is the one refining the tautological étale
neighbourhood of `x̄`, exactly as in the construction of
`AlgebraicGeometry.Space.baseToEtaleLocalRing`.

Only part (1) is proved here; see the section below on part (2).

## References

* [Stacks Project, Tag 0E02](https://stacks.math.columbia.edu/tag/0E02)
* [Stacks Project, Tag 020I](https://stacks.math.columbia.edu/tag/020I)
* [Stacks Project, Tag 0DMR](https://stacks.math.columbia.edu/tag/0DMR)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

/-- A local ring whose strict henselization is reduced is itself reduced: the strict
henselization is faithfully flat over it, hence the structure map is injective. -/
@[ega "IV 18.8.12" "(i)"]
theorem isReduced_of_isReduced_strictHenselization
    (A : Type u) [CommRing A] [IsLocalRing A] (κsep : Type u) [Field κsep]
    [Algebra (ResidueField A) κsep] [IsSepClosure (ResidueField A) κsep]
    (T : HenselizationTower A κsep) [_root_.IsReduced T.strictHenselization] :
    _root_.IsReduced A := by
  let : Module.FaithfullyFlat A T.strictHenselization :=
    IsHenselization.faithfullyFlat (R := A) (L := κsep)
  let : FaithfulSMul A T.strictHenselization := Module.FaithfullyFlat.faithfulSMul
  exact isReduced_of_injective (algebraMap A T.strictHenselization)
    (FaithfulSMul.algebraMap_injective A T.strictHenselization)

/-- Reducedness of the étale local ring of an algebraic space at a geometric point passes to
the ordinary local ring of a scheme chart carrying that point: by Stacks 04KF the former is the
strict henselization of the latter. -/
theorem isReduced_chartStalk_of_isReduced_etaleLocalRing
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {x : GeometricPoint B S hS F} (V : SmallEtaleNeighborhood x)
    (hred : _root_.IsReduced (etaleLocalRing B S hS F x)) :
    _root_.IsReduced ((neighborhoodChartScheme V).presheaf.stalk
      ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))) := by
  have hV : (bigEtaleSiteOfFppfSite B).Contains (neighborhoodChartScheme V) :=
    V.chart.obj.left.left.property
  have e := strictHenselizationEquivEtaleLocalRing hF V (bigEtaleSiteOfFppfSite B) hV
    (henselizationTower _ _)
  have hsh : _root_.IsReduced
      (henselizationTower
        ((neighborhoodChartScheme V).presheaf.stalk
          ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField)))
        (separableClosure (ResidueField ((neighborhoodChartScheme V).presheaf.stalk
            ((chartGeometricPoint V).hom
              (closedPoint (chartGeometricPoint V).residueField))))
          (chartGeometricPoint V).residueField)).strictHenselization :=
    let : _root_.IsReduced (etaleLocalRing B S hS F x) := hred
    isReduced_of_injective e.toRingHom e.injective
  let := hsh
  exact isReduced_of_isReduced_strictHenselization _
    (separableClosure (ResidueField ((neighborhoodChartScheme V).presheaf.stalk
        ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))))
      (chartGeometricPoint V).residueField)
    (henselizationTower _ _)

variable (k : Type u) [Field k] [PerfectField k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (.of k)))
  (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)

/-- **Stacks 0E02, part (1).** Let `X` be an algebraic space over a perfect field `k`, for
example a field of characteristic zero. If the étale local ring `𝒪_{X, x̄}` at a geometric
point `x̄` above `x` is reduced, then `X` is geometrically reduced at `x`. -/
@[stacks 0E02 "part (1)"]
theorem isGeometricallyReducedAt_of_isReduced_etaleLocalRing
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (x : points B (Spec (.of k)) hk X)
    (xbar : GeometricPoint B (Spec (.of k)) hk X) (hxbar : xbar.LiesOver x)
    (hred : _root_.IsReduced (etaleLocalRing B (Spec (.of k)) hk X xbar)) :
    IsGeometricallyReducedAt k B hk X hX x := by
  obtain ⟨V, -⟩ := EtaleNeighborhood.exists_smallEtaleNeighborhood_refinement
    (EtaleNeighborhood.self hX xbar)
  rw [isGeometricallyReducedAt_iff_exists_etaleChart]
  refine ⟨V.chart.obj.left, V.chart.obj.hom,
    (isEtale_iff_presheaf_of_yoneda B (Spec (.of k)) hk V.chart.obj.hom).mpr V.chart.property,
    { carrier := xbar.val.carrier, contained := xbar.val.contained,
      toBase := xbar.val.toBase, value := V.point }, ?_, ?_⟩
  · refine Eq.trans ?_ hxbar
    exact congrArg (fun v => (⟨xbar.val.carrier, xbar.val.contained, xbar.val.toBase, v⟩ :
      FieldValuedPoint B (Spec (.of k)) hk X).class B (Spec (.of k)) hk X) V.point_comp
  · let : _root_.IsReduced ((B.inclusion.obj (Over.left V.chart.obj.left)).presheaf.stalk
        (schemePoint B (Spec (.of k)) hk V.chart.obj.left
          { carrier := xbar.val.carrier, contained := xbar.val.contained,
            toBase := xbar.val.toBase, value := V.point })) :=
      isReduced_chartStalk_of_isReduced_etaleLocalRing hX V hred
    exact _root_.AlgebraicGeometry.isGeometricallyReducedAt_of_isReduced
      (B.inclusion.map V.chart.obj.left.hom) _

/-! ### Part (2)

Part (2) of [Stacks Project, Tag 0E02] — over a perfect field a reduced algebraic space is
geometrically reduced — is **not** restated here. The library already proves it, as
`AlgebraicGeometry.Space.isGeometricallyReduced_of_isReduced` in
`StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReducedFieldExtension`, with a
statement identical to the one this module would have given. That declaration carries the
`@[stacks 0E02 "part (2)"]` attribute; restating it here would have been a duplicate. -/

end AlgebraicGeometry.Space

end
