module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularLocalRings
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.EtaleSiteOfFppfSite
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties

/-!
# Regularity of an algebraic space at a point and its étale local rings

An algebraic space is regular at a point exactly when its étale local ring at one geometric
point above that point is a regular local ring, and then at every geometric point above it.
Regularity at a point is the condition `AlgebraicGeometry.Space.IsRegularAt` on the local
rings of the étale scheme charts, and the étale local ring at a geometric point is a strict
henselization of such a local ring, so the two readings agree.

## Main results

* `AlgebraicGeometry.Space.isRegularAt_tfae`: regularity at a point, regularity of the étale
  local ring at every geometric point above it, and regularity of the étale local ring at
  some geometric point above it are equivalent.

## Implementation notes

The source's "any (equivalently some)" is two separate clauses of one `List.TFAE`, so neither
quantifier is privileged. No Noetherian hypothesis is imposed, as the source imposes none: the
Noetherianity that the henselization comparison of Tag 06LN needs is produced from the
regularity assumed on whichever side the implication starts, since a regular local ring is
Noetherian, and Noetherianity transfers across a strict henselization by Tag 06LJ.

The cycle of implications is (1) → (2) → (3) → (1). The outer two steps both pass through
`AlgebraicGeometry.Space.isRegularLocalRing_etaleLocalRing_iff_chart_of_regular`, applied to
a small étale neighbourhood of the geometric point at hand, which a surjective étale atlas
supplies by `AlgebraicGeometry.Space.exists_pointed_smallEtaleNeighborhood`. Such a
neighbourhood selects a field-valued point of its chart over the same field, and that chart
point lies above the image point of the geometric point, which is what feeds the universal
condition (1) and what the one-chart criterion
`AlgebraicGeometry.Space.isRegularAt_iff_exists_etale_chart` asks for. The middle step is the
existence of a geometric point above a prescribed point,
`AlgebraicGeometry.Space.exists_geometricRepresentative`.

## References

* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ)
* [Stacks Project, Tag 06LN](https://stacks.math.columbia.edu/tag/06LN)
* [Stacks Project, Tag 0AH9](https://stacks.math.columbia.edu/tag/0AH9)
* [Stacks Project, Tag 0AHA](https://stacks.math.columbia.edu/tag/0AHA)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 04KF and 06LN.** The étale local ring of an algebraic space at a geometric point
is regular exactly when the local ring of a small étale chart through that point is regular at
the point the chart selects. The étale local ring is a strict henselization of that local ring,
and either regularity hypothesis supplies the Noetherianity the comparison needs. -/
theorem isRegularLocalRing_etaleLocalRing_iff_chart_of_regular
    (hF : IsAlgebraicSpace B S hS F) {x : GeometricPoint B S hS F}
    (V : SmallEtaleNeighborhood x) :
    IsRegularLocalRing (etaleLocalRing B S hS F x) ↔
      IsRegularLocalRing ((chartScheme V.chart).presheaf.stalk
        ((chartGeometricPoint V).hom
          (closedPoint (chartGeometricPoint V).residueField))) := by
  let R := (chartScheme V.chart).presheaf.stalk
    ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))
  let κ := separableClosure (ResidueField R) (chartGeometricPoint V).residueField
  let T := IsLocalRing.henselizationTower R κ
  let e : T.strictHenselization ≃+* etaleLocalRing B S hS F x :=
    strictHenselizationEquivEtaleLocalRing hF V (bigEtaleSiteOfFppfSite B)
      V.chart.obj.left.left.property T
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : IsRegularLocalRing T.strictHenselization := IsRegularLocalRing.of_ringEquiv e.symm
    have : IsNoetherianRing R :=
      (isNoetherianRing_iff_henselizations R T.henselization T.strictHenselization κ).2.mpr
        inferInstance
    exact (isRegularLocalRing_iff_henselizations R T.henselization T.strictHenselization κ).2.mpr
      inferInstance
  · have : IsRegularLocalRing R := h
    have : IsRegularLocalRing T.strictHenselization :=
      (isRegularLocalRing_iff_henselizations R T.henselization T.strictHenselization κ).2.mp h
    exact IsRegularLocalRing.of_ringEquiv e

/-- A small étale neighbourhood of a geometric point above a point of the algebraic space is an
étale chart whose selected chart point lies above that point. -/
private theorem exists_smallEtaleNeighborhood_of_liesOver (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} {xbar : GeometricPoint B S hS F} (hxbar : xbar.LiesOver x) :
    ∃ V : SmallEtaleNeighborhood xbar,
      pointsMap B S hS (yoneda.obj V.chart.obj.left) V.chart.obj.hom
        ((chartFieldValuedPoint V).class B S hS (yoneda.obj V.chart.obj.left)) = x := by
  obtain ⟨U, f, hSurj, hEtale⟩ := hF.exists_atlas
  obtain ⟨⟨V, -⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS F hF xbar f hSurj hEtale
  exact ⟨V, (chartFieldValuedPoint_pointsMap V).trans hxbar⟩

/-- **Stacks 0AHA.** For a point `x` of an algebraic space `F` the three conditions are
equivalent: `F` is regular at `x`; the étale local ring of `F` is a regular local ring at every
geometric point above `x`; and it is a regular local ring at some geometric point above `x`. -/
@[stacks 0AHA]
theorem isRegularAt_tfae (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) :
    List.TFAE
      [IsRegularAt B S hS F x,
        ∀ xbar : GeometricPoint B S hS F, xbar.LiesOver x →
          IsRegularLocalRing (etaleLocalRing B S hS F xbar),
        ∃ xbar : GeometricPoint B S hS F, xbar.LiesOver x ∧
          IsRegularLocalRing (etaleLocalRing B S hS F xbar)] := by
  tfae_have 1 → 2 := by
    intro hx xbar hxbar
    obtain ⟨V, hV⟩ := exists_smallEtaleNeighborhood_of_liesOver hF hxbar
    exact (isRegularLocalRing_etaleLocalRing_iff_chart_of_regular hF V).mpr
      (hx V.chart.obj.left V.chart.obj.hom V.chart.property (chartFieldValuedPoint V) hV)
  tfae_have 2 → 3 := by
    intro hx
    obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS F x
    exact ⟨xbar, hxbar, hx xbar hxbar⟩
  tfae_have 3 → 1 := by
    rintro ⟨xbar, hxbar, hreg⟩
    obtain ⟨V, hV⟩ := exists_smallEtaleNeighborhood_of_liesOver hF hxbar
    exact (isRegularAt_iff_exists_etale_chart B S hS F hF x).mpr
      ⟨V.chart.obj.left, V.chart.obj.hom, V.chart.property, chartFieldValuedPoint V, hV,
        (isRegularLocalRing_etaleLocalRing_iff_chart_of_regular hF V).mp hreg⟩
  tfae_finish

end AlgebraicGeometry.Space

end
