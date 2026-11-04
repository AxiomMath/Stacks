module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedChartFibreSquareDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# Closed chart fibre squares from one closed point of the target chart

`AlgebraicGeometry.Space.HasClosedChartFibreSquare` asks for two closedness conditions on a chart
square: the chart point of the apex must be closed in the chart fibre of the leg, and its second
coordinate must be closed in the chart fibre of `h`. When `h` is a morphism of the site whose
morphism of schemes is locally of finite type, both conditions follow from closedness of a single
point of the scheme `U'`.

## Main results

* `AlgebraicGeometry.Space.isClosed_singleton_chartGeometricPoint_of_isClosed`: the chart point
  of a small étale neighbourhood of a geometric point of a *represented* presheaf is closed in
  the chart scheme as soon as the point it lies over is closed in the representing scheme.
* `AlgebraicGeometry.Space.hasClosedChartFibreSquare_of_isClosed_pointsToScheme`:
  `AlgebraicGeometry.Space.HasClosedChartFibreSquare` for a leg which is a base change of
  `yoneda.map h`, from closedness of the second coordinate of the point in the scheme `U'`.

## References

* [Stacks Project, Tag 01T8](https://stacks.math.columbia.edu/tag/01T8)
* [Stacks Project, Tag 053M](https://stacks.math.columbia.edu/tag/053M)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The chart of a small étale neighbourhood of a geometric point of a represented presheaf is the
Yoneda image of a morphism of the site whose morphism of schemes is étale. -/
private theorem exists_yoneda_map_chart_etale {U : BigFppfOver B S hS}
    {x : GeometricPoint B S hS (yoneda.obj U)} (V : SmallEtaleNeighborhood x) :
    ∃ c : V.chart.obj.left ⟶ U, yoneda.map c = V.chart.obj.hom ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map c) := by
  obtain ⟨c, hc⟩ := yoneda.map_surjective V.chart.obj.hom
  exact ⟨c, hc, (presheaf_yoneda_map_etale_iff B S hS c).1 (by rw [hc]; exact V.chart.property)⟩

/-- **The chart point of a small étale neighbourhood of a geometric point of a represented
presheaf is closed as soon as the point below it is.** -/
theorem isClosed_singleton_chartGeometricPoint_of_isClosed {U : BigFppfOver B S hS}
    {x : GeometricPoint B S hS (yoneda.obj U)} (V : SmallEtaleNeighborhood x)
    (hcl : IsClosed ({pointsToScheme B S hS U x.image} :
      Set ((BigFppfOver.toScheme B S hS).obj U))) :
    IsClosed ({(chartGeometricPoint V).hom
      (IsLocalRing.closedPoint (chartGeometricPoint V).residueField)} :
      Set (neighborhoodChartScheme V)) := by
  obtain ⟨c, hc, hcEt⟩ := exists_yoneda_map_chart_etale B S hS V
  have hpt : (BigFppfOver.toScheme B S hS).map c
        ((chartGeometricPoint V).hom
          (IsLocalRing.closedPoint (chartGeometricPoint V).residueField)) =
      pointsToScheme B S hS U x.image := by
    have hcls : pointsToScheme B S hS V.chart.obj.left
        ((chartFieldValuedPoint V).class B S hS (yoneda.obj V.chart.obj.left)) =
        (chartGeometricPoint V).hom
          (IsLocalRing.closedPoint (chartGeometricPoint V).residueField) := rfl
    rw [← hcls, ← pointsToScheme_pointsMap_yoneda B S hS c, hc]
    exact congrArg (pointsToScheme B S hS U) (chartFieldValuedPoint_pointsMap V)
  let := hcEt
  exact Stacks.Curves.isClosed_singleton_of_quasiFinite_preimage
    ((BigFppfOver.toScheme B S hS).map c) _
    (by rwa [hpt])

/-- **A closed chart fibre square from one closed point of the target chart.** Let `h : U' ⟶ U` be
a morphism of the site whose morphism of schemes is locally of finite type, let a leg `π₁ : Z ⟶ W`
sit in a cartesian square `IsPullback π₁ π₂ k (yoneda.map h)` of presheaves, and let `a` be a
geometric point of `Z` whose second coordinate `π₂(a)` is a *closed* point of the scheme `U'`. Then
`AlgebraicGeometry.Space.HasClosedChartFibreSquare` holds for `π₁`. -/
theorem hasClosedChartFibreSquare_of_isClosed_pointsToScheme
    {W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U U' : BigFppfOver B S hS}
    (hW : IsAlgebraicSpace B S hS W) (hZ : IsAlgebraicSpace B S hS Z)
    (k : W ⟶ yoneda.obj U) (h : U' ⟶ U)
    (hh : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h))
    (π₁ : Z ⟶ W) (π₂ : Z ⟶ yoneda.obj U')
    (hsq₀ : IsPullback π₁ π₂ k (yoneda.map h))
    (a : GeometricPoint B S hS Z)
    (hcl : IsClosed ({pointsToScheme B S hS U' (geometricPointMap π₂ a).image} :
      Set ((BigFppfOver.toScheme B S hS).obj U'))) :
    HasClosedChartFibreSquare B S hS (yoneda.map h) π₁ π₂ a := by
  obtain ⟨M, N, P, Q, gfst, gsnd, gh, gk, hNaff, hQaff, hcomm₁, hcomm₂, hpoint₁, hpoint₂,
    hmp, hsq⟩ :=
    exists_pointed_chart_square_of_isPullback B S hS hW (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS U') k (yoneda.map h) π₁ π₂ hsq₀ hZ a
  have hPcl : IsClosed ({(chartGeometricPoint P).hom
      (IsLocalRing.closedPoint (chartGeometricPoint P).residueField)} :
      Set (neighborhoodChartScheme P)) :=
    isClosed_singleton_chartGeometricPoint_of_isClosed B S hS P hcl
  have hgsnd : (BigFppfOver.toScheme B S hS).map gsnd
        ((chartGeometricPoint M).hom
          (IsLocalRing.closedPoint (chartGeometricPoint M).residueField)) =
      (chartGeometricPoint P).hom
        (IsLocalRing.closedPoint (chartGeometricPoint P).residueField) := by
    have hmaps : (BigFppfOver.toScheme B S hS).map M.point ≫
        (BigFppfOver.toScheme B S hS).map gsnd =
        (BigFppfOver.toScheme B S hS).map P.point := by
      rw [← Functor.map_comp, hmp]
      rfl
    exact congrArg (fun m => m (IsLocalRing.closedPoint a.val.carrier)) hmaps
  have hcl₂ : IsClosed ({((BigFppfOver.toScheme B S hS).map gh).asFiber
      ((BigFppfOver.toScheme B S hS).map gsnd
        ((chartGeometricPoint M).hom
          (IsLocalRing.closedPoint (chartGeometricPoint M).residueField)))} : Set _) := by
    rw [hgsnd]
    exact isClosed_singleton_asFiber_of_isClosed _ _ hPcl
  have hghft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map gh) := by
    obtain ⟨cP, hcP, _⟩ := exists_yoneda_map_chart_etale B S hS P
    obtain ⟨cQ, hcQ, -⟩ := exists_yoneda_map_chart_etale B S hS Q
    have hsite : cP ≫ h = gh ≫ cQ := by
      refine yoneda.map_injective ?_
      rwa [Functor.map_comp, Functor.map_comp, hcP, hcQ]
    have hschemes : (BigFppfOver.toScheme B S hS).map cP ≫ (BigFppfOver.toScheme B S hS).map h =
        (BigFppfOver.toScheme B S hS).map gh ≫ (BigFppfOver.toScheme B S hS).map cQ := by
      rw [← Functor.map_comp, ← Functor.map_comp, hsite]
    let := hh
    have hleft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map cP ≫
        (BigFppfOver.toScheme B S hS).map h) := inferInstance
    rw [hschemes] at hleft
    exact LocallyOfFiniteType.of_comp hleft
  let := hghft
  have hcl₁ : IsClosed ({((BigFppfOver.toScheme B S hS).map gfst).asFiber
      ((chartGeometricPoint M).hom
        (IsLocalRing.closedPoint (chartGeometricPoint M).residueField))} : Set _) :=
    isClosed_asFiber_of_isPullback hsq _ hcl₂
  exact ⟨M, N, P, Q, gfst, gsnd, gh, gk, hNaff, hQaff, hcomm₁, hcomm₂, hpoint₁, hpoint₂, hmp,
    hsq, hcl₁, hcl₂⟩

end AlgebraicGeometry.Space

end
