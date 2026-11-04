module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtaleLocalRingChartIndependence

/-!
# The map of Stacks 0EMZ along a morphism of decent algebraic spaces

Let `g : X ⟶ Y` be a morphism of algebraic spaces, let `(U, u)` be an elementary étale
neighbourhood of a point `x` of `X`, let `(V, v)` be one of a point `y` of `Y` and let
`j : U ⟶ V` be a morphism of schemes over `g` carrying `u` to `v` — the chart square of
`AlgebraicGeometry.Space.exists_henselianLocalRingHom_chartSquare`.

This file describes the two canonical maps of that square, in relation to the naturality of the
map of Stacks 0EMZ along `g`, the commutativity

`𝒪^h_{Y, y} ⟶ 𝒪^h_{X, x} ⟶ 𝒪_{X, x̄}  =  𝒪^h_{Y, y} ⟶ 𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}`

of the square whose verticals are the maps of Stacks 0EMZ.

## Main results

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.liftGeometricPoint_comp_of_square`: the
  chosen lift of a geometric point `x̄` of `X` to `U`, composed with `j`, is the chosen lift of
  the image geometric point to `V`. This is Stacks 0H2X: both factor through the residue-field
  point of `v`, which is a monomorphic representative of `y`.
* `AlgebraicGeometry.Space.chartStalkToEtaleLocalRing_stalkMap_square`: the commuting square of
  local rings of Stacks 05VU, read on the stalk at a chosen spelling of the chart point.
* `AlgebraicGeometry.Space.chartStalkToEtaleLocalRing_square`: the same square for an opaque
  pair of small étale neighbourhoods related by a morphism of charts over `g` carrying the
  chosen lift to the chosen lift, which is the form a chart square instantiates.

## Implementation notes

The last statement is phrased for an opaque pair `(N, M, jj)` and not for the chart square
itself. The chosen lift `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.liftGeometricPoint`
is a choice term built from the monomorphism property of the residue-field point; the same
statement written at `U.smallEtaleNeighborhood x̄ _` and `V.smallEtaleNeighborhood ȳ _` makes the
elaborator unfold those choice terms on every definitional check, while the opaque form is
strictly more general.

## References

* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 0EMZ](https://stacks.math.columbia.edu/tag/0EMZ)
* [Stacks Project, Tag 0H2X](https://stacks.math.columbia.edu/tag/0H2X)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  {hY : IsAlgebraicSpace B S hS Y} (g : X ⟶ Y)
  {x : points B S hS X} {y : points B S hS Y}

namespace ElementaryEtaleNeighborhood

/-- **The chosen lift of a geometric point is natural along a chart square.** Let `j : U ⟶ V` be
a morphism of schemes over `g : X ⟶ Y` between an elementary étale neighbourhood of `x` and one
of `y`, carrying the distinguished point to the distinguished point. Then the chosen lift of a
geometric point `x̄` over `x` to `U`, composed with `j`, is the chosen lift to `V` of the image
geometric point of `Y`.

Both are factorizations of the image geometric point through the residue-field point of `v`,
which is a monomorphic representative of `y`, so Stacks 0H2X makes them equal. -/
theorem liftGeometricPoint_comp_of_square
    (U : ElementaryEtaleNeighborhood B S hS X hX x)
    (V : ElementaryEtaleNeighborhood B S hS Y hY y)
    (j : U.scheme ⟶ V.scheme) (hj : j.left.1 U.point = V.point)
    (hsq : yoneda.map j ≫ V.toSpace = U.toSpace ≫ g)
    (xbar : GeometricPoint B S hS X) (hxbar : xbar.LiesOver x)
    (hybar : (geometricPointMap g xbar).LiesOver y) :
    U.liftGeometricPoint xbar hxbar ≫ j =
      V.liftGeometricPoint (geometricPointMap g xbar) hybar := by
  set m := pointedResidueFieldMap B S hS j U.point V.point hj U.residueField_contained
    V.residueField_contained with hm
  have hg : (U.liftResidueField xbar hxbar ≫ m) ≫ V.fromResidueField =
      U.liftGeometricPoint xbar hxbar ≫ j := by
    rw [Category.assoc, hm, pointedResidueFieldMap_comp, liftGeometricPoint, Category.assoc]
  have step1 : Y.map (U.liftResidueField xbar hxbar ≫ m).op
        (neighborhoodFieldPoint B S hS Y hY y V).value =
      yonedaEquiv (yoneda.map (U.liftResidueField xbar hxbar ≫ m) ≫
        yoneda.map V.fromResidueField ≫ V.toSpace) :=
    yonedaEquiv_naturality _ _
  have step2 : yonedaEquiv (yoneda.map (U.liftResidueField xbar hxbar ≫ m) ≫
        yoneda.map V.fromResidueField ≫ V.toSpace) =
      yonedaEquiv (yoneda.map (U.liftGeometricPoint xbar hxbar) ≫ U.toSpace ≫ g) := by
    rw [← Category.assoc, ← yoneda.map_comp, hg, yoneda.map_comp, Category.assoc, hsq]
  have step3 : yonedaEquiv (yoneda.map (U.liftGeometricPoint xbar hxbar) ≫ U.toSpace ≫ g) =
      (geometricPointMap g xbar).val.value := by
    rw [← Category.assoc, yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact congrArg (g.app (op (xbar.val.siteObject B S hS X)))
      (U.toSpace_liftGeometricPoint xbar hxbar)
  have hval : Y.map (U.liftResidueField xbar hxbar ≫ m).op
      (neighborhoodFieldPoint B S hS Y hY y V).value =
      (geometricPointMap g xbar).val.value := (step1.trans step2).trans step3
  have key : U.liftResidueField xbar hxbar ≫ m =
      V.liftResidueField (geometricPointMap g xbar) hybar :=
    (FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS Y hY
      (neighborhoodFieldPoint B S hS Y hY y V) (geometricPointMap g xbar).val
      ((neighborhoodFieldPoint_class B S hS Y hY y V).trans hybar.symm)).unique hval
      (V.map_liftResidueField (geometricPointMap g xbar) hybar)
  rw [← hg, key, liftGeometricPoint]
  rfl

end ElementaryEtaleNeighborhood

/-- **The commuting square of local rings of Stacks 05VU at a chosen spelling of the chart
point.** Read on the stalk at a spelling `p` of the chart point of `N`, the map of Stacks 05VP
precomposed with the stalk map of the vertical morphism of a square of charts over `g` is the
map of Stacks 05VP of the target chart followed by the map of étale local rings of
Stacks 04NG. -/
theorem chartStalkToEtaleLocalRing_stalkMap_square {xbar : GeometricPoint B S hS X}
    (N : SmallEtaleNeighborhood xbar) (C : SmallEtale B S hS Y)
    (gg : N.chart.obj.left ⟶ C.obj.left)
    (hcomm : N.chart.obj.hom ≫ g = yoneda.map gg ≫ C.obj.hom)
    {p : chartScheme N.chart} (hp : chartPoint B S hS X N = p)
    (hq : chartPoint B S hS Y (targetNeighborhood B S hS N C gg hcomm) =
      ((BigFppfOver.toScheme B S hS).map gg).base p) :
    (chartStalkToEtaleLocalRing B S hS hX N hp).comp
        ((((BigFppfOver.toScheme B S hS).map gg).stalkMap p).hom) =
      (etaleLocalRingMap hX g xbar).comp
        (chartStalkToEtaleLocalRing B S hS hY
          (targetNeighborhood B S hS N C gg hcomm) hq) := by
  subst hp
  rw [chartStalkToEtaleLocalRing_rfl]
  refine Eq.trans (etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing B S hS
    (Xs := ⟨X, hX⟩) (Ys := ⟨Y, hY⟩) ⟨g⟩ xbar N C gg hcomm) ?_
  exact congrArg (fun φ ↦ (etaleLocalRingMap hX g xbar).comp φ)
    (chartStalkToEtaleLocalRing_rfl B S hS hY
      (targetNeighborhood B S hS N C gg hcomm)).symm

/-- **The commuting square of local rings of Stacks 05VU on a square of pointed charts.** Let
`jj` be a morphism over `g` from the chart of a small étale neighbourhood `N` of `x̄` to the
chart of a small étale neighbourhood `M` of the image geometric point, carrying the chosen lift
to the chosen lift. Then the homomorphism `𝒪_{M, q} → 𝒪_{N, p}` of local rings it induces,
followed by the canonical map of Stacks 05VP into `𝒪_{X, x̄}`, is the canonical map of
Stacks 05VP into `𝒪_{Y, ȳ}` followed by the map of étale local rings of Stacks 04NG. -/
theorem chartStalkToEtaleLocalRing_square {xbar : GeometricPoint B S hS X}
    (N : SmallEtaleNeighborhood xbar) (M : SmallEtaleNeighborhood (geometricPointMap g xbar))
    (jj : N.chart.obj.left ⟶ M.chart.obj.left)
    (hcomm : N.chart.obj.hom ≫ g = yoneda.map jj ≫ M.chart.obj.hom)
    (hpoint : N.point ≫ jj = M.point)
    {p : chartScheme N.chart} (hp : chartPoint B S hS X N = p)
    {q : chartScheme M.chart} (hq : chartPoint B S hS Y M = q)
    (hqp : q = ((BigFppfOver.toScheme B S hS).map jj).base p) :
    (chartStalkToEtaleLocalRing B S hS hX N hp).comp
        ((((chartScheme M.chart).presheaf.stalkCongr (Inseparable.of_eq hqp)).hom ≫
          ((BigFppfOver.toScheme B S hS).map jj).stalkMap p).hom) =
      (etaleLocalRingMap hX g xbar).comp (chartStalkToEtaleLocalRing B S hS hY M hq) := by
  refine RingHom.ext fun a ↦ ?_
  set t := (((chartScheme M.chart).presheaf.stalkCongr (Inseparable.of_eq hqp)).hom).hom a
    with ht
  have h1 := RingHom.congr_fun (chartStalkToEtaleLocalRing_stalkMap_square B S hS hX (hY := hY) g
    N M.chart jj hcomm hp (congrArg (((BigFppfOver.toScheme B S hS).map jj).base) hp)) t
  have h2 := congrArg (etaleLocalRingMap hX g xbar) (RingHom.congr_fun
    (chartStalkToEtaleLocalRing_congr B S hS hY (W := M.chart)
      (ℓ₁ := N.point ≫ jj) (ℓ₂ := M.point)
      (targetNeighborhood B S hS N M.chart jj hcomm).point_comp M.point_comp hpoint
      (congrArg (((BigFppfOver.toScheme B S hS).map jj).base) hp) (hq.trans hqp)) t)
  have h3 := congrArg (etaleLocalRingMap hX g xbar)
    (chartStalkToEtaleLocalRing_stalkCongr B S hS hY M hq hqp a)
  exact (h1.trans h2).trans h3

end AlgebraicGeometry.Space

end
