module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPointEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative

/-!
# Chartwise flatness of a module on an algebraic space, read on geometric points

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`F` be an `𝒪_X`-module.  Stacks 05VV defines flatness of `F` over `Y` chartwise, as
`AlgebraicGeometry.Space.IsFlatOver`: on *every* commuting square of étale scheme charts of `f`,
at *every* point of the chart of `X`, the restriction `F|_U` is flat over the chart of `Y`.
Stacks 05VU identifies the condition at one point of one square with flatness of the geometric
stalk `F_{x̄}` over the étale local ring `𝒪_{Y, ȳ}`, for a quasi-coherent `F`.  This file draws
the consequence: for a quasi-coherent module the universally quantified chartwise condition of
Stacks 05VV is equivalent to the chart-free condition that *every* geometric stalk is flat, and
is therefore already implied by the condition on a single surjective square.

That is the passage from the existential form of clause (1) of Stacks 05VU to the universal form
taken as the definition in Stacks 05VV.  It does not contradict the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleTargetChart.lean`, which record that
independence of the chart of `X` fails for a *general* `𝒪_X`-module: quasi-coherence is a
hypothesis of every statement below, as it is of Stacks 05VU, and it is also what the chart
base-change comparison of Stacks 03M0 needs — see "What this file does not itself give".

That the predicate depends on the module only through its isomorphism class — which needs no
quasi-coherence — is `AlgebraicGeometry.Space.isFlatOverOnChartDiagram_iff_of_iso` and
`AlgebraicGeometry.Space.isFlatOver_iff_of_iso` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleIso.lean`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtGeometricPoint`: **for a
  quasi-coherent module, flatness over `Y` in the sense of Stacks 05VV holds exactly when the
  geometric stalk of `F` is flat over the étale local ring of `Y` at every geometric point of
  `X`.**  This is the geometric-stalk form of Stacks 05VV, whose absence the implementation
  notes of `StacksFrontier/AlgebraicGeometry/Spaces/FlatModule.lean` record.
* `AlgebraicGeometry.Space.isFlatOver_of_isFlatOverOnChartDiagram_of_surjective`: **flatness
  over `Y` may be tested on one commuting square of étale scheme charts whose chart of `X` is
  surjective on points.**  This is the reduction step the proof of Stacks 05VW performs.

## Implementation notes

The iso-transport lemmas of `StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleIso.lean` used below
are the ringed-space statement `AlgebraicGeometry.isFlatOver_iff_of_moduleIso` of Stacks 08KT
applied to the restriction of the isomorphism to the chart, which is
`AlgebraicGeometry.Space.restrictToChartIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionFunctorial.lean`.  They are the reason
that file exists: without functoriality of the restriction in the module there is no morphism of
Zariski modules on the chart to feed to the ringed-space lemma.

The geometric criterion is Stacks 05VU in the pointed form
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint`, which is
stated at one square and the point under a *chosen lift* of the geometric point, rather than in
the existential form carrying the tag.  The pointed form is what converts the existential into
the universal: every point of every chart is the point under a lift of a geometric point —
`AlgebraicGeometry.Space.exists_chartLift_of_chartPoint`, Stacks 05VN on a chart, applied to
`AlgebraicGeometry.Space.exists_geometricRepresentative` and
`AlgebraicGeometry.Space.surjective_pointsToScheme` — so the condition at that point is a
condition on the geometric point alone.

For the converse a square through a given geometric point is produced from an étale atlas of
`Y` and `AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`, exactly as in the
proof of Stacks 05VU; surjectivity of the chart is used only through
`AlgebraicGeometry.Space.surjective_iff_surjective_pointsMap`, and
`AlgebraicGeometry.Space.isFlatOver_of_isFlatOverOnChartDiagram_of_surjective` therefore takes
surjectivity on points as its hypothesis rather than the morphism property.

The module universe is the universe `u` of the structure rings, as it must be for
`AlgebraicGeometry.Space.IsFlatOver` and for Stacks 05VU.

## What this file does not itself give

It does not itself give Stacks 05VW, base change of flat modules for algebraic spaces.  With the
reduction above, the remaining content of 05VW is its scheme-theoretic step: for a cartesian
square of algebraic spaces and charts `U' = V' ×_V U`, the restriction `F'|_{U'}` of the pulled
back module must be identified with the pullback of `F|_U` along `U' ⟶ U`, after which
Stacks 047C applies.  That identification **is available**, for a quasi-coherent module, as
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean` — the compatibility of
Stacks 03M0 with Stacks 03LW, which assumes no square cartesian — and 05VW itself is proved,
downstream of this file, in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleBaseChange.lean`.  The canonical comparison
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` is a different statement, between a chart restriction and the inverse image
of another chart restriction; it is only a morphism, and is not an isomorphism for a general
module.

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-! ### The geometric-stalk form of Stacks 05VV -/

/-- The scheme point of a point `y` of a represented presheaf lies over any point of `X` equal to
the image of `y`. -/
private theorem chartPoint_pointsToScheme_of_eq (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (y : points B S hS (yoneda.obj U)) {x : points B S hS X}
    (h : pointsMap B S hS (yoneda.obj U) a y = x) :
    ChartPoint B S hS U a (pointsToScheme B S hS U y) x :=
  h ▸ chartPoint_pointsToScheme B S hS U a y

/-- Every point of an étale scheme chart of `X` is the point under a lift of some geometric
point of `X` to that chart: a point of the chart scheme is the scheme point of a point of the
represented presheaf, which has a geometric representative, and Stacks 05VN lifts it. -/
theorem exists_geometricPoint_chartLift (hX' : IsAlgebraicSpace B S hS X)
    (U : SmallEtale B S hS X) (u : chartScheme U) :
    ∃ (xbar : GeometricPoint B S hS X) (q : xbar.val.siteObject ⟶ U.obj.left)
      (_ : U.obj.hom.app (Opposite.op xbar.val.siteObject) q = xbar.val.value),
      ((BigFppfOver.toScheme B S hS).map q)
        (IsLocalRing.closedPoint xbar.val.carrier) = u := by
  obtain ⟨z, hz⟩ := surjective_pointsToScheme B S hS U.obj.left u
  obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS X
    (pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom z)
  exact ⟨xbar, exists_chartLift_of_chartPoint B S hS hX' xbar U u
    (hz ▸ chartPoint_pointsToScheme_of_eq B S hS U.obj.left U.obj.hom z hxbar.symm)⟩

/-- **Flatness over `Y` may be tested on one commuting square of étale scheme charts whose
chart of `X` is surjective on points.**  For a quasi-coherent module the condition at a point
of a chart depends only on the geometric point beneath it, by Stacks 05VU, so a square whose
chart of `X` meets every point of `|X|` already sees all of Stacks 05VV.

This is the reduction performed by the proof of Stacks 05VW. -/
theorem isFlatOver_of_isFlatOverOnChartDiagram_of_surjective
    {Xs Ys : AlgebraicSpaces B S hS} (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [F.IsQuasicoherentOnSite]
    (d : ChartDiagram B S hS Xs.1 Ys.1 f.hom)
    (hd : Function.Surjective
      (pointsMap B S hS (yoneda.obj d.U.obj.left) d.U.obj.hom))
    (h : IsFlatOverOnChartDiagram B S hS Xs.2 F d) (xbar : GeometricPoint B S hS Xs.1) :
    IsFlatOverAtGeometricPoint B S hS f F xbar := by
  obtain ⟨y, hy⟩ := hd xbar.image
  obtain ⟨q, hq, -⟩ := exists_chartLift_of_chartPoint B S hS Xs.2 xbar d.U _
    (chartPoint_pointsToScheme_of_eq B S hS d.U.obj.left d.U.obj.hom y hy)
  exact (isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint B S hS f F
    ⟨d.U, q, hq⟩ d.V d.g d.comm).1 (h _)

/-- **The geometric-stalk form of Stacks 05VV.**  A quasi-coherent `𝒪_X`-module is flat over `Y`
in the chartwise sense of Stacks 05VV exactly when its geometric stalk `F_{x̄}` is flat over the
étale local ring `𝒪_{Y, ȳ}` at every geometric point `x̄` of `X`.

The right-hand condition mentions no chart, so this is also the independence of the chartwise
condition from the charts — which for a general, not necessarily quasi-coherent, `𝒪_X`-module is
false; see the implementation notes. -/
theorem isFlatOver_iff_forall_isFlatOverAtGeometricPoint {Xs Ys : AlgebraicSpaces B S hS}
    (f : Xs ⟶ Ys) (F : Modules.{u, u} B S hS Xs.1 Xs.2) [F.IsQuasicoherentOnSite] :
    IsFlatOver B S hS Xs.2 f.hom F ↔
      ∀ xbar : GeometricPoint B S hS Xs.1, IsFlatOverAtGeometricPoint B S hS f F xbar := by
  constructor
  · intro hflat xbar
    obtain ⟨V₀, b, hbSurjective, hbEtale⟩ := Ys.2.exists_atlas
    obtain ⟨U₀, a, g, hcomm, haSurjective, haEtale⟩ :=
      exists_surjective_etale_presentation_lift B S hS Xs.2 Ys.2 f.hom V₀ b
        hbSurjective hbEtale
    exact isFlatOver_of_isFlatOverOnChartDiagram_of_surjective B S hS f F
      { U := ⟨CostructuredArrow.mk a, haEtale⟩, V := ⟨CostructuredArrow.mk b, hbEtale⟩
        g := g, comm := hcomm }
      ((surjective_iff_surjective_pointsMap B S hS Xs.1 Xs.2 U₀ a).mp haSurjective)
      (hflat _) xbar
  · intro h d u
    obtain ⟨xbar, q, hq, rfl⟩ := exists_geometricPoint_chartLift B S hS Xs.2 d.U u
    exact (isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint B S hS f F
      ⟨d.U, q, hq⟩ d.V d.g d.comm).2 (h xbar)

end AlgebraicGeometry.Space

end
