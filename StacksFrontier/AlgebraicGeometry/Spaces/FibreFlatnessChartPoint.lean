module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreFlatnessGeometricPoint

/-!
# Stacks 05WY condition (3) at a point of a chart, and the choice of geometric point

Work in Situation 05WX: a scheme `S`, algebraic spaces `X`, `Y`, `Z` over `S` with morphisms
`f : X ⟶ Y` and `h : Y ⟶ Z`, a quasi-coherent `𝒪_X`-module `F`, and a point of `X`.

Condition (3) of Stacks 05WY reads: *pick a commutative diagram of schemes `U ⟶ V ⟶ W` étale
over `X ⟶ Y ⟶ Z`, **and a point `u ∈ U` mapping to `x`**; then `F_w` is flat over `V_w` at `u`*.
`StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessGeometricPoint.lean` states it with the
point presented as a *lift of a geometric point to the chart*, which by Stacks 05VN is the same
data.  This file states it with the point presented as the source does, a point `u` of `U`
above `x` with no lift chosen, and proves that reading equivalent to condition (1).

That form of condition (3) mentions the geometric point of condition (1) only through its image
in `|X|`, so it yields what the source needs for condition (1) to be well posed and does not
state: the condition of Stacks 05WY at a geometric point depends only on the point of `|X|` it
lies over.

## Main definitions

* `AlgebraicGeometry.Space.chartZariskiModuleStalkAt`: the Zariski stalk `(a^* F)_u` of the
  chart restriction at an arbitrary point `u` of the chart, rather than at the point under a
  chosen lift of a geometric point.
* `AlgebraicGeometry.Space.IsFibreFlatOnChartSquares`: **condition (3) of Stacks 05WY at a
  point `u` of `U`**, read on the local rings of the charts.

## Main results

* `exists_chartPoint_isFibreFlatOnChartSquares_iff_isFibreFlatOverAtGeometricPoint`:
  **Stacks 05WY, conditions (1) and (3)**, with condition (3) carrying a point of `U` above the
  image of the geometric point, as the source states it.
* `AlgebraicGeometry.Space.isFibreFlatOverAtGeometricPoint_congr_of_image_eq`: **the condition
  of Stacks 05WY at a geometric point depends only on its image in `|X|`.**  This is the
  independence that makes the source's "pick a geometric point `x̄` of `X` lying over `x`" in
  condition (1) well posed.
* `AlgebraicGeometry.Space.isFibreFlatOnChartSquares_chartPoint`: at the point under a chosen
  lift the chart condition of this file is the one of
  `StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessGeometricPoint.lean`, by definition.

## Implementation notes

Everything the chart condition speaks of — the local rings `𝒪_{U, u}`, `𝒪_{V, v}`, `𝒪_{W, w}`,
the maps between them and the Zariski stalk `(a^* F)_u` — is a function of the chart and of the
point of it, and of nothing else about a geometric point: `chartLocalRing`, `chartZariskiPoint`
and `chartZariskiFiberIso` are all defined from `V.chart` and `chartPoint V`, and the point of a
target chart is the image of the point of the source chart on the nose
(`AlgebraicGeometry.Space.chartPoint_targetNeighborhood`).  So
`AlgebraicGeometry.Space.chartZariskiModuleStalkAt` is the body of
`AlgebraicGeometry.Space.chartZariskiModuleStalk` with the point taken as an argument, the two
agree by `rfl` at `u = chartPoint N`, and `AlgebraicGeometry.Space.IsFibreFlatOnChartSquares` is
likewise the chart condition of the pointed statement with `chartPoint N` replaced by `u`; the
agreement at `u = chartPoint N` is again definitional.

The commutativity of the two squares is not an argument of the predicate, since the condition
does not mention it; it is carried by the existential of the main theorem, which is where the
data of condition (3) is assembled.  This follows the treatment of condition (1) of Stacks 05VU,
`AlgebraicGeometry.Space.IsFlatOverAtOnChartDiagram`, whose body likewise uses only the charts
and the vertical morphism of its `AlgebraicGeometry.Space.ChartDiagram`.

The two directions of the main theorem are the two halves of Stacks 05VN.  A point of `U` above
the image of `x̄` is the point under a lift of `x̄` itself
(`AlgebraicGeometry.Space.exists_chartLift_of_chartPoint`), which turns the chart condition at
that point into the pointed one; conversely the point under a lift lies above the image
(`AlgebraicGeometry.Space.chartPoint_isChartPoint`), and a diagram exists by
`AlgebraicGeometry.Space.exists_chartSquares`.  This is exactly how Stacks 05VU is stated and
proved in `StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleAtGeometricPointEquiv.lean`.

Independence of the choice of geometric point is then a rewrite: the chart form of condition (3)
sees the geometric point only through `GeometricPoint.image`.  It is *not* obtained by comparing
the two étale local rings, which this development does not identify; the comparison is routed
through the charts, where there is nothing to compare.

## References

* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 05WX](https://stacks.math.columbia.edu/tag/05WX)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Opposite TopologicalSpace

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-! ### The Zariski stalk of the chart restriction at a point of the chart -/

/-- **The Zariski stalk `(a^* F)_u` at an arbitrary point of an étale scheme chart.**  This is
`AlgebraicGeometry.Space.chartZariskiModuleStalk` with the point of the chart taken as an
argument instead of being read off a chosen lift of a geometric point: the stalk of the chart
restriction at the point of the Zariski site of the chart determined by `u`, with its scalars
restricted along the identification of the fibre of the structure sheaf with `𝒪_{U, u}`. -/
def chartZariskiModuleStalkAt (U : SmallEtale B S hS X) (u : chartScheme U)
    (F : Modules.{u, m} B S hS X hX) :
    ModuleCat.{max u m} ↥((chartScheme U).presheaf.stalk u) :=
  (ModuleCat.restrictScalars (Opens.pointFiberStalkIso u (chartScheme U).presheaf).inv.hom).obj
    (Stacks.moduleStalkLarge (Opens.pointGrothendieckTopology u)
      (show Sheaf (Opens.grothendieckTopology (chartScheme U)) CommRingCat.{u} from
        (chartScheme U).sheaf)
      (restrictToChart B S hS hX F U))

/-- At the point under a chosen lift of a geometric point, the stalk of
`AlgebraicGeometry.Space.chartZariskiModuleStalkAt` is the pointed
`AlgebraicGeometry.Space.chartZariskiModuleStalk`, by definition. -/
theorem chartZariskiModuleStalkAt_chartPoint {x : GeometricPoint B S hS X}
    (N : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX) :
    chartZariskiModuleStalkAt B S hS X hX N.chart (chartPoint B S hS X N) F =
      chartZariskiModuleStalk B S hS X hX N F :=
  rfl

/-! ### Condition (3) of Stacks 05WY at a point of the chart -/

/-- **Condition (3) of Stacks 05WY at a point of `U`.**  Let `U ⟶ V ⟶ W` be étale scheme charts
of `X`, `Y`, `Z` with vertical morphisms `g₁ : U ⟶ V` and `g₂ : V ⟶ W`, and let `u` be a point
of `U`, with images `v` in `V` and `w` in `W`.  The condition is that the fibre
`(a^* F)_u / 𝔪_w (a^* F)_u` is flat over the fibre `𝒪_{V, v} / 𝔪_w 𝒪_{V, v}`.

Condition (3) of the source reads this on the scheme-theoretic fibres `U_w` and `V_w`; here it
is read on the local rings, through the canonical identifications
`𝒪_{V_w, v} = 𝒪_{V, v}/𝔪_w 𝒪_{V, v}` and `(F_w)_u = (a^* F)_u/𝔪_w (a^* F)_u` which the source
records at the start of its proof. -/
def IsFibreFlatOnChartSquares {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (F : Modules.{u, m} B S hS X hX) (U : SmallEtale B S hS X) (Vc : SmallEtale B S hS Y)
    (Wc : SmallEtale B S hS Z) (g₁ : U.obj.left ⟶ Vc.obj.left)
    (g₂ : Vc.obj.left ⟶ Wc.obj.left) (u : chartScheme U) : Prop :=
  Module.FlatQuotSMul
    (((BigFppfOver.toScheme B S hS).map g₁).stalkMap u).hom
    ((maximalIdeal ↥((chartScheme Wc).presheaf.stalk
        (((BigFppfOver.toScheme B S hS).map g₂).base
          (((BigFppfOver.toScheme B S hS).map g₁).base u)))).map
      (((BigFppfOver.toScheme B S hS).map g₂).stalkMap
        (((BigFppfOver.toScheme B S hS).map g₁).base u)).hom)
    (((maximalIdeal ↥((chartScheme Wc).presheaf.stalk
          (((BigFppfOver.toScheme B S hS).map g₂).base
            (((BigFppfOver.toScheme B S hS).map g₁).base u)))).map
        (((BigFppfOver.toScheme B S hS).map g₂).stalkMap
          (((BigFppfOver.toScheme B S hS).map g₁).base u)).hom).map
      (((BigFppfOver.toScheme B S hS).map g₁).stalkMap u).hom)
    rfl ↥(chartZariskiModuleStalkAt B S hS X hX U u F)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- At the point under a chosen lift of a geometric point, condition (3) of Stacks 05WY in the
form of `AlgebraicGeometry.Space.IsFibreFlatOnChartSquares` is the chart condition of
`AlgebraicGeometry.Space.flatQuotSMul_chartZariskiModuleStalk_iff_isFibreFlatOverAtGeometricPoint`,
by definition. -/
theorem isFibreFlatOnChartSquares_chartPoint {X Y Z : AlgebraicSpaces B S hS}
    (F : Modules.{u, m} B S hS X.1 X.2) {xbar : GeometricPoint B S hS X.1}
    (N : SmallEtaleNeighborhood xbar) (Vc : SmallEtale B S hS Y.1)
    (g₁ : N.chart.obj.left ⟶ Vc.obj.left) (Wc : SmallEtale B S hS Z.1)
    (g₂ : Vc.obj.left ⟶ Wc.obj.left) :
    IsFibreFlatOnChartSquares B S hS X.1 X.2 F N.chart Vc Wc g₁ g₂
        (chartPoint B S hS X.1 N) ↔
      Module.FlatQuotSMul
        (((BigFppfOver.toScheme B S hS).map g₁).stalkMap (chartPoint B S hS X.1 N)).hom
        ((maximalIdeal ↥((chartScheme Wc).presheaf.stalk
            (((BigFppfOver.toScheme B S hS).map g₂).base
              (((BigFppfOver.toScheme B S hS).map g₁).base
                (chartPoint B S hS X.1 N))))).map
          (((BigFppfOver.toScheme B S hS).map g₂).stalkMap
            (((BigFppfOver.toScheme B S hS).map g₁).base (chartPoint B S hS X.1 N))).hom)
        (((maximalIdeal ↥((chartScheme Wc).presheaf.stalk
              (((BigFppfOver.toScheme B S hS).map g₂).base
                (((BigFppfOver.toScheme B S hS).map g₁).base
                  (chartPoint B S hS X.1 N))))).map
            (((BigFppfOver.toScheme B S hS).map g₂).stalkMap
              (((BigFppfOver.toScheme B S hS).map g₁).base
                (chartPoint B S hS X.1 N))).hom).map
          (((BigFppfOver.toScheme B S hS).map g₁).stalkMap (chartPoint B S hS X.1 N)).hom)
        rfl ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) :=
  Iff.rfl

/-! ### Stacks 05WY, condition (3) as the source states it -/

/-- **Stacks 05WY: condition (3) if and only if condition (1), with condition (3) carrying a
point of `U` above `x`.**  In Situation 05WX the following are equivalent, for a geometric point
`x̄` of `X`:

1. writing `ȳ = f ∘ x̄` and `z̄ = h ∘ ȳ`, the fibre `F_x̄ / 𝔪_z̄ F_x̄` is flat over
   `𝒪_{Y, ȳ} / 𝔪_z̄ 𝒪_{Y, ȳ}`;
3. there is a commuting diagram of schemes `U ⟶ V ⟶ W` étale over `f` and `h`, **and a point
   `u` of `U` mapping to the image of `x̄` in `|X|`**, at which the fibre of `F|_U` over the
   fibre of `V` is flat.

This is condition (3) as the source states it: the source picks a diagram *and a point
`u ∈ U` mapping to `x`*, with no lift of the geometric point chosen.
`AlgebraicGeometry.Space.exists_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint` is the
same equivalence with the point presented as a lift of `x̄` to the chart.

Condition (3) is read on the local rings of the charts rather than on the scheme-theoretic
fibres `U_w` and `V_w`, through the canonical identifications
`𝒪_{V_w, v} = 𝒪_{V, v}/𝔪_w 𝒪_{V, v}` and `(F_w)_u = (F|_U)_u/𝔪_w (F|_U)_u` which the source
records at the start of its proof. -/
@[stacks 05WY "(1) iff (3), with condition (3) carrying a point u of U above x as the source \
states it rather than a lift of the geometric point; condition (3) read on the local rings of \
the charts"]
theorem exists_chartPoint_isFibreFlatOnChartSquares_iff_isFibreFlatOverAtGeometricPoint
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (xbar : GeometricPoint B S hS X.1) :
    (∃ (U : SmallEtale B S hS X.1) (Vc : SmallEtale B S hS Y.1) (Wc : SmallEtale B S hS Z.1)
        (g₁ : U.obj.left ⟶ Vc.obj.left)
        (_hcomm₁ : U.obj.hom ≫ f.hom = yoneda.map g₁ ≫ Vc.obj.hom)
        (g₂ : Vc.obj.left ⟶ Wc.obj.left)
        (_hcomm₂ : Vc.obj.hom ≫ h.hom = yoneda.map g₂ ≫ Wc.obj.hom)
        (u : chartScheme U),
      ChartPoint B S hS U.obj.left U.obj.hom u xbar.image ∧
        IsFibreFlatOnChartSquares B S hS X.1 X.2 F U Vc Wc g₁ g₂ u) ↔
      IsFibreFlatOverAtGeometricPoint B S hS f h F xbar := by
  constructor
  · rintro ⟨U, Vc, Wc, g₁, hcomm₁, g₂, hcomm₂, u, hcp, hflat⟩
    obtain ⟨q, hq, rfl⟩ := exists_chartLift_of_chartPoint B S hS X.2 xbar U u hcp
    exact (flatQuotSMul_chartZariskiModuleStalk_iff_isFibreFlatOverAtGeometricPoint
      B S hS f h ⟨U, q, hq⟩ Vc g₁ hcomm₁ Wc g₂ hcomm₂ F _ rfl _ rfl).1 hflat
  · intro hgeom
    obtain ⟨N, Vc, g₁, hcomm₁, Wc, g₂, hcomm₂⟩ := exists_chartSquares B S hS f h xbar
    exact ⟨N.chart, Vc, Wc, g₁, hcomm₁, g₂, hcomm₂, chartPoint B S hS X.1 N,
      chartPoint_isChartPoint B S hS xbar N,
      (flatQuotSMul_chartZariskiModuleStalk_iff_isFibreFlatOverAtGeometricPoint B S hS f h
        N Vc g₁ hcomm₁ Wc g₂ hcomm₂ F _ rfl _ rfl).2 hgeom⟩

/-! ### The condition does not depend on the chosen geometric point -/

/-- **The condition of Stacks 05WY at a geometric point depends only on the point of `|X|` it
lies over.**  For two geometric points `x̄`, `x̄'` of `X` with the same image in `|X|`,
condition (1) of Stacks 05WY holds at `x̄` exactly when it holds at `x̄'`. -/
@[stacks 05WY "well-posedness of 'pick a geometric point xbar of X lying over x' in \
condition (1): the condition at a geometric point depends only on its image in |X|"]
theorem isFibreFlatOverAtGeometricPoint_congr_of_image_eq {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (h : Y ⟶ Z) (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (xbar xbar' : GeometricPoint B S hS X.1) (himage : xbar.image = xbar'.image) :
    IsFibreFlatOverAtGeometricPoint B S hS f h F xbar ↔
      IsFibreFlatOverAtGeometricPoint B S hS f h F xbar' := by
  rw [← exists_chartPoint_isFibreFlatOnChartSquares_iff_isFibreFlatOverAtGeometricPoint
        B S hS f h F xbar,
    ← exists_chartPoint_isFibreFlatOnChartSquares_iff_isFibreFlatOverAtGeometricPoint
        B S hS f h F xbar', himage]

end AlgebraicGeometry.Space

end
