module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra

/-!
# Stacks 05VU: flatness of a module over the target at a point of an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `F` be a
quasi-coherent `𝒪_X`-module and let `x̄` be a geometric point of `X`.  Stacks 05VU gives two
equivalent conditions:

1. there is a commuting square of étale scheme charts `U ⟶ V` over `f` and a point `u` of `U`
   above the image of `x̄` at which the restriction `a^* F` is flat over `V`;
2. the geometric stalk `F_{x̄}` is flat over the étale local ring `𝒪_{Y, ȳ}`, where
   `ȳ = f ∘ x̄`.

This file proves the equivalence.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint`:
  **Stacks 05VU**, the equivalence of conditions (1) and (2).
* `AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint`: the
  equivalence at one commuting square of charts and the point under a chosen lift of `x̄`, which
  is what makes the existential in (1) harmless.
* `AlgebraicGeometry.Space.flat_chartZariskiModuleStalk_iff_flat_geometricModuleStalk`: the
  heart of the proof — the Zariski stalk `(a^* F)_u` is flat over `𝒪_{V, v}` exactly when the
  geometric stalk `F_{x̄}` is.
* `AlgebraicGeometry.Space.exists_chartLift_of_chartPoint`: a point of an étale scheme chart
  above the image of `x̄` is the point under a lift of `x̄` itself, which is Stacks 05VN read on
  a chart.

## Implementation notes

The proof is the source's.  Condition (1) at the point under a lift of `x̄` is flatness of the
Zariski stalk over `𝒪_{V, v}`
(`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_flat_chartZariskiModuleStalk`); the
base-change formula `F_{x̄} = (a^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` of Stacks 05VP turns that into
flatness of `F_{x̄}` over `𝒪_{V, v}`, through Stacks 0584 (2) applied to the faithfully flat map
`𝒪_{U, u} → 𝒪_{X, x̄}`; and flatness over `𝒪_{V, v}` is condition (2) by Stacks 04KF and
Stacks 05VL, which is
`AlgebraicGeometry.Space.flat_chartLocalRing_geometricModuleStalk_iff`.  What reconciles the
two `𝒪_{V, v}`-module structures on `F_{x̄}` appearing in the last two steps is the commuting
square of local rings,
`AlgebraicGeometry.Space.etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing`.

The algebra instances are chosen so that both scalar towers hold by `rfl`: `𝒪_{V, v} → 𝒪_{X, x̄}`
is *defined* as the composite through `𝒪_{U, u}`, and the square is then used once, to rewrite
that composite into the one through `𝒪_{Y, ȳ}` which Stacks 05VL is stated for.

The existential in condition (1) costs no construction.  In one direction a point above the
image of `x̄` is the point under a lift of `x̄` by Stacks 05VN, so the pointed statement applies;
in the other a square is produced from an étale atlas of `Y` by Stacks 02X1, and the point is
the one under the lift.  Quasi-coherence of `F` is needed and is not decoration: it is the
hypothesis of Stacks 05VP.

The statement is at module universe `m = u`, as both conditions are: condition (1) is the
ringed-space predicate of Stacks 08KT on the chart, and Stacks 05VP is available there.

## References

* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 05VP and 0584 (2): the Zariski stalk and the geometric stalk -/

section Stalks

variable {Xs Ys : AlgebraicSpaces B S hS} (f : Xs ⟶ Ys)
  {xbar : GeometricPoint B S hS Xs.1} (N : SmallEtaleNeighborhood xbar)
  (V : SmallEtaleNeighborhood (geometricPointMap f.hom xbar))
  (F : Modules.{u, u} B S hS Xs.1 Xs.2)

/-- **Stacks 05VP through Stacks 0584 (2).**  The Zariski stalk `(a^* F)_u` of the restriction
of a quasi-coherent `𝒪_X`-module to an étale scheme chart is flat over the local ring of a
chart of `Y` exactly when the geometric stalk `F_{x̄}` is, the scalars being restricted along
`φ : 𝒪_{V, v} → 𝒪_{U, u}` respectively along the composite `χ` of `φ` with the canonical map
`𝒪_{U, u} → 𝒪_{X, x̄}`.

The base change `F_{x̄} = (a^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` of Stacks 05VP is along a faithfully
flat map, so Stacks 0584 (2) applies to it. -/
theorem flat_chartZariskiModuleStalk_iff_flat_geometricModuleStalk
    [F.IsQuasicoherentOnSite]
    (φ : ↥(chartLocalRing B S hS Ys.1 V) →+* ↥(chartLocalRing B S hS Xs.1 N))
    (χ : ↥(chartLocalRing B S hS Ys.1 V) →+* ↥(etaleLocalRing B S hS Xs.1 xbar))
    (hφ : (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N).comp φ = χ) :
    letI : Module ↥(chartLocalRing B S hS Ys.1 V)
        ↥(chartZariskiModuleStalk B S hS Xs.1 Xs.2 N F) := Module.compHom _ φ
    letI : Module ↥(chartLocalRing B S hS Ys.1 V)
        ↥(geometricModuleStalk B S hS Xs xbar F) := Module.compHom _ χ
    (Module.Flat ↥(chartLocalRing B S hS Ys.1 V)
        ↥(chartZariskiModuleStalk B S hS Xs.1 Xs.2 N F) ↔
      Module.Flat ↥(chartLocalRing B S hS Ys.1 V)
        ↥(geometricModuleStalk B S hS Xs xbar F)) := by
  subst hφ
  let : Algebra ↥(chartLocalRing B S hS Ys.1 V) ↥(chartLocalRing B S hS Xs.1 N) :=
    φ.toAlgebra
  let : Algebra ↥(chartLocalRing B S hS Xs.1 N) ↥(etaleLocalRing B S hS Xs.1 xbar) :=
    (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N).toAlgebra
  let : Algebra ↥(chartLocalRing B S hS Ys.1 V) ↥(etaleLocalRing B S hS Xs.1 xbar) :=
    ((chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N).comp φ).toAlgebra
  let : IsScalarTower ↥(chartLocalRing B S hS Ys.1 V) ↥(chartLocalRing B S hS Xs.1 N)
      ↥(etaleLocalRing B S hS Xs.1 xbar) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module ↥(chartLocalRing B S hS Ys.1 V)
      ↥(chartZariskiModuleStalk B S hS Xs.1 Xs.2 N F) := Module.compHom _ φ
  let : IsScalarTower ↥(chartLocalRing B S hS Ys.1 V) ↥(chartLocalRing B S hS Xs.1 N)
      ↥(chartZariskiModuleStalk B S hS Xs.1 Xs.2 N F) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Module.FaithfullyFlat ↥(chartLocalRing B S hS Xs.1 N)
      ↥(etaleLocalRing B S hS Xs.1 xbar) :=
    faithfullyFlat_chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N
  let : Module ↥(chartLocalRing B S hS Ys.1 V)
      ↥(geometricModuleStalk B S hS Xs xbar F) :=
    Module.compHom _ ((chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N).comp φ)
  let : IsScalarTower ↥(chartLocalRing B S hS Ys.1 V) ↥(etaleLocalRing B S hS Xs.1 xbar)
      ↥(geometricModuleStalk B S hS Xs xbar F) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  refine Iff.trans (Module.Flat.tensorProduct_iff_of_faithfullyFlat
    (R := ↥(chartLocalRing B S hS Ys.1 V)) (S := ↥(chartLocalRing B S hS Xs.1 N))
    (S' := ↥(etaleLocalRing B S hS Xs.1 xbar))
    (M := ↥(chartZariskiModuleStalk B S hS Xs.1 Xs.2 N F))).symm ?_
  let e := (@asIso _ _ _ _ _ (isIso_chartStalkTensorComparison B S hS Xs.2 N F)).toLinearEquiv
  exact Module.Flat.equiv_iff
    { toFun := e
      map_add' := fun t t' => map_add e t t'
      map_smul' := fun r t =>
        (congrArg e (algebraMap_smul ↥(etaleLocalRing B S hS Xs.1 xbar) r t).symm).trans
          (map_smul e (algebraMap ↥(chartLocalRing B S hS Ys.1 V)
            ↥(etaleLocalRing B S hS Xs.1 xbar) r) t)
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv }

end Stalks

/-! ### The equivalence at one commuting square of charts -/

section Pointed

variable {Xs Ys : AlgebraicSpaces B S hS} (f : Xs ⟶ Ys)
  (F : Modules.{u, u} B S hS Xs.1 Xs.2) [F.IsQuasicoherentOnSite]
  {xbar : GeometricPoint B S hS Xs.1}

/-- **Stacks 05VU at one commuting square of charts.**  In a commuting square of étale scheme
charts over `f` carrying a lift of the geometric point `x̄`, the restriction of a quasi-coherent
`𝒪_X`-module to the source chart is flat over the target chart at the point under that lift
exactly when the geometric stalk `F_{x̄}` is flat over the étale local ring `𝒪_{Y, ȳ}`. -/
theorem isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint
    (N : SmallEtaleNeighborhood xbar) (Wc : SmallEtale B S hS Ys.1)
    (g : N.chart.obj.left ⟶ Wc.obj.left)
    (hcomm : N.chart.obj.hom ≫ f.hom = yoneda.map g ≫ Wc.obj.hom) :
    IsFlatOverAtOnChartDiagram B S hS Xs.2 F
        { U := N.chart, V := Wc, g := g, comm := hcomm } (chartPoint B S hS Xs.1 N) ↔
      IsFlatOverAtGeometricPoint B S hS f F xbar := by
  let Vn := targetNeighborhood B S hS N Wc g hcomm
  refine Iff.trans (isFlatOverAtOnChartDiagram_iff_flat_chartZariskiModuleStalk
    B S hS Xs.2 F N Wc g hcomm) ?_
  refine Iff.trans (flat_chartZariskiModuleStalk_iff_flat_geometricModuleStalk B S hS f N Vn F
    ((((BigFppfOver.toScheme B S hS).map g).stalkMap (chartPoint B S hS Xs.1 N)).hom)
    ((etaleLocalRingMap Xs.2 f.hom xbar).comp
      (chartLocalRingToEtaleLocalRing B S hS Ys.1 Ys.2 Vn))
    (etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing B S hS f xbar N Wc g hcomm)) ?_
  exact flat_chartLocalRing_geometricModuleStalk_iff B S hS f F xbar Vn

end Pointed

/-! ### Points of a chart above a geometric point -/

section ChartPoints

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 05VN read on an étale scheme chart.**  A point of an étale scheme chart of `X`
above the image of a geometric point `x̄` is the point under a lift of `x̄` itself to that
chart. -/
theorem exists_chartLift_of_chartPoint (hX : IsAlgebraicSpace B S hS X)
    (xbar : GeometricPoint B S hS X) (U : SmallEtale B S hS X) (u : chartScheme U)
    (hu : ChartPoint B S hS U.obj.left U.obj.hom u xbar.image) :
    ∃ (q : xbar.val.siteObject ⟶ U.obj.left)
      (_ : U.obj.hom.app (Opposite.op xbar.val.siteObject) q = xbar.val.value),
      ((BigFppfOver.toScheme B S hS).map q)
        (IsLocalRing.closedPoint xbar.val.carrier) = u := by
  obtain ⟨p, hpu, hpx⟩ := hu
  obtain ⟨ubar, hlies, hmap⟩ := exists_geometricPoint_lift_of_isEtale B S hS
    (isAlgebraicSpace_yoneda B S hS U.obj.left) hX U.obj.hom
    ((isEtale_iff_presheaf_of_yoneda B S hS U.obj.hom).mpr U.property) xbar
    (p.class B S hS (yoneda.obj U.obj.left)) hpx
  have hsite : Opposite.op ubar.val.siteObject = Opposite.op xbar.val.siteObject :=
    congrArg Opposite.op
      (congrArg (fun w : FieldValuedPoint B S hS X => w.siteObject) hmap)
  have hvalue : hsite ▸ U.obj.hom.app (Opposite.op ubar.val.siteObject) ubar.val.value =
      xbar.val.value :=
    fieldValuedPoint_map_value_eq B S hS U.obj.hom ubar.val xbar.val hsite hmap
  refine ⟨(yoneda.obj U.obj.left).map (eqToHom hsite) ubar.val.value, ?_, ?_⟩
  · calc U.obj.hom.app (Opposite.op xbar.val.siteObject)
            ((yoneda.obj U.obj.left).map (eqToHom hsite) ubar.val.value) =
          X.map (eqToHom hsite)
            (U.obj.hom.app (Opposite.op ubar.val.siteObject) ubar.val.value) := by
            simpa only [types_comp_apply] using
              congrArg (fun k => k ubar.val.value) (U.obj.hom.naturality (eqToHom hsite))
      _ = xbar.val.value := (map_eqToHom_eq_cast hsite _).trans hvalue
  · refine Eq.trans ?_ ((congrArg (pointsToScheme B S hS U.obj.left) hlies).trans hpu)
    change ((BigFppfOver.toScheme B S hS).map
        ((eqToHom hsite).unop ≫ ubar.val.value))
        (IsLocalRing.closedPoint xbar.val.carrier) = _
    rw [Functor.map_comp]
    have ht : ((BigFppfOver.toScheme B S hS).map (eqToHom hsite).unop)
        (IsLocalRing.closedPoint xbar.val.carrier) =
        IsLocalRing.closedPoint ubar.val.carrier := by
      change (_ : Spec (.of ubar.val.carrier)) = _
      exact Subsingleton.elim _ _
    change ((BigFppfOver.toScheme B S hS).map ubar.val.value)
      (((BigFppfOver.toScheme B S hS).map (eqToHom hsite).unop)
        (IsLocalRing.closedPoint xbar.val.carrier)) = _
    exact congrArg ((BigFppfOver.toScheme B S hS).map ubar.val.value) ht

/-- The point of a chart under the chosen lift of a geometric point is a point of the chart
above the image point. -/
theorem chartPoint_isChartPoint (xbar : GeometricPoint B S hS X)
    (N : SmallEtaleNeighborhood xbar) :
    ChartPoint B S hS N.chart.obj.left N.chart.obj.hom (chartPoint B S hS X N) xbar.image := by
  let p : FieldValuedPoint B S hS (yoneda.obj N.chart.obj.left) :=
    { carrier := xbar.val.carrier
      contained := xbar.val.contained
      toBase := xbar.val.toBase
      value := N.point }
  refine ⟨p, rfl, ?_⟩
  refine Eq.trans (pointsMap_class B S hS (yoneda.obj N.chart.obj.left) N.chart.obj.hom p) ?_
  refine Quot.sound
    ⟨FieldValuedPoint.map B S hS (yoneda.obj N.chart.obj.left) N.chart.obj.hom p,
      FieldValuedPoint.dominates_refl B S hS X _, ⟨𝟙 _, ?_⟩⟩
  change (X.map (𝟙 (Opposite.op (FieldValuedPoint.siteObject B S hS X xbar.val)))) _ = _
  rw [X.map_id]
  exact N.point_comp.symm

end ChartPoints

/-! ### Stacks 05VU -/

/-- **Stacks 05VU.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `F` be a
quasi-coherent `𝒪_X`-module and let `x̄` be a geometric point of `X`.  The following are
equivalent:

1. there is a commuting square of étale scheme charts `U ⟶ V` over `f` and a point `u` of `U`
   above the image of `x̄` in `|X|` at which the restriction of `F` to `U` is flat over `V`;
2. the geometric stalk `F_{x̄}` is flat over the étale local ring `𝒪_{Y, ȳ}`, where
   `ȳ = f ∘ x̄`.

Condition (1) is `AlgebraicGeometry.Space.IsFlatOverAtOnChartDiagram`, the ringed-space
predicate of Stacks 08KT on the square, the condition "above `x`" being
`AlgebraicGeometry.Space.ChartPoint`; condition (2) is
`AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint`.  Condition (2) mentions no chart, so the
equivalence also says that condition (1) does not depend on the chosen square or point. -/
@[stacks 05VU]
theorem isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint
    {Xs Ys : AlgebraicSpaces B S hS} (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [F.IsQuasicoherentOnSite]
    (xbar : GeometricPoint B S hS Xs.1) :
    (∃ (d : ChartDiagram B S hS Xs.1 Ys.1 f.hom) (u : chartScheme d.U),
        ChartPoint B S hS d.U.obj.left d.U.obj.hom u xbar.image ∧
        IsFlatOverAtOnChartDiagram B S hS Xs.2 F d u) ↔
      IsFlatOverAtGeometricPoint B S hS f F xbar := by
  constructor
  · rintro ⟨d, u, hcp, hflat⟩
    obtain ⟨q, hq, hu⟩ := exists_chartLift_of_chartPoint B S hS Xs.2 xbar d.U u hcp
    subst hu
    exact (isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint B S hS f F
      ⟨d.U, q, hq⟩ d.V d.g d.comm).1 hflat
  · intro h
    obtain ⟨V₀, b, hbSurjective, hbEtale⟩ := Ys.2.exists_atlas
    obtain ⟨U₀, a, g, hcomm, haSurjective, haEtale⟩ :=
      exists_surjective_etale_presentation_lift B S hS Xs.2 Ys.2 f.hom V₀ b
        hbSurjective hbEtale
    obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap B S hS Xs.1 Xs.2 U₀ a).mp
      haSurjective xbar.image
    have hcp : ChartPoint B S hS U₀ a (pointsToScheme B S hS U₀ z) xbar.image :=
      hz ▸ chartPoint_pointsToScheme B S hS U₀ a z
    let Uc : SmallEtale B S hS Xs.1 := ⟨CostructuredArrow.mk a, haEtale⟩
    let Vc : SmallEtale B S hS Ys.1 := ⟨CostructuredArrow.mk b, hbEtale⟩
    obtain ⟨q, hq, -⟩ := exists_chartLift_of_chartPoint B S hS Xs.2 xbar Uc _ hcp
    let N : SmallEtaleNeighborhood xbar := ⟨Uc, q, hq⟩
    exact ⟨{ U := Uc, V := Vc, g := g, comm := hcomm },
      chartPoint B S hS Xs.1 N, chartPoint_isChartPoint B S hS xbar N,
      (isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint B S hS f F
        N Vc g hcomm).2 h⟩

end AlgebraicGeometry.Space

end
