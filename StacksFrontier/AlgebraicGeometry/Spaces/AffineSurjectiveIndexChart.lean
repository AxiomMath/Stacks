module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction

/-!
# Affine surjective charts above a base-changed chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `V` be an étale scheme chart of `Y`. The étale scheme charts of `X` above the
algebraic space `X ×_Y V` of Stacks 03G2, part (4), are the objects of the index category
`StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op` which
computes the sections over `V` of a direct image along `f`. This file produces index objects
whose underlying scheme is affine and which are surjective onto `X ×_Y V`: over a single affine
chart `V` of a quasi-compact `f`, by Stacks 03H6, and by base change of such an index object over
`U` along a morphism `m : V ⟶ U` of affine charts of `Y`, forming the fibre product of its chart
with `V` over `U`.

## Main definitions

* `AlgebraicGeometry.Space.pullbackIndexChart` is the étale scheme chart of `X` underlying the
  fibre product of the chart of an index object over `U` with a chart `V` of `Y` over `U`;
  `AlgebraicGeometry.Space.pullbackIndexChartHom` is its projection to the given chart and
  `AlgebraicGeometry.Space.pullbackChartDiagram` is the chart diagram of Stacks 03G3 which,
  through `AlgebraicGeometry.Space.pullbackIndex`, presents it as an index object over `V`.

## Main results

* `AlgebraicGeometry.Space.isPullback_chartLift_of_isPullback`: a cartesian square of Yoneda
  presheaves over a morphism of charts of `Y` stays cartesian after passage to the charts of `X`
  above the two base-changed charts.
* `AlgebraicGeometry.Space.exists_isAffine_isSurjective_index`: for a quasi-compact `f` and an
  affine chart `V` of `Y` there is an index object over `V` whose chart is affine and which is
  surjective onto `X ×_Y V`.
* `AlgebraicGeometry.Space.exists_isAffine_isSurjective_index_pullback`: such an index object
  over `U` base changes along `m : V ⟶ U` to one over `V`, together with the cartesian square
  of schemes identifying its chart as the fibre product of the old one with `V` over `U`.

## References

* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-! ### An affine surjective chart over an affine chart of the target -/

/-- **Stacks 03H6 in the index category of Stacks 03G4.** For a quasi-compact morphism `f` and
an affine étale scheme chart `V` of `Y` there is an étale scheme chart of `X` above `X ×_Y V`
whose underlying scheme is affine and whose morphism to `X ×_Y V` is surjective on points. -/
theorem exists_isAffine_isSurjective_index (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))
    (hf : IsQuasiCompact B S hS f.hom) :
    ∃ j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op,
      IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj j.right.unop))
        ∧ IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map j.hom.unop).hom := by
  obtain ⟨W, p, hWaff, hpsurj, hpEtale⟩ :=
    exists_affine_etale_surjective_chart_chartBaseChange B S hS f V hV hf
  have hbEtale : IsEtale B S hS (p ≫
      (((SpacesEtale.inclusion B S hS X).obj (chartBaseChange B S hS f V)).hom.hom)) :=
    isEtale_comp B S hS hpEtale (chartBaseChange B S hS f V).property
  have hsurj : IsSurjective B S hS p :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS
      ((SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V)).1
      ((SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V)).property W p).1 hpsurj
  refine ⟨StructuredArrow.mk
      (Y := op (⟨CostructuredArrow.mk (p ≫
          (((SpacesEtale.inclusion B S hS X).obj (chartBaseChange B S hS f V)).hom.hom)),
        presheaf_etale_of_isEtale B S hS hbEtale⟩ : SmallEtale B S hS X.1))
      (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk p) rfl)).op, hWaff, ?_⟩
  exact hsurj

/-! ### Base change of an index object along a morphism of charts of the target -/

section Pullback

variable (f : X ⟶ Y) {U : SmallEtale B S hS Y.1}
  (j₀ : StructuredArrow (op (chartBaseChange B S hS f U)) (comparisonFunctor B S hS X).op)

/-- **The cartesian square over `X ×_Y U`.** Let `m : d.V ⟶ U` be a morphism of étale scheme
charts of `Y`, let `j₀` be an étale scheme chart of `X` above `X ×_Y U` and let `d` be a chart
diagram over `d.V` whose chart of `X` lies over that of `j₀` by `ρ`. If the resulting square of
Yoneda presheaves is cartesian, then so is the square of algebraic spaces formed by the index
objects over `d.V` and over `U` and the base-changed charts `X ×_Y d.V` and `X ×_Y U`. -/
theorem isPullback_chartLift_of_isPullback (d : ChartDiagram B S hS X.1 Y.1 f.hom) (m : d.V ⟶ U)
    (ρ : d.U ⟶ j₀.right.unop)
    (hpb : IsPullback (yoneda.map d.g)
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map ρ))
      (yoneda.map ((SmallEtale.toOver B S hS Y.1).map m))
      (yoneda.map (chartBaseChangeMap B S hS f U j₀))) :
    IsPullback
      ((SpacesEtale.toSpaces B S hS X).map (indexOfChartDiagram B S hS f d).hom.unop)
      ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map ρ))
      ((SpacesEtale.toSpaces B S hS X).map
        ((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map m)))
      ((SpacesEtale.toSpaces B S hS X).map j₀.hom.unop) := by
  have hstrU : (SpacesEtale.toSpaces B S hS X).map
        ((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map m)) ≫
      ((spacesBaseChange B S hS f).functor.obj
        ((comparisonFunctor B S hS Y).obj U)).1.hom =
      ((spacesBaseChange B S hS f).functor.obj
        ((comparisonFunctor B S hS Y).obj d.V)).1.hom := Over.w _
  have hstrV : (SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map m) ≫
      ((comparisonFunctor B S hS Y).obj U).1.hom =
      ((comparisonFunctor B S hS Y).obj d.V).1.hom := Over.w _
  have hnat : (SpacesEtale.toSpaces B S hS X).map
        ((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map m)) ≫
      (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj U) =
      (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj d.V) ≫
        (SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map m) :=
    (spacesBaseChange B S hS f).projection.naturality ((comparisonFunctor B S hS Y).map m)
  have hbase : IsPullback
      ((spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj d.V))
      ((SpacesEtale.toSpaces B S hS X).map
        ((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map m)))
      ((SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map m))
      ((spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj U)) := by
    refine IsPullback.of_bot ?_ hnat.symm
      ((spacesBaseChange B S hS f).isPullback ((comparisonFunctor B S hS Y).obj U))
    rw [hstrU, hstrV]
    exact (spacesBaseChange B S hS f).isPullback ((comparisonFunctor B S hS Y).obj d.V)
  have hsq : IsPullback (chartDiagramSpaceMap B S hS f d)
      ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map ρ))
      ((SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map m))
      (chartDiagramSpaceMap B S hS f (chartDiagramOfIndex B S hS f U j₀)) := by
    refine IsPullback.of_map_of_faithful (ObjectProperty.ι _) ?_
    show IsPullback (yoneda.map d.g)
      ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map ρ)).hom
      ((SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map m)).hom
      (yoneda.map (chartBaseChangeMap B S hS f U j₀))
    simp only [toSpaces_comparisonFunctor_map_hom]
    exact hpb
  have hT : (SpacesEtale.toSpaces B S hS X).map (indexOfChartDiagram B S hS f d).hom.unop ≫
      (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj d.V) =
      chartDiagramSpaceMap B S hS f d := chartLift_projection B S hS f d
  have hG : (SpacesEtale.toSpaces B S hS X).map j₀.hom.unop ≫
      (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj U) =
      chartDiagramSpaceMap B S hS f (chartDiagramOfIndex B S hS f U j₀) :=
    ObjectProperty.hom_ext _ (yoneda_map_chartBaseChangeMap B S hS f U j₀).symm
  have hTover : (SpacesEtale.toSpaces B S hS X).map
        (indexOfChartDiagram B S hS f d).hom.unop ≫
      ((spacesBaseChange B S hS f).functor.obj
        ((comparisonFunctor B S hS Y).obj d.V)).1.hom =
      ((comparisonFunctor B S hS X).obj d.U).1.hom := Over.w _
  have hGover : (SpacesEtale.toSpaces B S hS X).map j₀.hom.unop ≫
      ((spacesBaseChange B S hS f).functor.obj
        ((comparisonFunctor B S hS Y).obj U)).1.hom =
      ((comparisonFunctor B S hS X).obj j₀.right.unop).1.hom := Over.w _
  have hRover : (SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map ρ) ≫
      ((comparisonFunctor B S hS X).obj j₀.right.unop).1.hom =
      ((comparisonFunctor B S hS X).obj d.U).1.hom := Over.w _
  have hp : (SpacesEtale.toSpaces B S hS X).map (indexOfChartDiagram B S hS f d).hom.unop ≫
      (SpacesEtale.toSpaces B S hS X).map
        ((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map m)) =
      (SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map ρ) ≫
        (SpacesEtale.toSpaces B S hS X).map j₀.hom.unop := by
    refine ((spacesBaseChange B S hS f).isPullback
      ((comparisonFunctor B S hS Y).obj U)).hom_ext ?_ ?_
    · rw [Category.assoc, hnat, ← Category.assoc, hT]
      refine hsq.w.trans ?_
      exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hG)).symm
    · rw [Category.assoc, hstrU, hTover]
      exact (((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hGover)).trans hRover).symm
  refine IsPullback.of_right ?_ hp hbase
  rwa [hT, hG]

variable {V : SmallEtale B S hS Y.1} (m : V ⟶ U)

/-- The underlying morphism of schemes of a morphism of étale scheme charts of `Y` is étale,
by part (2) of Stacks 03EC. -/
theorem etale_toOver_map_of_smallEtale :
    Etale ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y.1).map m)) :=
  etale_of_comp_etale_chart B S hS V.property U.property (CostructuredArrow.w m.hom)

/-- The cartesian square of schemes exhibiting the fibre product of the chart of an index
object over `U` with a chart `V` of `Y` over `U`. -/
theorem isPullback_pullbackIndexChart :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (chartBaseChangeMap B S hS f U j₀)
          ((SmallEtale.toOver B S hS Y.1).map m)))
      ((BigFppfOver.toScheme B S hS).map
        (pullback.fst (chartBaseChangeMap B S hS f U j₀)
          ((SmallEtale.toOver B S hS Y.1).map m)))
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y.1).map m))
      ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS f U j₀)) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  exact ((IsPullback.of_hasPullback (chartBaseChangeMap B S hS f U j₀)
    ((SmallEtale.toOver B S hS Y.1).map m)).map (BigFppfOver.toScheme B S hS)).flip

/-- The projection of the fibre product to the chart of the given index object is étale. -/
theorem etale_pullback_fst_chartBaseChangeMap :
    Etale ((BigFppfOver.toScheme B S hS).map
      (pullback.fst (chartBaseChangeMap B S hS f U j₀)
        ((SmallEtale.toOver B S hS Y.1).map m))) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_pullbackIndexChart B S hS f j₀ m)
    (etale_toOver_map_of_smallEtale B S hS m)

/-- The étale scheme chart of `X` underlying the fibre product of the chart of an index object
over `U` with a chart `V` of `Y` over `U`. -/
noncomputable def pullbackIndexChart : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk (yoneda.map (pullback.fst (chartBaseChangeMap B S hS f U j₀)
      ((SmallEtale.toOver B S hS Y.1).map m)) ≫ j₀.right.unop.1.hom),
    etale_comp_of_scheme B S hS _ _
      (etale_pullback_fst_chartBaseChangeMap B S hS f j₀ m) j₀.right.unop.property⟩

/-- The projection of the fibre product chart to the chart of the given index object, as a
morphism of étale scheme charts of `X`. -/
noncomputable def pullbackIndexChartHom :
    pullbackIndexChart B S hS f j₀ m ⟶ j₀.right.unop :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (pullback.fst (chartBaseChangeMap B S hS f U j₀)
      ((SmallEtale.toOver B S hS Y.1).map m)) rfl)

/-- **Stacks 03G3 for the base-changed chart.** The chart diagram over `V` presenting
`AlgebraicGeometry.Space.pullbackIndexChart` as an étale scheme chart of `X` above
`X ×_Y V`. -/
noncomputable def pullbackChartDiagram : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := pullbackIndexChart B S hS f j₀ m
  V := V
  g := pullback.snd (chartBaseChangeMap B S hS f U j₀)
    ((SmallEtale.toOver B S hS Y.1).map m)
  comm := by
    have hd₀ : j₀.right.unop.1.hom ≫ f.hom =
        yoneda.map (chartBaseChangeMap B S hS f U j₀) ≫ U.1.hom :=
      (chartDiagramOfIndex B S hS f U j₀).comm
    have hmw : yoneda.map ((SmallEtale.toOver B S hS Y.1).map m) ≫ U.1.hom = V.1.hom :=
      CostructuredArrow.w m.hom
    change (yoneda.map (pullback.fst (chartBaseChangeMap B S hS f U j₀)
          ((SmallEtale.toOver B S hS Y.1).map m)) ≫ j₀.right.unop.1.hom) ≫ f.hom =
      yoneda.map (pullback.snd (chartBaseChangeMap B S hS f U j₀)
        ((SmallEtale.toOver B S hS Y.1).map m)) ≫ V.1.hom
    rw [Category.assoc, hd₀, ← hmw, ← Category.assoc, ← Functor.map_comp, ← Category.assoc,
      ← Functor.map_comp, pullback.condition]

/-- The base change along `m : V ⟶ U` of an étale scheme chart of `X` above `X ×_Y U`: the
étale scheme chart of `X` above `X ×_Y V` carried by
`AlgebraicGeometry.Space.pullbackChartDiagram`. -/
noncomputable def pullbackIndex :
    StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op :=
  indexOfChartDiagram B S hS f (pullbackChartDiagram B S hS f j₀ m)

/-- The chartwise morphism of the base-changed index object is the second projection of the
fibre product. -/
theorem chartBaseChangeMap_pullbackIndex :
    chartBaseChangeMap B S hS f V (pullbackIndex B S hS f j₀ m) =
      pullback.snd (chartBaseChangeMap B S hS f U j₀)
        ((SmallEtale.toOver B S hS Y.1).map m) :=
  chartBaseChangeMap_indexOfChartDiagram B S hS f (pullbackChartDiagram B S hS f j₀ m)

end Pullback

/-- **The base change of an affine surjective index object along a morphism of charts of the
target.** Let `m : V ⟶ U` be a morphism of affine étale scheme charts of `Y` and let `j₀` be an
étale scheme chart of `X` above `X ×_Y U` whose underlying scheme is affine and which is
surjective onto `X ×_Y U`. Then the fibre product of the chart of `j₀` with `V` over `U` is an
étale scheme chart of `X` above `X ×_Y V` with the same two properties, and the square of
schemes identifying it as that fibre product is cartesian. -/
theorem exists_isAffine_isSurjective_index_pullback (f : X ⟶ Y) {U V : SmallEtale B S hS Y.1}
    (m : V ⟶ U)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj U)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))
    (j₀ : StructuredArrow (op (chartBaseChange B S hS f U)) (comparisonFunctor B S hS X).op)
    (hj₀aff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj j₀.right.unop)))
    (hj₀ : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map j₀.hom.unop).hom) :
    ∃ (j₁ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
      (r : (SmallEtale.toOver B S hS X.1).obj j₁.right.unop ⟶
            (SmallEtale.toOver B S hS X.1).obj j₀.right.unop),
      IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj j₁.right.unop))
        ∧ IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map j₁.hom.unop).hom
        ∧ IsPullback
            ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS f V j₁))
            ((BigFppfOver.toScheme B S hS).map r)
            ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y.1).map m))
            ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS f U j₀)) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS Y.1).obj U)) := hU
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS Y.1).obj V)) := hV
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS X.1).obj j₀.right.unop)) := hj₀aff
  refine ⟨pullbackIndex B S hS f j₀ m,
    pullback.fst (chartBaseChangeMap B S hS f U j₀) ((SmallEtale.toOver B S hS Y.1).map m),
    IsAffine.of_isPullback (isPullback_pullbackIndexChart B S hS f j₀ m), ?_, ?_⟩
  · have hsq := isPullback_chartLift_of_isPullback B S hS f j₀
      (pullbackChartDiagram B S hS f j₀ m) m (pullbackIndexChartHom B S hS f j₀ m)
      (((IsPullback.of_hasPullback (chartBaseChangeMap B S hS f U j₀)
        ((SmallEtale.toOver B S hS Y.1).map m)).map yoneda).flip)
    exact isSurjective_of_isPullback B S hS hsq.flip hj₀
  · rw [chartBaseChangeMap_pullbackIndex B S hS f j₀ m]
    exact isPullback_pullbackIndexChart B S hS f j₀ m

end AlgebraicGeometry.Space

end
