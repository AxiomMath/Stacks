module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.AffineChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.AffineChartsAlongLimit
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackVanishing
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent

/-!
# The zero condition after base change is limit preserving on affine schemes

Let `u : F ⟶ G` be a homomorphism of quasi-coherent modules on a scheme `X` over `S`, with `F`
of finite type and `X ⟶ S` quasi-compact. If an inverse system of affine schemes over `S`,
indexed by a cofiltered category, has limit `T`, and if `u` becomes zero after base change to
`T`, then it already becomes zero after base change to one of the stages. Equivalently, the
subterminal functor recording the vanishing of the base change takes the limit of such a system
to the colimit of its values.

## Main definitions

* `AlgebraicGeometry.chartStageMap` and `AlgebraicGeometry.chartLimitMap`, with their
  ring-theoretic shadows `AlgebraicGeometry.chartStageRingMap` and
  `AlgebraicGeometry.chartLimitRingMap`: the morphisms to an affine open of the target from the
  inverse images, at the stages and on the limit, of an open of a stage lying over it.

## Main results

* `Stacks.Flatness.ModuleMapBaseChangeSituation.exists_isZeroAfterBaseChange_of_isColimit`: if
  the base change of the homomorphism to the limit of such a system vanishes, its base change to
  one of the stages already vanishes.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.zeroFunctor_preservesColimit_of_isAffine`:
  preservation of the filtered colimit attached to a cofiltered inverse system of affine schemes
  over the base.
* `AlgebraicGeometry.isPullback_overPullback_map_left`: the morphism of base changes induced by a
  morphism over the base is itself a base change, hence affine between affine stages.

## Implementation notes

The index category lives in the universe of the schemes: with an index in a strictly larger
universe and no smallness hypothesis the statement is false. The inverse system
`Stacks.AlgebraicGeometry.SmallnessNecessary.system` of spectra of fields indexed by `Ordinal`
has every stage a nonempty affine scheme over a field and empty limit, so that the base change
of any homomorphism to the limit vanishes while the base change to no stage need.

The argument is local on `X ×_S T` for a *finite* affine cover subordinate to the projection to
`X`, which exists because that projection is quasi-compact. On such a chart both sides of the
statement become commutative algebra: the chart is the spectrum of a ring, the inverse images of
the chart at the later stages form an inverse system of affine schemes whose rings of global
sections form a filtered colimit, and vanishing of the inverse image of the homomorphism is
vanishing of an extension of scalars of a map of finite modules. Descent of that vanishing to a
stage is `Stacks.FinitePresentation.ColimitDescent.exists_baseChange_eq_of_isColimit`, Tag
05LI(1). The finitely many charts are brought to a common stage because the category of objects
over a stage of a cofiltered category is again cofiltered.

The inclusion of the inverse image of the chart into the stage is given a name of its own,
`AlgebraicGeometry.chartOpensι`, rather than being written as `Scheme.Opens.ι` of that inverse
image. The two are definitionally equal, but only the former has
`(AlgebraicGeometry.opensDiagram E i U).obj k` for its source, so that composites with the
transition morphisms of the diagram stay syntactically well typed.

## References

* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The morphism of base changes induced by a morphism over the base is a base change of it.**
For `f : X ⟶ S` and a morphism `g` of schemes over `S`, the induced morphism of the base changes
along `f` sits in a cartesian square over `g`. -/
theorem isPullback_overPullback_map_left {S X : Scheme.{u}} (f : X ⟶ S) {A B : Over S}
    (g : A ⟶ B) :
    IsPullback ((Over.pullback f).map g).left (pullback.fst A.hom f) (pullback.fst B.hom f)
      g.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd B.hom f) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback B.hom f).flip
  rw [show ((Over.pullback f).map g).left ≫ pullback.snd B.hom f = pullback.snd A.hom f from
    pullback.lift_snd _ _ _, Over.w g]
  exact (IsPullback.of_hasPullback A.hom f).flip

/-- **The morphism of base changes induced by an affine morphism over the base is affine.** -/
instance isAffineHom_overPullback_map_left {S X : Scheme.{u}} (f : X ⟶ S) {A B : Over S}
    (g : A ⟶ B) [IsAffineHom g.left] : IsAffineHom ((Over.pullback f).map g).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_overPullback_map_left f g).flip inferInstance

section AffineChartAlongLimit

variable {I : Type u} [Category.{u} I] (E : I ⥤ Scheme.{u}) (cE : Cone E) (i₀ : I)
  (U : (E.obj i₀).Opens)

/-- The inclusion of the inverse image of an open of a stage into a later stage, as a morphism
out of the value of `AlgebraicGeometry.opensDiagram`. -/
noncomputable def chartOpensι (k : Over i₀) : (opensDiagram E i₀ U).obj k ⟶ E.obj k.left :=
  (E.map k.hom ⁻¹ᵁ U).ι

/-- The inclusion of the inverse image on the limit of an open of a stage, as a morphism out of
the vertex of `AlgebraicGeometry.opensCone`. -/
noncomputable def chartOpensιLimit : (opensCone E cE i₀ U).pt ⟶ cE.pt :=
  (cE.π.app i₀ ⁻¹ᵁ U).ι

lemma chartOpensι_eq (k : Over i₀) : chartOpensι E i₀ U k = (E.map k.hom ⁻¹ᵁ U).ι := rfl

lemma chartOpensιLimit_eq : chartOpensιLimit E cE i₀ U = (cE.π.app i₀ ⁻¹ᵁ U).ι := rfl

lemma opensDiagram_map_comp_chartOpensι {k l : Over i₀} (g : k ⟶ l) :
    (opensDiagram E i₀ U).map g ≫ chartOpensι E i₀ U l =
      chartOpensι E i₀ U k ≫ E.map g.left :=
  Scheme.Hom.resLE_comp_ι _ _

lemma opensCone_π_comp_chartOpensι (k : Over i₀) :
    (opensCone E cE i₀ U).π.app k ≫ chartOpensι E i₀ U k =
      chartOpensιLimit E cE i₀ U ≫ cE.π.app k.left :=
  Scheme.Hom.resLE_comp_ι _ _

variable {X : Scheme.{u}} {p : E.obj i₀ ⟶ X} {W : X.Opens} (hsub : U ≤ p ⁻¹ᵁ W)

include hsub

/-- The inverse image of an open lying over `W` again lies over `W`. -/
lemma preimage_le_preimage_comp_of_le_preimage {Y : Scheme.{u}} (g : Y ⟶ E.obj i₀) :
    g ⁻¹ᵁ U ≤ (g ≫ p) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]; exact fun x hx => hsub hx

/-- **The chart map at a stage.**  The inverse image at a later stage of an open of a stage
lying over an open `W` of the target maps to `W`. -/
noncomputable def chartStageMap (k : Over i₀) :
    (opensDiagram E i₀ U).obj k ⟶ W.toScheme :=
  (E.map k.hom ≫ p).resLE W (E.map k.hom ⁻¹ᵁ U)
    (preimage_le_preimage_comp_of_le_preimage E i₀ U hsub (E.map k.hom))

/-- **The chart map on the limit.** -/
noncomputable def chartLimitMap : (opensCone E cE i₀ U).pt ⟶ W.toScheme :=
  (cE.π.app i₀ ≫ p).resLE W (cE.π.app i₀ ⁻¹ᵁ U)
    (preimage_le_preimage_comp_of_le_preimage E i₀ U hsub (cE.π.app i₀))

lemma chartStageMap_comp_ι (k : Over i₀) :
    chartStageMap E i₀ U hsub k ≫ W.ι = chartOpensι E i₀ U k ≫ E.map k.hom ≫ p :=
  Scheme.Hom.resLE_comp_ι _ _

lemma chartLimitMap_comp_ι :
    chartLimitMap E cE i₀ U hsub ≫ W.ι = chartOpensιLimit E cE i₀ U ≫ cE.π.app i₀ ≫ p :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The chart maps at the stages are compatible with the transition morphisms. -/
lemma opensDiagram_map_comp_chartStageMap {k l : Over i₀} (g : k ⟶ l) :
    (opensDiagram E i₀ U).map g ≫ chartStageMap E i₀ U hsub l = chartStageMap E i₀ U hsub k := by
  rw [← cancel_mono W.ι, Category.assoc, chartStageMap_comp_ι, chartStageMap_comp_ι,
    ← Category.assoc, opensDiagram_map_comp_chartOpensι, Category.assoc,
    ← Category.assoc (E.map g.left), ← E.map_comp, Over.w g]

/-- The chart maps at the stages assemble the chart map on the limit. -/
lemma opensCone_π_comp_chartStageMap (k : Over i₀) :
    (opensCone E cE i₀ U).π.app k ≫ chartStageMap E i₀ U hsub k =
      chartLimitMap E cE i₀ U hsub := by
  rw [← cancel_mono W.ι, Category.assoc, chartStageMap_comp_ι, chartLimitMap_comp_ι,
    ← Category.assoc, opensCone_π_comp_chartOpensι, Category.assoc,
    ← Category.assoc (cE.π.app k.left), cE.w k.hom]

/-- **The ring map from the coordinate ring of the chart to that of its inverse image at a
stage.** -/
noncomputable def chartStageRingMap (k : Over i₀) :
    Γ(X, W) ⟶ Γ((opensDiagram E i₀ U).obj k, ⊤) :=
  W.topIso.inv ≫ (chartStageMap E i₀ U hsub k).appTop

/-- **The ring map from the coordinate ring of the chart to that of its inverse image on the
limit.** -/
noncomputable def chartLimitRingMap : Γ(X, W) ⟶ Γ((opensCone E cE i₀ U).pt, ⊤) :=
  W.topIso.inv ≫ (chartLimitMap E cE i₀ U hsub).appTop

/-- The ring maps of the chart are compatible with the transition morphisms. -/
lemma chartStageRingMap_comp_appTop {k l : Over i₀} (g : k ⟶ l) :
    chartStageRingMap E i₀ U hsub l ≫ ((opensDiagram E i₀ U).map g).appTop =
      chartStageRingMap E i₀ U hsub k := by
  rw [chartStageRingMap, chartStageRingMap, Category.assoc, ← Scheme.Hom.comp_appTop,
    opensDiagram_map_comp_chartStageMap]

/-- The ring maps of the chart assemble the ring map of the chart on the limit. -/
lemma chartStageRingMap_comp_π_appTop (k : Over i₀) :
    chartStageRingMap E i₀ U hsub k ≫ ((opensCone E cE i₀ U).π.app k).appTop =
      chartLimitRingMap E cE i₀ U hsub := by
  rw [chartStageRingMap, chartLimitRingMap, Category.assoc, ← Scheme.Hom.comp_appTop,
    opensCone_π_comp_chartStageMap]

end AffineChartAlongLimit

end AlgebraicGeometry

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

/-- **The vanishing of an inverse image on an affine chart descends to a stage.**  Let `E` be a
cofiltered inverse system of schemes with affine transition morphisms and limit cone `cE`, let
`p` be a morphism from a stage `i₀` to the source of the situation, let `W` be an affine open of
that source and `U` an affine open of the stage lying over `W`. If the inverse image of the
homomorphism of the situation along the chart map on the limit is zero, then it is already zero
along the chart map at some later stage. -/
private theorem exists_stage_chart_pullback_eq_zero (D : ModuleMapBaseChangeSituation.{u})
    [D.F.IsFiniteType] {I : Type u} [Category.{u} I] [IsCofiltered I] (E : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (E.map g)] (cE : Cone E) (hcE : IsLimit cE) (i₀ : I)
    {p : E.obj i₀ ⟶ D.X} {W : D.X.Opens} (hW : IsAffineOpen W) (U : (E.obj i₀).Opens)
    (hU : IsAffineOpen U) (hsub : U ≤ p ⁻¹ᵁ W)
    (h : (Scheme.Modules.pullback (chartLimitMap E cE i₀ U hsub ≫ W.ι)).map D.hom = 0) :
    ∃ k : Over i₀,
      (Scheme.Modules.pullback (chartStageMap E i₀ U hsub k ≫ W.ι)).map D.hom = 0 := by
  classical
  let d : Over i₀ ⥤ Scheme.{u} := opensDiagram E i₀ U
  let dc : Cone d := opensCone E cE i₀ U
  have hdAffine (k : Over i₀) : IsAffine (d.obj k) := hU.preimage (E.map k.hom)
  have hdcAffine : IsAffine dc.pt :=
    have : IsAffineHom (cE.π.app i₀) := isAffineHom_π_app E cE hcE i₀
    hU.preimage (cE.π.app i₀)
  let A : CommRingCat.{u} := Γ(D.X, W)
  let eW : (W : Scheme.{u}) ≅ Spec A := hW.isoSpec
  let R : (Over i₀)ᵒᵖ ⥤ CommRingCat.{u} := d.op ⋙ Scheme.Γ
  let cΓ : Cocone R := Scheme.Γ.mapCocone dc.op
  have hcΓ : IsColimit cΓ := isColimitΓMapCoconeOpensConeOp E cE hcE i₀ hU
  let fstage : ∀ k : Over i₀, A ⟶ R.obj (op k) := chartStageRingMap E i₀ U hsub
  let flimit : A ⟶ cΓ.pt := chartLimitRingMap E cE i₀ U hsub
  let _ (k : (Over i₀)ᵒᵖ) : Algebra (A : Type u) (R.obj k : Type u) :=
    (fstage k.unop).hom.toAlgebra
  let _ : Algebra (A : Type u) (cΓ.pt : Type u) := flimit.hom.toAlgebra
  have halgR : ∀ ⦃k l : (Over i₀)ᵒᵖ⦄ (g : k ⟶ l) (a : A),
      (R.map g).hom (algebraMap A (R.obj k) a) = algebraMap A (R.obj l) a := fun _ l g a =>
    congrArg (fun z : A ⟶ R.obj l => z.hom a)
      (chartStageRingMap_comp_appTop E i₀ U hsub g.unop)
  have halgι : ∀ (k : (Over i₀)ᵒᵖ) (a : A),
      (cΓ.ι.app k).hom (algebraMap A (R.obj k) a) = algebraMap A cΓ.pt a := fun k a =>
    congrArg (fun z : A ⟶ cΓ.pt => z.hom a)
      (chartStageRingMap_comp_π_appTop E cE i₀ U hsub k.unop)
  have hfin : Module.Finite (A : Type u)
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.F)) :=
    D.module_finite_moduleSpecΓ_chart W A eW
  have hgLim : dc.pt.isoSpec.inv ≫ chartLimitMap E cE i₀ U hsub ≫ W.ι =
      Spec.map flimit ≫ D.chartInclusion W A eW := by
    rw [← Category.assoc, hW.isoSpec_inv_comp (chartLimitMap E cE i₀ U hsub), Category.assoc]
    rfl
  have hbaseLim :
      LinearMap.baseChange (cΓ.pt : Type u)
        (moduleSpecΓFunctor.map (D.chartHom W A eW)).hom = 0 :=
    (D.pullback_eq_zero_iff_of_factorsThrough_chart W A cΓ.pt eW flimit hgLim).2
      (Scheme.Modules.pullback_map_eq_zero_of_comp _ _ D.hom h)
  obtain ⟨k, hk⟩ := Stacks.FinitePresentation.ColimitDescent.exists_baseChange_eq_of_isColimit
    R cΓ halgR halgι (isColimitOfPreserves (forget CommRingCat) hcΓ)
    (moduleSpecΓFunctor.map (D.chartHom W A eW)).hom 0 (by simpa using hbaseLim)
  refine ⟨k.unop, ?_⟩
  have hkzero : LinearMap.baseChange (R.obj k : Type u)
      (moduleSpecΓFunctor.map (D.chartHom W A eW)).hom = 0 :=
    hk.trans LinearMap.baseChange_zero
  have hgStage : (d.obj k.unop).isoSpec.inv ≫ chartStageMap E i₀ U hsub k.unop ≫ W.ι =
      Spec.map (fstage k.unop) ≫ D.chartInclusion W A eW := by
    rw [← Category.assoc, hW.isoSpec_inv_comp (chartStageMap E i₀ U hsub k.unop),
      Category.assoc]
    rfl
  exact (Scheme.Modules.pullback_map_eq_zero_iff_of_isIso (d.obj k.unop).isoSpec.inv _).1
    ((Scheme.Modules.pullback_comp_map_eq_zero_iff _ _ D.hom).1
      ((D.pullback_eq_zero_iff_of_factorsThrough_chart W A (R.obj k) eW (fstage k.unop)
        hgStage).1 hkzero))

/-- **The zero condition after base change descends to a stage.**  If an inverse system of
affine schemes over the base, indexed by a cofiltered category in the universe of the schemes,
has limit `T` and the homomorphism of the situation becomes zero after base change to `T`, then
it already becomes zero after base change to one of the stages. -/
theorem exists_isZeroAfterBaseChange_of_isColimit (D : ModuleMapBaseChangeSituation.{u})
    [QuasiCompact D.f] [D.F.IsFiniteType] {I : Type u} [Category.{u} I] [IsCofiltered I]
    (T : I ⥤ Over D.S) (hT : ∀ i, IsAffine (T.obj i).left) (c : Cocone T.op)
    (hc : IsColimit c) (h : D.IsZeroAfterBaseChange c.pt.unop) :
    ∃ i, D.IsZeroAfterBaseChange (T.obj i) := by
  classical
  let K : Over D.S ⥤ Scheme.{u} := Over.pullback D.f ⋙ Over.forget D.X
  let E : I ⥤ Scheme.{u} := T ⋙ K
  let cE : Cone E := K.mapCone c.unop
  have hcE : IsLimit cE := isLimitOfPreserves K hc.unop
  have haff {i j : I} (g : i ⟶ j) : IsAffineHom (E.map g) := by
    have := hT i
    have := hT j
    exact isAffineHom_overPullback_map_left D.f (T.map g)
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  let p : E.obj i₀ ⟶ D.X := ((Over.pullback D.f).obj (T.obj i₀)).hom
  have hstruct {i j : I} (g : i ⟶ j) :
      E.map g ≫ ((Over.pullback D.f).obj (T.obj j)).hom =
        ((Over.pullback D.f).obj (T.obj i)).hom := Over.w ((Over.pullback D.f).map (T.map g))
  have hlimstruct (i : I) :
      cE.π.app i ≫ ((Over.pullback D.f).obj (T.obj i)).hom =
        ((Over.pullback D.f).obj c.pt.unop).hom :=
    Over.w ((Over.pullback D.f).map (c.unop.π.app i))
  have : IsAffine (T.obj i₀).left := hT i₀
  have : CompactSpace (E.obj i₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (T.obj i₀).hom D.f)
  obtain ⟨n, W, U, hW, hU, hcover, hsub⟩ := exists_finite_affineOpenCover_subordinate p
  have hlimzero :
      (Scheme.Modules.pullback ((Over.pullback D.f).obj c.pt.unop).hom).map D.hom = 0 := by
    rw [show ((Over.pullback D.f).obj c.pt.unop).hom =
      (pullbackSymmetry c.pt.unop.hom D.f).hom ≫ pullback.fst D.f c.pt.unop.hom from
      (pullbackSymmetry_hom_comp_fst c.pt.unop.hom D.f).symm]
    exact Scheme.Modules.pullback_map_eq_zero_of_comp _ _ D.hom h
  have hchart (j : Fin n) : ∃ k : Over i₀,
      (Scheme.Modules.pullback
        (chartStageMap E i₀ (U j) (hsub j) k ≫ (W j).ι)).map D.hom = 0 := by
    refine exists_stage_chart_pullback_eq_zero D E cE hcE i₀ (hW j) (U j) (hU j) (hsub j) ?_
    rw [chartLimitMap_comp_ι, hlimstruct i₀]
    exact Scheme.Modules.pullback_map_eq_zero_of_comp _ _ D.hom hlimzero
  choose chartStage hchartStage using hchart
  obtain ⟨k₀, hk₀⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image chartStage)
  have hzero (j : Fin n) :
      (Scheme.Modules.pullback ((E.map k₀.hom ⁻¹ᵁ U j).ι ≫ E.map k₀.hom ≫ p)).map D.hom = 0 := by
    obtain ⟨g⟩ := hk₀ (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩)
    have hstage : (Scheme.Modules.pullback
        (chartStageMap E i₀ (U j) (hsub j) k₀ ≫ (W j).ι)).map D.hom = 0 := by
      rw [← opensDiagram_map_comp_chartStageMap E i₀ (U j) (hsub j) g, Category.assoc]
      exact Scheme.Modules.pullback_map_eq_zero_of_comp _ _ D.hom (hchartStage j)
    rwa [chartStageMap_comp_ι, chartOpensι_eq] at hstage
  have hwhole : (Scheme.Modules.pullback (E.map k₀.hom ≫ p)).map D.hom = 0 := by
    exact Scheme.Modules.hom_eq_zero_of_pullback_ι_map_eq_zero _
      (Scheme.Hom.iSup_preimage_eq_top (E.map k₀.hom) hcover) _ fun j =>
        (Scheme.Modules.pullback_comp_map_eq_zero_iff _ _ D.hom).1 (hzero j)
  refine ⟨k₀.left, ?_⟩
  rw [show E.map k₀.hom ≫ p = ((Over.pullback D.f).obj (T.obj k₀.left)).hom from
    hstruct k₀.hom, show ((Over.pullback D.f).obj (T.obj k₀.left)).hom =
      (pullbackSymmetry (T.obj k₀.left).hom D.f).hom ≫
        pullback.fst D.f (T.obj k₀.left).hom from
      (pullbackSymmetry_hom_comp_fst (T.obj k₀.left).hom D.f).symm] at hwhole
  exact (Scheme.Modules.pullback_map_eq_zero_iff_of_isIso
    (pullbackSymmetry (T.obj k₀.left).hom D.f).hom _).1
    ((Scheme.Modules.pullback_comp_map_eq_zero_iff _ _ D.hom).1 hwhole)

/-- **Stacks Project, Tag 05MJ.**  The zero functor of a homomorphism of quasi-coherent modules
with source of finite type, along a quasi-compact morphism, preserves the filtered colimit
attached to a cofiltered inverse system of affine schemes over the base. -/
@[stacks 05MJ "zero_limit"]
theorem zeroFunctor_preservesColimit_of_isAffine (D : ModuleMapBaseChangeSituation.{u})
    [QuasiCompact D.f] [D.F.IsFiniteType] (I : Type u) [Category.{u} I] [IsCofiltered I]
    (T : I ⥤ Over D.S) (hT : ∀ i, IsAffine (T.obj i).left) :
    PreservesColimit T.op D.zeroFunctor := by
  classical
  refine ⟨fun {c} hc => ⟨Types.FilteredColimit.isColimitOf (T.op ⋙ D.zeroFunctor)
    (D.zeroFunctor.mapCocone c) (fun x => ?_) fun j k x y _ => ?_⟩⟩
  · obtain ⟨i, hi⟩ := exists_isZeroAfterBaseChange_of_isColimit D T hT c hc x.down
    exact ⟨op i, ⟨hi⟩,
      (show Subsingleton (PLift (D.IsZeroAfterBaseChange c.pt.unop)) from inferInstance).elim _ _⟩
  · obtain ⟨l, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs j k
    exact ⟨l, f, g, (show Subsingleton (PLift (D.IsZeroAfterBaseChange (T.obj l.unop))) from
      inferInstance).elim _ _⟩

end Stacks.Flatness.ModuleMapBaseChangeSituation

end
