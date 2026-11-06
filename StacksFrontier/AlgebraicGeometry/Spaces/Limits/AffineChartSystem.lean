module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# Affine charts of an inverse limit of algebraic spaces at a stage

Let `D` be a cofiltered inverse system of presheaves on the big fppf site of a scheme `S`
whose transition morphisms are affine, let `i₀` be a stage, and let
`f₀ : yoneda U₀ ⟶ D i₀` be a scheme-valued point of that stage whose source is affine. Base
changing the stages above `i₀` along `f₀` gives an inverse system indexed by the slice
`Over i₀`, and affineness of the transition morphisms says that every member of that system
is represented by an *affine* object of the site. The system of representing objects is an
`AlgebraicGeometry.Space.AffineChartSystem`, and when the index category is small enough for
the site it has a limit in the site whose underlying scheme is affine and which represents
the base change of the limit projection `limit.π D i₀` along `f₀`; that limiting data is an
`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge`.

## Main definitions

* `AlgebraicGeometry.Space.stageBaseChangeDiagram`: the inverse system of base changes along
  `f₀` of the stages above `i₀`, with projections
  `AlgebraicGeometry.Space.stageBaseChangeFst` and `.stageBaseChangeSnd`.
* `AlgebraicGeometry.Space.AffineChartSystem`: a system of affine objects of the site
  representing that diagram, with `AlgebraicGeometry.Space.affineChartSystem` producing one
  from affineness of the transition morphisms.
* `AlgebraicGeometry.Space.AffineChartSystem.stageMap` and `.baseMap`: the two projections of
  a chart, to its own stage and to `U₀`.
* `AlgebraicGeometry.Space.AffineChartSystem.LimitBridge`: a limit of the chart system in the
  site, together with the identification of the presheaf it represents with the base change
  of `limit.π D i₀` along `f₀`, and `AlgebraicGeometry.Space.AffineChartSystem.limitBridge`
  producing one; `.limitBridgeOfLimitInSite`, `.limitBridgeOfIsSiteSmall`, `.limitBridgeOfMono`,
  `.limitBridgeOfBaseChangeSizeBounded` and `.limitBridgeOfBounded` produce one under other
  hypotheses.
* `AlgebraicGeometry.Space.AffineChartSystem.ChartLimit`: the same data without the statement
  that the underlying schemes form a limit, with
  `AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.toChartLimit` forgetting that statement.

## Main results

* `AlgebraicGeometry.Space.AffineChartSystem.isPullback`: each chart is the fibre product of
  its stage with `U₀` over `D i₀`.
* `AlgebraicGeometry.Space.AffineChartSystem.isAffine_obj` and `.isAffineHom_map`: the chart
  system is a system of affine schemes with affine transition morphisms.
* `AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.isPullback` and `.isPullback_stage`:
  the limit of the chart system is the fibre product of `limit D` with `U₀` over the stage
  `i₀`, and also over each later stage through the corresponding chart.
* `AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.isAffine_pt`: the underlying scheme
  of the limit is affine.

## Implementation notes

The two projections of a base change, and the two projections of the canonical cone on it,
are given names of their own rather than being written as `pullback.fst`/`pullback.snd`: the
vertices are chosen pullbacks definitionally but not syntactically, and rewrites against
composites of the unnamed forms need unfolding.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Diagram

variable {I : Type u} [Category.{u} I] (i₀ : I)
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (U₀ : BigAffineFppf B S hS)
  (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)

/-- The inverse system, indexed by the stages above `i₀`, of the base changes along `f₀` of
those stages. Its limit is the base change of `limit.π D i₀` along `f₀`. -/
noncomputable abbrev stageBaseChangeDiagram : Over i₀ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Over.post (X := i₀) D ⋙ Over.pullback f₀) ⋙
    Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀))

/-- The projection of a base change to its own stage. -/
noncomputable def stageBaseChangeFst (j : Over i₀) :
    (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).obj j ⟶ D.obj j.left :=
  pullback.fst (D.map j.hom) f₀

/-- The projection of a base change to the chosen scheme-valued point of the stage `i₀`. -/
noncomputable def stageBaseChangeSnd (j : Over i₀) :
    (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).obj j ⟶
      yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) :=
  pullback.snd (D.map j.hom) f₀

/-- A member of the diagram of base changes is the fibre product of its stage with `U₀` over
the stage `i₀`. -/
theorem isPullback_stageBaseChange (j : Over i₀) :
    IsPullback (stageBaseChangeFst B S hS i₀ D U₀ f₀ j)
      (stageBaseChangeSnd B S hS i₀ D U₀ f₀ j) (D.map j.hom) f₀ :=
  IsPullback.of_hasPullback _ _

/-- The transition morphisms of the diagram of base changes are compatible with the projections
to the stages. -/
theorem stageBaseChangeDiagram_map_comp_fst {j k : Over i₀} (g : j ⟶ k) :
    (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map g ≫
        stageBaseChangeFst B S hS i₀ D U₀ f₀ k =
      stageBaseChangeFst B S hS i₀ D U₀ f₀ j ≫ D.map g.left := by
  dsimp [stageBaseChangeFst, Over.pullback, Over.post]
  exact pullback.lift_fst _ _ _

/-- The transition morphisms of the diagram of base changes are compatible with the projections
to the chosen scheme-valued point of the distinguished stage. -/
theorem stageBaseChangeDiagram_map_comp_snd {j k : Over i₀} (g : j ⟶ k) :
    (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map g ≫
        stageBaseChangeSnd B S hS i₀ D U₀ f₀ k =
      stageBaseChangeSnd B S hS i₀ D U₀ f₀ j := by
  dsimp [stageBaseChangeSnd, Over.pullback, Over.post]
  exact pullback.lift_snd _ _ _

/-- The embedding of the big affine site of `S` into presheaves. -/
abbrev affineYoneda : BigAffineFppf B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  BigAffineFppf.inclusion B S hS ⋙ yoneda

/-- A system of affine charts for the inverse system `D` at the stage `i₀` and the affine
scheme-valued point `f₀`: a diagram of affine objects of the big fppf site of `S`, indexed by
the stages above `i₀`, representing the base changes of those stages along `f₀`. -/
structure AffineChartSystem where
  /-- The diagram of affine objects of the site. -/
  diagram : Over i₀ ⥤ BigAffineFppf B S hS
  /-- Its image in presheaves is the diagram of base changes along `f₀`. -/
  iso : diagram ⋙ affineYoneda B S hS ≅ stageBaseChangeDiagram B S hS i₀ D U₀ f₀

/-- **Stacks 03WF.** Affineness of the transition morphisms of `D` provides a system of
affine charts at every stage and every affine scheme-valued point of it: each base change
`D k ×_{D i₀} U₀` is represented by an affine object of the site, and the system of
representing objects is obtained by lifting through the Yoneda embedding. -/
noncomputable def affineChartSystem
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    AffineChartSystem B S hS i₀ D U₀ f₀ :=
  have hess : ∀ k : Over i₀, (affineYoneda B S hS).essImage
      ((stageBaseChangeDiagram B S hS i₀ D U₀ f₀).obj k) := fun k ↦
    let ⟨A, _, _, hpb⟩ := hAffine k.hom U₀ f₀
    ⟨A, ⟨hpb.isoPullback⟩⟩
  ⟨Functor.essImage.liftFunctor _ (affineYoneda B S hS) hess,
    Functor.essImage.liftFunctorCompIso _ (affineYoneda B S hS) hess⟩

namespace AffineChartSystem

variable {B S hS i₀ D U₀ f₀} (C : AffineChartSystem B S hS i₀ D U₀ f₀)

/-- The diagram of objects of the big fppf site of `S` underlying a chart system. -/
abbrev siteDiagram : Over i₀ ⥤ BigFppfOver B S hS :=
  C.diagram ⋙ BigAffineFppf.inclusion B S hS

/-- The diagram of schemes underlying a chart system. -/
abbrev schemeDiagram : Over i₀ ⥤ Scheme.{u} :=
  C.siteDiagram ⋙ BigFppfOver.toScheme B S hS

/-- Every chart is affine as a scheme. -/
theorem isAffine_obj (j : Over i₀) : IsAffine (C.schemeDiagram.obj j) :=
  (C.diagram.obj j).property

/-- Every transition morphism of the chart system is an affine morphism of schemes: both its
source and its target are affine. -/
theorem isAffineHom_map {j k : Over i₀} (g : j ⟶ k) :
    _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) :=
  have := C.isAffine_obj j
  have := C.isAffine_obj k
  isAffineHom_of_isAffine _

/-- The projection of a chart to its own stage of `D`. -/
noncomputable def stageMap (j : Over i₀) :
    (C.siteDiagram ⋙ yoneda).obj j ⟶ D.obj j.left :=
  C.iso.hom.app j ≫ stageBaseChangeFst B S hS i₀ D U₀ f₀ j

/-- The projection of a chart to the chosen affine scheme-valued point of the stage `i₀`. -/
noncomputable def baseMap (j : Over i₀) :
    (C.siteDiagram ⋙ yoneda).obj j ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) :=
  C.iso.hom.app j ≫ stageBaseChangeSnd B S hS i₀ D U₀ f₀ j

/-- A chart is the fibre product of its own stage with `U₀` over the stage `i₀`. -/
theorem isPullback (j : Over i₀) :
    IsPullback (C.stageMap j) (C.baseMap j) (D.map j.hom) f₀ :=
  (isPullback_stageBaseChange B S hS i₀ D U₀ f₀ j).of_iso' (C.iso.app j) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp [stageMap]) (by simp [baseMap]) (by simp) (by simp)

end AffineChartSystem

end Diagram

/-! ### The limit of a chart system -/

section LimitBridge

variable {I : Type u} [Category.{u} I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

variable (i₀ D U₀ f₀) in
/-- **Stacks 07SF, part (2).** The canonical cone exhibiting the base change of
`limit.π D i₀` along `f₀` as the limit of the base changes of the later stages. -/
noncomputable abbrev stageBaseChangeCone : Cone (stageBaseChangeDiagram B S hS i₀ D U₀ f₀) :=
  (Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀))).mapCone
    ((Over.pullback f₀).mapCone ((limit.cone D).overPost i₀))

variable (i₀ D U₀ f₀) in
/-- The projection of the base change of `limit.π D i₀` along `f₀` to the limit of `D`. -/
noncomputable def stageBaseChangeConeFst :
    (stageBaseChangeCone B S hS i₀ D U₀ f₀).pt ⟶ limit D :=
  pullback.fst (limit.π D i₀) f₀

variable (i₀ D U₀ f₀) in
/-- The projection of the base change of `limit.π D i₀` along `f₀` to `U₀`. -/
noncomputable def stageBaseChangeConeSnd :
    (stageBaseChangeCone B S hS i₀ D U₀ f₀).pt ⟶
      yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) :=
  pullback.snd (limit.π D i₀) f₀

/-- The vertex of the canonical cone is the fibre product of `limit D` with `U₀` over the
stage `i₀`. -/
theorem isPullback_stageBaseChangeCone :
    IsPullback (stageBaseChangeConeFst B S hS i₀ D U₀ f₀)
      (stageBaseChangeConeSnd B S hS i₀ D U₀ f₀) (limit.π D i₀) f₀ :=
  IsPullback.of_hasPullback _ _

/-- Projecting the canonical cone to a stage and then to that stage of `D` is its own
projection to `limit D` followed by the limit projection. -/
theorem stageBaseChangeCone_π_comp_fst (j : Over i₀) :
    (stageBaseChangeCone B S hS i₀ D U₀ f₀).π.app j ≫
        stageBaseChangeFst B S hS i₀ D U₀ f₀ j =
      stageBaseChangeConeFst B S hS i₀ D U₀ f₀ ≫ limit.π D j.left := by
  dsimp [stageBaseChangeFst, stageBaseChangeConeFst, Over.pullback, Over.post, Cone.overPost]
  simp only [Over.homMk_left, pullback.lift_fst]

/-- Projecting the canonical cone to a stage and then to `U₀` is its own projection to
`U₀`. -/
theorem stageBaseChangeCone_π_comp_snd (j : Over i₀) :
    (stageBaseChangeCone B S hS i₀ D U₀ f₀).π.app j ≫
        stageBaseChangeSnd B S hS i₀ D U₀ f₀ j =
      stageBaseChangeConeSnd B S hS i₀ D U₀ f₀ := by
  dsimp [stageBaseChangeSnd, stageBaseChangeConeSnd, Over.pullback, Over.post, Cone.overPost]
  simp only [Over.homMk_left, pullback.lift_snd]

namespace AffineChartSystem

variable {B S hS}

/-- The limit of a chart system, as data: a limit cone in the big fppf site of `S`, the
statement that the underlying schemes form a limit as well, and the identification of the
presheaf represented by the limit with the base change of `limit.π D i₀` along `f₀`. -/
structure LimitBridge (C : AffineChartSystem B S hS i₀ D U₀ f₀) where
  /-- The limit cone in the site. -/
  cone : Cone C.siteDiagram
  /-- It is a limit cone. -/
  isLimit : IsLimit cone
  /-- The underlying schemes form a limit cone too. -/
  schemeIsLimit : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cone)
  /-- The presheaf represented by the limit is the base change of `limit.π D i₀` along
  `f₀`. -/
  iso : yoneda.obj cone.pt ≅ (stageBaseChangeCone B S hS i₀ D U₀ f₀).pt
  /-- The identification is compatible with the projections to the stages. -/
  iso_comp_π : ∀ j : Over i₀,
    iso.hom ≫ (stageBaseChangeCone B S hS i₀ D U₀ f₀).π.app j =
      yoneda.map (cone.π.app j) ≫ C.iso.hom.app j

/-- The diagram of schemes underlying a chart system at a stage with bounded base changes is
bounded below the site's cutoff. -/
theorem diagramBoundedBelow (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hb : HasBoundedBaseChanges B S hS i₀ D) :
    Scheme.DiagramBoundedBelow B.cutoff C.schemeDiagram :=
  let ⟨μ, hμ, hI, hW⟩ := hb U₀ f₀
  ⟨μ, hμ, hI, fun j => hW j _ _ _ (C.isPullback j)⟩

/-- **Stacks 07SF, from a size bound on the charts.** A cofiltered chart system whose diagram of
schemes is bounded below the site's cutoff has a limit in the big fppf site of `S`, whose
underlying scheme is a limit of the underlying schemes of the charts and which represents the
base change of `limit.π D i₀` along `f₀`. -/
noncomputable def limitBridgeOfBounded [IsCofiltered I]
    (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hb : Scheme.DiagramBoundedBelow B.cutoff C.schemeDiagram) :
    LimitBridge C := by
  classical
  have hWaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)) :=
    C.isAffine_obj
  have _ : HasLimit C.siteDiagram :=
    BigFppfOver.hasLimit_of_isAffine_of_bounded C.siteDiagram hWaff hb
  have _ := BigFppfOver.preservesLimit_toScheme_of_bounded C.siteDiagram hWaff hb
  have hyoneda : IsLimit (yoneda.mapCone (limit.cone C.siteDiagram)) :=
    isLimitOfPreserves yoneda (limit.isLimit C.siteDiagram)
  have hpost : IsLimit ((Cone.postcompose C.iso.hom).obj
      (yoneda.mapCone (limit.cone C.siteDiagram))) :=
    (IsLimit.postcomposeHomEquiv C.iso (yoneda.mapCone (limit.cone C.siteDiagram))).symm
      hyoneda
  have hbase : IsLimit (stageBaseChangeCone B S hS i₀ D U₀ f₀) :=
    isLimitPullbackLimitOverPost B S hS D i₀ f₀
  exact
    { cone := limit.cone C.siteDiagram
      isLimit := limit.isLimit C.siteDiagram
      schemeIsLimit :=
        isLimitOfPreserves (BigFppfOver.toScheme B S hS) (limit.isLimit C.siteDiagram)
      iso := hpost.conePointUniqueUpToIso hbase
      iso_comp_π := fun j ↦ hpost.conePointUniqueUpToIso_hom_comp hbase j }

/-- The limit bridge of a cofiltered chart system whose diagram of charts has a limit in the
site which the underlying scheme functor preserves. -/
noncomputable def limitBridgeOfHasLimit [IsCofiltered I]
    (C : AffineChartSystem B S hS i₀ D U₀ f₀) (hlim : HasLimit C.siteDiagram)
    (hpres : PreservesLimit C.siteDiagram (BigFppfOver.toScheme B S hS)) :
    LimitBridge C := by
  classical
  have _ : HasLimit C.siteDiagram := hlim
  have _ := hpres
  have hyoneda : IsLimit (yoneda.mapCone (limit.cone C.siteDiagram)) :=
    isLimitOfPreserves yoneda (limit.isLimit C.siteDiagram)
  have hpost : IsLimit ((Cone.postcompose C.iso.hom).obj
      (yoneda.mapCone (limit.cone C.siteDiagram))) :=
    (IsLimit.postcomposeHomEquiv C.iso (yoneda.mapCone (limit.cone C.siteDiagram))).symm
      hyoneda
  have hbase : IsLimit (stageBaseChangeCone B S hS i₀ D U₀ f₀) :=
    isLimitPullbackLimitOverPost B S hS D i₀ f₀
  exact
    { cone := limit.cone C.siteDiagram
      isLimit := limit.isLimit C.siteDiagram
      schemeIsLimit :=
        isLimitOfPreserves (BigFppfOver.toScheme B S hS) (limit.isLimit C.siteDiagram)
      iso := hpost.conePointUniqueUpToIso hbase
      iso_comp_π := fun j ↦ hpost.conePointUniqueUpToIso_hom_comp hbase j }

/-- **The limit of a chart system.** A chart system indexed by a slice of a sufficiently small
index category has a limit in the big fppf site of `S`, whose underlying scheme is a limit of
the underlying schemes of the charts and which represents the base change of `limit.π D i₀`
along `f₀`. -/
@[stacks 07SF "limit of the affine charts at a stage"]
noncomputable def limitBridge [IsCofiltered I] (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hSize : #I < B.cutoff.ord.cof) (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) :
    LimitBridge C :=
  have hWaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)) :=
    C.isAffine_obj
  have hJ : #(Over i₀) < B.cutoff.ord.cof :=
    mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize i₀
  limitBridgeOfHasLimit C (BigFppfOver.hasLimit_of_isAffine C.siteDiagram hWaff hJ)
    (BigFppfOver.preservesLimit_toScheme C.siteDiagram hWaff hJ)

/-- **The limit of a chart system, with no cofinality hypothesis.** The index category is
only asked to have fewer objects than the site's size cutoff with all its morphism types
bounded by one cardinal below the cutoff, in exchange for the transition morphisms of `D`
being monomorphisms. -/
noncomputable def limitBridgeOfMono [IsCofiltered I]
    (C : AffineChartSystem B S hS i₀ D U₀ f₀) {ν : Cardinal.{u}} (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hMono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f)) :
    LimitBridge C :=
  have hWaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)) :=
    C.isAffine_obj
  have hJ : #(Over i₀) < B.cutoff :=
    mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hSize hν hHomSize i₀
  have hstage : ∀ j, ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)).size ≤
      monoSizeBound B S hS ((BigAffineFppf.inclusion B S hS).obj U₀) := fun j =>
    size_le_monoSizeBound_of_mono B S hS (C.baseMap j)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback (C.isPullback j) (hMono j.hom))
  limitBridgeOfHasLimit C
    (BigFppfOver.hasLimit_of_isAffine_of_size_le C.siteDiagram hWaff hJ
      (monoSizeBound_lt_cutoff B S hS _) hstage)
    (BigFppfOver.preservesLimit_toScheme_of_size_le C.siteDiagram hWaff hJ
      (monoSizeBound_lt_cutoff B S hS _) hstage)

/-- **The limit of a chart system, for a system with uniformly bounded base changes.** The
index category is only asked to have fewer objects than the site's size cutoff with all its
morphism types bounded by one cardinal below the cutoff, in exchange for the base changes of the
stages of `D` along `f₀` being bounded by one cardinal below the cutoff
(`AlgebraicGeometry.Space.BaseChangeSizeBounded`). -/
noncomputable def limitBridgeOfBaseChangeSizeBounded [IsCofiltered I]
    (C : AffineChartSystem B S hS i₀ D U₀ f₀) {ν : Cardinal.{u}} (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hB : BaseChangeSizeBounded B S hS D) :
    LimitBridge C :=
  have hWaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)) :=
    C.isAffine_obj
  have hJ : #(Over i₀) < B.cutoff :=
    mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hSize hν hHomSize i₀
  have hμ := (hB i₀ _ f₀).choose_spec
  limitBridgeOfHasLimit C
    (BigFppfOver.hasLimit_of_isAffine_of_size_le C.siteDiagram hWaff hJ hμ.1
      fun j => hμ.2 j _ (C.stageMap j) (C.baseMap j) (C.isPullback j))
    (BigFppfOver.preservesLimit_toScheme_of_size_le C.siteDiagram hWaff hJ hμ.1
      fun j => hμ.2 j _ (C.stageMap j) (C.baseMap j) (C.isPullback j))

/-- The vertex of the canonical cone, reparametrised by an isomorphism, is the fibre product of
`limit D` with `U₀` over the stage `i₀`. -/
private theorem isPullback_comp_iso_stageBaseChangeCone
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ≅ (stageBaseChangeCone B S hS i₀ D U₀ f₀).pt) :
    IsPullback (e.hom ≫ stageBaseChangeConeFst B S hS i₀ D U₀ f₀)
      (e.hom ≫ stageBaseChangeConeSnd B S hS i₀ D U₀ f₀) (limit.π D i₀) f₀ :=
  (isPullback_stageBaseChangeCone B S hS).of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id])
    (by rw [Iso.refl_hom, Category.comp_id]) (by simp) (by simp)

/-- The projection of a limit of charts to the limit of `D`, then to a stage, factors through
the chart. -/
private theorem comp_iso_fst_comp_limitπ {C : AffineChartSystem B S hS i₀ D U₀ f₀}
    {c : Cone C.siteDiagram} (e : yoneda.obj c.pt ≅ (stageBaseChangeCone B S hS i₀ D U₀ f₀).pt)
    (he : ∀ j : Over i₀, e.hom ≫ (stageBaseChangeCone B S hS i₀ D U₀ f₀).π.app j =
      yoneda.map (c.π.app j) ≫ C.iso.hom.app j) (j : Over i₀) :
    (e.hom ≫ stageBaseChangeConeFst B S hS i₀ D U₀ f₀) ≫ limit.π D j.left =
      yoneda.map (c.π.app j) ≫ C.stageMap j := by
  change (e.hom ≫ stageBaseChangeConeFst B S hS i₀ D U₀ f₀) ≫ limit.π D j.left =
    yoneda.map (c.π.app j) ≫ C.iso.hom.app j ≫ stageBaseChangeFst B S hS i₀ D U₀ f₀ j
  rw [Category.assoc, ← stageBaseChangeCone_π_comp_fst B S hS, ← Category.assoc,
    he j, Category.assoc]

/-- The projection of a limit of charts to a chart, then to `U₀`, is its projection to `U₀`. -/
private theorem comp_baseMap_eq_comp_iso_snd {C : AffineChartSystem B S hS i₀ D U₀ f₀}
    {c : Cone C.siteDiagram} (e : yoneda.obj c.pt ≅ (stageBaseChangeCone B S hS i₀ D U₀ f₀).pt)
    (he : ∀ j : Over i₀, e.hom ≫ (stageBaseChangeCone B S hS i₀ D U₀ f₀).π.app j =
      yoneda.map (c.π.app j) ≫ C.iso.hom.app j) (j : Over i₀) :
    yoneda.map (c.π.app j) ≫ C.baseMap j =
      e.hom ≫ stageBaseChangeConeSnd B S hS i₀ D U₀ f₀ := by
  change yoneda.map (c.π.app j) ≫ C.iso.hom.app j ≫
      stageBaseChangeSnd B S hS i₀ D U₀ f₀ j =
    e.hom ≫ stageBaseChangeConeSnd B S hS i₀ D U₀ f₀
  rw [← Category.assoc, ← he j, Category.assoc, stageBaseChangeCone_π_comp_snd B S hS]

/-- A limit of charts is the fibre product of `limit D` with `U₀` over any one of the later
stages, through the corresponding chart. -/
private theorem isPullback_comp_iso_chart {C : AffineChartSystem B S hS i₀ D U₀ f₀}
    {c : Cone C.siteDiagram} (e : yoneda.obj c.pt ≅ (stageBaseChangeCone B S hS i₀ D U₀ f₀).pt)
    (he : ∀ j : Over i₀, e.hom ≫ (stageBaseChangeCone B S hS i₀ D U₀ f₀).π.app j =
      yoneda.map (c.π.app j) ≫ C.iso.hom.app j) (j : Over i₀) :
    IsPullback (e.hom ≫ stageBaseChangeConeFst B S hS i₀ D U₀ f₀) (yoneda.map (c.π.app j))
      (limit.π D j.left) (C.stageMap j) := by
  refine IsPullback.of_bot (t := C.isPullback j) (p := comp_iso_fst_comp_limitπ e he j) ?_
  simpa only [comp_baseMap_eq_comp_iso_snd e he j, limit.w] using
    isPullback_comp_iso_stageBaseChangeCone e

namespace LimitBridge

variable {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : LimitBridge C)

/-- The projection of the limit of the chart system to the limit of `D`. -/
noncomputable def toLimit : yoneda.obj L.cone.pt ⟶ limit D :=
  L.iso.hom ≫ stageBaseChangeConeFst B S hS i₀ D U₀ f₀

/-- The projection of the limit of the chart system to the chosen affine scheme-valued point
of the stage `i₀`. -/
noncomputable def toBase :
    yoneda.obj L.cone.pt ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) :=
  L.iso.hom ≫ stageBaseChangeConeSnd B S hS i₀ D U₀ f₀

/-- The limit of the chart system is the fibre product of `limit D` with `U₀` over the stage
`i₀`. -/
theorem isPullback : IsPullback L.toLimit L.toBase (limit.π D i₀) f₀ :=
  isPullback_comp_iso_stageBaseChangeCone L.iso

/-- Projecting the limit of the chart system to a chart and then to that chart's stage is the
projection to the limit of `D` followed by the limit projection to the stage. -/
theorem toLimit_comp_limitπ (j : Over i₀) :
    L.toLimit ≫ limit.π D j.left = yoneda.map (L.cone.π.app j) ≫ C.stageMap j :=
  comp_iso_fst_comp_limitπ L.iso L.iso_comp_π j

/-- Projecting the limit of the chart system to a chart and then to `U₀` is its own
projection to `U₀`. -/
theorem baseMap_comp (j : Over i₀) :
    yoneda.map (L.cone.π.app j) ≫ C.baseMap j = L.toBase :=
  comp_baseMap_eq_comp_iso_snd L.iso L.iso_comp_π j

/-- The limit of a chart system is the fibre product of `limit D` with `U₀` over any one of
the later stages, through the corresponding chart. -/
theorem isPullback_stage (j : Over i₀) :
    IsPullback L.toLimit (yoneda.map (L.cone.π.app j)) (limit.π D j.left) (C.stageMap j) :=
  isPullback_comp_iso_chart L.iso L.iso_comp_π j

/-- The underlying scheme of the limit of a chart system is affine. -/
theorem isAffine_pt : IsAffine ((BigFppfOver.toScheme B S hS).obj L.cone.pt) := by
  have : ∀ j, IsAffine (C.schemeDiagram.obj j) := C.isAffine_obj
  exact Scheme.isAffine_of_isLimit _ L.schemeIsLimit

end LimitBridge

/-- A limit of a chart system in the site, as data: a limit cone in the big fppf site of `S`,
and the identification of the presheaf represented by the limit with the base change of
`limit.π D i₀` along `f₀`.  Nothing is said about the underlying schemes; that is the extra
field of `AlgebraicGeometry.Space.AffineChartSystem.LimitBridge`. -/
structure ChartLimit (C : AffineChartSystem B S hS i₀ D U₀ f₀) where
  /-- The limit cone in the site. -/
  cone : Cone C.siteDiagram
  /-- It is a limit cone. -/
  isLimit : IsLimit cone
  /-- The presheaf represented by the limit is the base change of `limit.π D i₀` along
  `f₀`. -/
  iso : yoneda.obj cone.pt ≅ (stageBaseChangeCone B S hS i₀ D U₀ f₀).pt
  /-- The identification is compatible with the projections to the stages. -/
  iso_comp_π : ∀ j : Over i₀,
    iso.hom ≫ (stageBaseChangeCone B S hS i₀ D U₀ f₀).π.app j =
      yoneda.map (cone.π.app j) ≫ C.iso.hom.app j

/-- The limit in the site underlying a limit bridge. -/
@[simps]
def LimitBridge.toChartLimit {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : LimitBridge C) :
    ChartLimit C where
  cone := L.cone
  isLimit := L.isLimit
  iso := L.iso
  iso_comp_π := L.iso_comp_π

namespace ChartLimit

variable {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : ChartLimit C)

/-- The projection of the limit of the chart system to the limit of `D`. -/
noncomputable def toLimit : yoneda.obj L.cone.pt ⟶ limit D :=
  L.iso.hom ≫ stageBaseChangeConeFst B S hS i₀ D U₀ f₀

/-- The projection of the limit of the chart system to the chosen affine scheme-valued point
of the stage `i₀`. -/
noncomputable def toBase :
    yoneda.obj L.cone.pt ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) :=
  L.iso.hom ≫ stageBaseChangeConeSnd B S hS i₀ D U₀ f₀

/-- The limit of the chart system is the fibre product of `limit D` with `U₀` over the stage
`i₀`. -/
theorem isPullback : IsPullback L.toLimit L.toBase (limit.π D i₀) f₀ :=
  isPullback_comp_iso_stageBaseChangeCone L.iso

/-- Projecting the limit of the chart system to a chart and then to that chart's stage is the
projection to the limit of `D` followed by the limit projection to the stage. -/
theorem toLimit_comp_limitπ (j : Over i₀) :
    L.toLimit ≫ limit.π D j.left = yoneda.map (L.cone.π.app j) ≫ C.stageMap j :=
  comp_iso_fst_comp_limitπ L.iso L.iso_comp_π j

/-- Projecting the limit of the chart system to a chart and then to `U₀` is its own
projection to `U₀`. -/
theorem baseMap_comp (j : Over i₀) :
    yoneda.map (L.cone.π.app j) ≫ C.baseMap j = L.toBase :=
  comp_baseMap_eq_comp_iso_snd L.iso L.iso_comp_π j

/-- The limit of a chart system is the fibre product of `limit D` with `U₀` over any one of
the later stages, through the corresponding chart. -/
theorem isPullback_stage (j : Over i₀) :
    IsPullback L.toLimit (yoneda.map (L.cone.π.app j)) (limit.π D j.left) (C.stageMap j) :=
  isPullback_comp_iso_chart L.iso L.iso_comp_π j

end ChartLimit

end AffineChartSystem

end LimitBridge

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Diagram

variable {I : Type u} [Category.{u} I] (i₀ : I)
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (U₀ : BigAffineFppf B S hS)
  (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)

namespace AffineChartSystem

variable {B S hS i₀ D U₀ f₀} (C : AffineChartSystem B S hS i₀ D U₀ f₀)

/-- **A chart system of a system which is small for the site is itself small for the site.** -/
theorem isSiteSmallDiagram_siteDiagram (hb : Space.IsSiteSmall B S hS D) :
    BigFppfOver.IsSiteSmallDiagram C.siteDiagram := by
  rcases hb with ⟨hSize, hHomSize⟩ | hmono
  · exact .of_lt_cof (mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize i₀)
  refine BigFppfOver.IsSiteSmallDiagram.of_mono_yoneda C.iso
    ((BigAffineFppf.inclusion B S hS).obj U₀) (stageBaseChangeSnd B S hS i₀ D U₀ f₀)
    (stageBaseChangeDiagram_map_comp_snd B S hS i₀ D U₀ f₀) (fun j => ?_)
  have _ : Mono (D.map j.hom) := hmono j.hom
  exact (isPullback_stageBaseChange B S hS i₀ D U₀ f₀ j).mono_snd_of_mono

/-- **The presheaves represented by a chart system of a system small for the site form a system
small for the site.** -/
theorem isSiteSmall_siteDiagram_comp_yoneda (hb : Space.IsSiteSmall B S hS D) :
    Space.IsSiteSmall B S hS (C.siteDiagram ⋙ yoneda) := by
  rcases hb with ⟨hSize, hHomSize⟩ | hmono
  · exact .of_lt_cof (mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize i₀)
      (mk_over_hom_lt hHomSize i₀)
  refine .of_mono ?_
  intro j k g
  have _ : Mono (D.map j.hom) := hmono j.hom
  have _ : Mono (stageBaseChangeSnd B S hS i₀ D U₀ f₀ j) :=
    (isPullback_stageBaseChange B S hS i₀ D U₀ f₀ j).mono_snd_of_mono
  have _ : Mono (C.baseMap j) := mono_comp _ _
  have hnat : yoneda.map (C.siteDiagram.map g) ≫ C.iso.hom.app k =
      C.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map g :=
    C.iso.hom.naturality g
  have hbase : yoneda.map (C.siteDiagram.map g) ≫ C.baseMap k = C.baseMap j := by
    change yoneda.map (C.siteDiagram.map g) ≫
        C.iso.hom.app k ≫ stageBaseChangeSnd B S hS i₀ D U₀ f₀ k =
      C.iso.hom.app j ≫ stageBaseChangeSnd B S hS i₀ D U₀ f₀ j
    rw [← Category.assoc, hnat, Category.assoc, stageBaseChangeDiagram_map_comp_snd]
  exact mono_of_mono_fac hbase

end AffineChartSystem

end Diagram

/-! ### The limit of a chart system -/

section LimitBridge

variable {I : Type u} [Category.{u} I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

namespace AffineChartSystem

variable {B S hS}

/-- **The limit of the charts of a chart system of a system small for the site lies in the
site.** -/
theorem limitInSite_siteDiagram [IsCofiltered I] (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hb : Space.IsSiteSmall B S hS D) : BigFppfOver.LimitInSite C.siteDiagram :=
  (C.isSiteSmallDiagram_siteDiagram hb).limitInSite C.isAffine_obj

/-- **The limit of a chart system whose limit of charts lies in the site.** A chart system whose
limit of charts lies in the site has a limit in the big fppf site of `S`, whose underlying
scheme is a limit of the underlying schemes of the charts and which represents the base change
of `limit.π D i₀` along `f₀`. -/
@[stacks 07SF "limit of the affine charts at a stage"]
noncomputable def limitBridgeOfLimitInSite [IsCofiltered I]
    (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hL : BigFppfOver.LimitInSite C.siteDiagram) :
    LimitBridge C := by
  classical
  have hWaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)) :=
    C.isAffine_obj
  have _ : HasLimit C.siteDiagram :=
    BigFppfOver.hasLimit_of_isAffine_of_limitInSite C.siteDiagram hWaff hL
  have _ := BigFppfOver.preservesLimit_toScheme_of_limitInSite C.siteDiagram hWaff hL
  have hyoneda : IsLimit (yoneda.mapCone (limit.cone C.siteDiagram)) :=
    isLimitOfPreserves yoneda (limit.isLimit C.siteDiagram)
  have hpost : IsLimit ((Cone.postcompose C.iso.hom).obj
      (yoneda.mapCone (limit.cone C.siteDiagram))) :=
    (IsLimit.postcomposeHomEquiv C.iso (yoneda.mapCone (limit.cone C.siteDiagram))).symm
      hyoneda
  have hbase : IsLimit (stageBaseChangeCone B S hS i₀ D U₀ f₀) :=
    isLimitPullbackLimitOverPost B S hS D i₀ f₀
  exact
    { cone := limit.cone C.siteDiagram
      isLimit := limit.isLimit C.siteDiagram
      schemeIsLimit :=
        isLimitOfPreserves (BigFppfOver.toScheme B S hS) (limit.isLimit C.siteDiagram)
      iso := hpost.conePointUniqueUpToIso hbase
      iso_comp_π := fun j ↦ hpost.conePointUniqueUpToIso_hom_comp hbase j }

/-- **The limit of a chart system of a system small for the site.** A chart system of a system
which is small for the site has a limit in the big fppf site of `S`, whose underlying scheme is
a limit of the underlying schemes of the charts and which represents the base change of
`limit.π D i₀` along `f₀`. -/
@[stacks 07SF "limit of the affine charts at a stage"]
noncomputable def limitBridgeOfIsSiteSmall [IsCofiltered I]
    (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hb : Space.IsSiteSmall B S hS D) :
    LimitBridge C :=
  C.limitBridgeOfLimitInSite (C.limitInSite_siteDiagram hb)

/-- **For a system satisfying `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, the limit of
the charts of a chart system lies in the site.** -/
theorem limitInSite_of_siteContainsBaseChangeLimits [IsCofiltered I]
    (C : AffineChartSystem B S hS i₀ D U₀ f₀) (hconv : SiteContainsBaseChangeLimits B S hS D) :
    BigFppfOver.LimitInSite C.siteDiagram :=
  hconv i₀ U₀ f₀ C.diagram C.iso

namespace LimitBridge

variable {C : AffineChartSystem B S hS i₀ D U₀ f₀} (L : LimitBridge C)

end LimitBridge

end AffineChartSystem

end LimitBridge

end AlgebraicGeometry.Space

end
