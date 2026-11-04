module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationStepsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StagesReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedRelationSystem

/-!
# Functoriality of a chart system in the scheme-valued point

An `AlgebraicGeometry.Space.AffineChartSystem` for an inverse system `D : I ⥤ _` at a stage `i₀`
is built from an affine scheme-valued point `f₀ : yoneda U₀ ⟶ D i₀`, and its value at a stage `j`
represents the base change `Dⱼ ×_{D i₀} U₀`. A morphism `τ` of two such points over `D i₀` induces
a morphism of the chart systems they produce, natural in the stage. On rings of global sections
it gives maps compatible with the transition morphisms and with the projections of the limits.

## Main definitions

* `AlgebraicGeometry.Space.AffineChartSystem.inducedPresheafMap`: the map of presheaves
  `yoneda Rⱼ ⟶ yoneda Uⱼ` induced at a stage by a morphism `τ` of the two points, obtained from
  the universal property of the base change `Uⱼ = Dⱼ ×_{D i₀} U₀`.
* `AlgebraicGeometry.Space.AffineChartSystem.inducedMap` and
  `AlgebraicGeometry.Space.AffineChartSystem.inducedHom`: the same map read in the big fppf site
  of `S` through the full faithfulness of Yoneda, and the natural transformation of chart systems
  it assembles into.
* `AlgebraicGeometry.Space.AffineChartSystem.inducedSchemeHom` and
  `AlgebraicGeometry.Space.LimitSituation.stagesSchemeHom`: the induced morphism of the diagrams
  of underlying schemes, and its reindexing by the stages of a limit situation.
* `AlgebraicGeometry.appTopHom` and `AlgebraicGeometry.appTopHomLimit`: the maps on rings of
  global sections induced by a morphism of inverse systems of schemes over a preorder, at a stage
  and at a limit.
* `AlgebraicGeometry.Space.LimitSituation.chartStagesDiagram`,
  `AlgebraicGeometry.Space.LimitSituation.chartStagesCone`,
  `AlgebraicGeometry.Space.LimitSituation.chartStagesRestriction` and
  `AlgebraicGeometry.Space.LimitSituation.chartStagesRestrictionLimit`: the system `Uᵢ` of a
  limit situation at an affine point, its limit, and the restriction maps on rings of global
  sections induced by a morphism of points.

## Main results

* `AlgebraicGeometry.Space.AffineChartSystem.inducedPresheafMap_naturality` and
  `AlgebraicGeometry.Space.AffineChartSystem.inducedMap_naturality`: the induced map of charts is
  natural in the stage.
* `AlgebraicGeometry.Space.AffineChartSystem.stageMap_naturality` and
  `AlgebraicGeometry.Space.AffineChartSystem.baseMap_naturality`: the two projections of a chart
  are natural in the stage.
* `AlgebraicGeometry.appTopHom_map` and `AlgebraicGeometry.appTopHomLimit_π`: the induced maps on
  global sections are compatible with the transition morphisms and with the projections of a
  limiting cone.
* `isSectionsColimit_of_equalizerPresentation_of_relationChart`, in the namespace
  `AlgebraicGeometry.Space.LimitSituation`: for an affine point `U₀ ⟶ X₀` whose relation
  `R₀ = U₀ ×_{X₀} U₀` is affine, if the sections of the stages and of the limit are equalizers of
  the two restriction maps from `Uᵢ` to `Rᵢ` and from `U` to `R`, compatibly with the transition
  maps and the projections, then the sections of the limit are the filtered colimit of the
  sections of the stages.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe v u

namespace AlgebraicGeometry

/-! ### Global sections of a morphism of inverse systems of schemes -/

section AppTop

/-- Global sections of a commuting square of schemes agree along the two composites. -/
private theorem appTop_hom_apply_eq_of_comp_eq {X Y Z W : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ W}
    {c : X ⟶ Z} {d : Z ⟶ W} (h : a ≫ b = c ≫ d) (x : Γ(W, ⊤)) :
    a.appTop.hom (b.appTop.hom x) = c.appTop.hom (d.appTop.hom x) := by
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
    congrArg (fun f : X ⟶ W => f.appTop.hom x) h

variable {J : Type v} [Preorder J] {EU ER : Jᵒᵖ ⥤ Scheme.{u}} (α : ER ⟶ EU)

/-- The map `Γ(EUᵢ, ⊤) → Γ(ERᵢ, ⊤)` on rings of global sections induced at a stage `i` by a
morphism `α : ER ⟶ EU` of inverse systems of schemes indexed by `Jᵒᵖ`. -/
def appTopHom (i : J) : (Γ(EU.obj (op i), ⊤) : Type u) → (Γ(ER.obj (op i), ⊤) : Type u) :=
  (α.app (op i)).appTop.hom

/-- The maps `appTopHom α` on rings of global sections are compatible with the transition
morphisms of the two systems. -/
theorem appTopHom_map (i j : J) (h : i ≤ j) (x : Γ(EU.obj (op i), ⊤)) :
    appTopHom α j ((EU.map (homOfLE h).op).appTop.hom x)
      = (ER.map (homOfLE h).op).appTop.hom (appTopHom α i x) := by
  exact appTop_hom_apply_eq_of_comp_eq (α.naturality (homOfLE h).op).symm x

variable {cU : Cone EU} (hcU : IsLimit cU) (cR : Cone ER)

/-- The map `Γ(cU.pt, ⊤) → Γ(cR.pt, ⊤)` on rings of global sections induced by the morphism
`CategoryTheory.Limits.IsLimit.map` from a cone `cR` over `ER` to a limiting cone `cU` over
`EU`. -/
noncomputable def appTopHomLimit : (Γ(cU.pt, ⊤) : Type u) → (Γ(cR.pt, ⊤) : Type u) :=
  (hcU.map cR α).appTop.hom

/-- The map `appTopHomLimit` on rings of global sections at the limit is compatible with the
projections of the two cones. -/
theorem appTopHomLimit_π (i : J) (x : Γ(EU.obj (op i), ⊤)) :
    appTopHomLimit α hcU cR ((cU.π.app (op i)).appTop.hom x)
      = (cR.π.app (op i)).appTop.hom (appTopHom α i x) := by
  exact appTop_hom_apply_eq_of_comp_eq (hcU.map_π cR α (op i)) x

end AppTop

namespace Space

/-! ### Naturality of the two projections of a chart -/

section Naturality

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Category.{u} I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

namespace AffineChartSystem

variable (C : AffineChartSystem B S hS i₀ D U₀ f₀)

/-- The isomorphism of a chart system with the base change diagram is natural in the stage. -/
private theorem siteDiagram_map_comp_iso_hom_app {j k : Over i₀} (g : j ⟶ k) :
    yoneda.map (C.siteDiagram.map g) ≫ C.iso.hom.app k =
      C.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map g :=
  C.iso.hom.naturality g

/-- The projection of a chart to its own stage is natural in the stage. -/
theorem stageMap_naturality {j k : Over i₀} (g : j ⟶ k) :
    yoneda.map (C.siteDiagram.map g) ≫ C.stageMap k = C.stageMap j ≫ D.map g.left := by
  show yoneda.map (C.siteDiagram.map g) ≫
      C.iso.hom.app k ≫ stageBaseChangeFst B S hS i₀ D U₀ f₀ k =
    (C.iso.hom.app j ≫ stageBaseChangeFst B S hS i₀ D U₀ f₀ j) ≫ D.map g.left
  rw [← Category.assoc, C.siteDiagram_map_comp_iso_hom_app g, Category.assoc,
    stageBaseChangeDiagram_map_comp_fst, Category.assoc]

/-- The projection of a chart to the chosen scheme-valued point `U₀` of the base stage is natural
in the stage. -/
theorem baseMap_naturality {j k : Over i₀} (g : j ⟶ k) :
    yoneda.map (C.siteDiagram.map g) ≫ C.baseMap k = C.baseMap j := by
  show yoneda.map (C.siteDiagram.map g) ≫
      C.iso.hom.app k ≫ stageBaseChangeSnd B S hS i₀ D U₀ f₀ k =
    C.iso.hom.app j ≫ stageBaseChangeSnd B S hS i₀ D U₀ f₀ j
  rw [← Category.assoc, C.siteDiagram_map_comp_iso_hom_app g, Category.assoc,
    stageBaseChangeDiagram_map_comp_snd]

end AffineChartSystem

end Naturality

/-! ### The morphism of chart systems induced by a morphism of scheme-valued points -/

section Induced

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Category.{u} I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶ D.obj i₀}
  {τ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}

namespace AffineChartSystem

variable (C : AffineChartSystem B S hS i₀ D U₀ f₀) (E : AffineChartSystem B S hS i₀ D R₀ g₀)

/-- The map of presheaves `yoneda Rⱼ ⟶ yoneda Uⱼ` of charts induced at a stage `j` by a morphism
`τ : yoneda R₀ ⟶ yoneda U₀` over `D i₀`: the map `Dⱼ ×_{D i₀} R₀ ⟶ Dⱼ ×_{D i₀} U₀` given by the
identity on the first factor and by `τ` on the second. -/
noncomputable def inducedPresheafMap (hτ : τ ≫ f₀ = g₀) (j : Over i₀) :
    yoneda.obj (E.siteDiagram.obj j) ⟶ yoneda.obj (C.siteDiagram.obj j) :=
  (C.isPullback j).lift (E.stageMap j) (E.baseMap j ≫ τ) <| by
    rw [Category.assoc, hτ, (E.isPullback j).w]

/-- The induced map of charts, followed by the projection to the stage, is the projection to the
stage. -/
@[simp]
theorem inducedPresheafMap_comp_stageMap (hτ : τ ≫ f₀ = g₀) (j : Over i₀) :
    C.inducedPresheafMap E hτ j ≫ C.stageMap j = E.stageMap j :=
  (C.isPullback j).lift_fst _ _ _

/-- The induced map of charts, followed by the projection to `U₀`, is the projection to `R₀`
followed by the morphism of points. -/
@[simp]
theorem inducedPresheafMap_comp_baseMap (hτ : τ ≫ f₀ = g₀) (j : Over i₀) :
    C.inducedPresheafMap E hτ j ≫ C.baseMap j = E.baseMap j ≫ τ :=
  (C.isPullback j).lift_snd _ _ _

/-- The induced map of presheaves of charts is natural in the stage. -/
theorem inducedPresheafMap_naturality (hτ : τ ≫ f₀ = g₀) {j k : Over i₀} (g : j ⟶ k) :
    yoneda.map (E.siteDiagram.map g) ≫ C.inducedPresheafMap E hτ k
      = C.inducedPresheafMap E hτ j ≫ yoneda.map (C.siteDiagram.map g) := by
  refine (C.isPullback k).hom_ext ?_ ?_
  · rw [Category.assoc, C.inducedPresheafMap_comp_stageMap E hτ k, Category.assoc,
      C.stageMap_naturality g, ← Category.assoc,
      C.inducedPresheafMap_comp_stageMap E hτ j, E.stageMap_naturality g]
  · rw [Category.assoc, C.inducedPresheafMap_comp_baseMap E hτ k, Category.assoc,
      C.baseMap_naturality g, C.inducedPresheafMap_comp_baseMap E hτ j, ← Category.assoc,
      E.baseMap_naturality g]

/-- The map of charts induced at a stage by a morphism of the two scheme-valued points, as a
morphism of the big fppf site of `S`: the preimage under Yoneda of
`AlgebraicGeometry.Space.AffineChartSystem.inducedPresheafMap`. -/
noncomputable def inducedMap (hτ : τ ≫ f₀ = g₀) (j : Over i₀) :
    E.siteDiagram.obj j ⟶ C.siteDiagram.obj j :=
  Yoneda.fullyFaithful.preimage (C.inducedPresheafMap E hτ j)

/-- The image under Yoneda of the induced morphism of charts is the induced map of presheaves. -/
@[simp]
theorem yoneda_map_inducedMap (hτ : τ ≫ f₀ = g₀) (j : Over i₀) :
    yoneda.map (C.inducedMap E hτ j) = C.inducedPresheafMap E hτ j :=
  Yoneda.fullyFaithful.map_preimage _

/-- The induced morphism of charts in the site is natural in the stage. -/
theorem inducedMap_naturality (hτ : τ ≫ f₀ = g₀) {j k : Over i₀} (g : j ⟶ k) :
    E.siteDiagram.map g ≫ C.inducedMap E hτ k
      = C.inducedMap E hτ j ≫ C.siteDiagram.map g :=
  yoneda.map_injective <| by
    rw [yoneda.map_comp, yoneda.map_comp, C.yoneda_map_inducedMap E hτ k,
      C.yoneda_map_inducedMap E hτ j, C.inducedPresheafMap_naturality E hτ g]

/-- The natural transformation of chart systems induced by a morphism of the two scheme-valued
points, with components `AlgebraicGeometry.Space.AffineChartSystem.inducedMap`. -/
noncomputable def inducedHom (hτ : τ ≫ f₀ = g₀) : E.siteDiagram ⟶ C.siteDiagram where
  app j := C.inducedMap E hτ j
  naturality _ _ g := C.inducedMap_naturality E hτ g

/-- The components of the induced morphism of chart systems are the induced maps of charts. -/
@[simp]
theorem inducedHom_app (hτ : τ ≫ f₀ = g₀) (j : Over i₀) :
    (C.inducedHom E hτ).app j = C.inducedMap E hτ j :=
  rfl

/-- The morphism of the diagrams of underlying schemes induced by a morphism of the two
scheme-valued points. -/
noncomputable def inducedSchemeHom (hτ : τ ≫ f₀ = g₀) : E.schemeDiagram ⟶ C.schemeDiagram :=
  Functor.whiskerRight (C.inducedHom E hτ) (BigFppfOver.toScheme B S hS)

/-- The components of the induced morphism of diagrams of schemes are the morphisms of schemes
underlying the induced maps of charts. -/
@[simp]
theorem inducedSchemeHom_app (hτ : τ ≫ f₀ = g₀) (j : Over i₀) :
    (C.inducedSchemeHom E hτ).app j
      = (BigFppfOver.toScheme B S hS).map (C.inducedMap E hτ j) :=
  rfl

end AffineChartSystem

end Induced

/-! ### The induced morphism, reindexed by the stages of a limit situation -/

namespace LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X) {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶ A.system.obj (op A.base)}
  {τ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
  (E : AffineChartSystem B S hS (op A.base) A.system R₀ g₀)

/-- The morphism of the diagrams of schemes of two chart systems, reindexed by the stages:
`AlgebraicGeometry.Space.AffineChartSystem.inducedSchemeHom` whiskered with the index equivalence
`AlgebraicGeometry.Space.LimitSituation.stagesOverEquivalence`. -/
noncomputable def stagesSchemeHom (hτ : τ ≫ f₀ = g₀) :
    stagesSchemeDiagram A E ⟶ stagesSchemeDiagram A C :=
  Functor.whiskerLeft (stagesOverEquivalence A).functor (C.inducedSchemeHom E hτ)

/-- The components of the reindexed morphism are the morphisms of schemes underlying the induced
maps of charts. -/
@[simp]
theorem stagesSchemeHom_app (hτ : τ ≫ f₀ = g₀) (a : (A.Stages)ᵒᵖ) :
    (stagesSchemeHom A C E hτ).app a
      = (BigFppfOver.toScheme B S hS).map
          (C.inducedMap E hτ ((stagesOverEquivalence A).functor.obj a)) :=
  rfl

/-! ### Equalizer presentations over a chart and its relation -/

section Relation

variable (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)

variable (V : BigAffineFppf B S hS)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ A.system.obj (op A.base))

/-- The system of affine charts of a limit situation at an affine scheme-valued point `g` of the
chosen stage, as a diagram of schemes indexed by the stages:
`AlgebraicGeometry.Space.LimitSituation.chartSystem` read through
`AlgebraicGeometry.Space.LimitSituation.stagesSchemeDiagram`. -/
noncomputable abbrev chartStagesDiagram : (A.Stages)ᵒᵖ ⥤ Scheme.{u} :=
  stagesSchemeDiagram A (A.chartSystem V g)

/-- Every member of the system `AlgebraicGeometry.Space.LimitSituation.chartStagesDiagram` is
affine. -/
theorem isAffine_chartStagesDiagram_obj (a : (A.Stages)ᵒᵖ) :
    IsAffine ((A.chartStagesDiagram V g).obj a) :=
  isAffine_stagesSchemeDiagram_obj A (A.chartSystem V g) a

/-- A cone over `AlgebraicGeometry.Space.LimitSituation.chartStagesDiagram`, from the limit of the
chart system, when the base changes of the stages along the affine points of the chosen stage are
bounded below the cutoff. -/
noncomputable def chartStagesConeOfBounded
    (hb : HasBoundedBaseChanges B S hS (op A.base) A.system) :
    Cone (A.chartStagesDiagram V g) :=
  stagesSchemeCone A (A.chartSystem V g) (A.chartLimitBridgeOfBounded V g hb)

/-- The cone `AlgebraicGeometry.Space.LimitSituation.chartStagesConeOfBounded` is limiting. -/
noncomputable def isLimit_chartStagesConeOfBounded
    (hb : HasBoundedBaseChanges B S hS (op A.base) A.system) :
    IsLimit (A.chartStagesConeOfBounded V g hb) :=
  isLimit_stagesSchemeCone A (A.chartSystem V g) (A.chartLimitBridgeOfBounded V g hb)

/-- A cone over `AlgebraicGeometry.Space.LimitSituation.chartStagesDiagram`, from the limit of the
chart system, when the index type has cardinality below the cofinality of the cutoff. -/
noncomputable def chartStagesCone (hI : #A.I < B.cutoff.ord.cof) :
    Cone (A.chartStagesDiagram V g) :=
  A.chartStagesConeOfBounded V g (A.hasBoundedBaseChanges_of_lt_cof hI)

/-- The cone `AlgebraicGeometry.Space.LimitSituation.chartStagesCone` is limiting. -/
noncomputable def isLimit_chartStagesCone (hI : #A.I < B.cutoff.ord.cof) :
    IsLimit (A.chartStagesCone V g hI) :=
  A.isLimit_chartStagesConeOfBounded V g (A.hasBoundedBaseChanges_of_lt_cof hI)

/-- Restriction of a global function along the map of charts induced by a morphism `τ` of the two
scheme-valued points: `AlgebraicGeometry.appTopHom` of
`AlgebraicGeometry.Space.LimitSituation.stagesSchemeHom`. -/
noncomputable def chartStagesRestriction (hτ : τ ≫ f₀ = g₀) (i : A.Stages) :
    (Γ((A.chartStagesDiagram U₀ f₀).obj (op i), ⊤) : Type u) →
      (Γ((A.chartStagesDiagram R₀ g₀).obj (op i), ⊤) : Type u) :=
  appTopHom (stagesSchemeHom A (A.chartSystem U₀ f₀) (A.chartSystem R₀ g₀) hτ) i

/-- The restriction `AlgebraicGeometry.Space.LimitSituation.chartStagesRestriction` is compatible
with the transition morphisms of the two systems. -/
theorem chartStagesRestriction_map (hτ : τ ≫ f₀ = g₀) (i j : A.Stages) (h : i ≤ j)
    (x : Γ((A.chartStagesDiagram U₀ f₀).obj (op i), ⊤)) :
    A.chartStagesRestriction hτ j
        (((A.chartStagesDiagram U₀ f₀).map (homOfLE h).op).appTop.hom x)
      = ((A.chartStagesDiagram R₀ g₀).map (homOfLE h).op).appTop.hom
          (A.chartStagesRestriction hτ i x) :=
  appTopHom_map _ i j h x

/-- Restriction of a global function at the limit along the comparison of the two limits, when the
base changes of the stages along the affine points of the chosen stage are bounded below the
cutoff: `AlgebraicGeometry.appTopHomLimit` of
`AlgebraicGeometry.Space.LimitSituation.stagesSchemeHom`. -/
noncomputable def chartStagesRestrictionLimitOfBounded (hτ : τ ≫ f₀ = g₀)
    (hb : HasBoundedBaseChanges B S hS (op A.base) A.system) :
    (Γ((A.chartStagesConeOfBounded U₀ f₀ hb).pt, ⊤) : Type u) →
      (Γ((A.chartStagesConeOfBounded R₀ g₀ hb).pt, ⊤) : Type u) :=
  appTopHomLimit (stagesSchemeHom A (A.chartSystem U₀ f₀) (A.chartSystem R₀ g₀) hτ)
    (A.isLimit_chartStagesConeOfBounded U₀ f₀ hb) (A.chartStagesConeOfBounded R₀ g₀ hb)

/-- The restriction at the limit is compatible with the projections of the two cones. -/
theorem chartStagesRestrictionLimitOfBounded_π (hτ : τ ≫ f₀ = g₀)
    (hb : HasBoundedBaseChanges B S hS (op A.base) A.system)
    (i : A.Stages) (x : Γ((A.chartStagesDiagram U₀ f₀).obj (op i), ⊤)) :
    A.chartStagesRestrictionLimitOfBounded hτ hb
        (((A.chartStagesConeOfBounded U₀ f₀ hb).π.app (op i)).appTop.hom x)
      = ((A.chartStagesConeOfBounded R₀ g₀ hb).π.app (op i)).appTop.hom
          (A.chartStagesRestriction hτ i x) :=
  appTopHomLimit_π _ (A.isLimit_chartStagesConeOfBounded U₀ f₀ hb)
    (A.chartStagesConeOfBounded R₀ g₀ hb) i x

/-- Restriction of a global function at the limit along the comparison of the two limits, when the
index type has cardinality below the cofinality of the cutoff: `AlgebraicGeometry.appTopHomLimit`
of `AlgebraicGeometry.Space.LimitSituation.stagesSchemeHom`. -/
noncomputable def chartStagesRestrictionLimit (hτ : τ ≫ f₀ = g₀)
    (hI : #A.I < B.cutoff.ord.cof) :
    (Γ((A.chartStagesCone U₀ f₀ hI).pt, ⊤) : Type u) →
      (Γ((A.chartStagesCone R₀ g₀ hI).pt, ⊤) : Type u) :=
  A.chartStagesRestrictionLimitOfBounded hτ (A.hasBoundedBaseChanges_of_lt_cof hI)

/-- The restriction at the limit is compatible with the projections of the two cones. -/
theorem chartStagesRestrictionLimit_π (hτ : τ ≫ f₀ = g₀) (hI : #A.I < B.cutoff.ord.cof)
    (i : A.Stages) (x : Γ((A.chartStagesDiagram U₀ f₀).obj (op i), ⊤)) :
    A.chartStagesRestrictionLimit hτ hI
        (((A.chartStagesCone U₀ f₀ hI).π.app (op i)).appTop.hom x)
      = ((A.chartStagesCone R₀ g₀ hI).π.app (op i)).appTop.hom
          (A.chartStagesRestriction hτ i x) :=
  A.chartStagesRestrictionLimitOfBounded_π hτ (A.hasBoundedBaseChanges_of_lt_cof hI) i x

/-- Let `X` be an algebraic space, let the index type have cardinality below the cofinality of the
cutoff, and let `f₀' : yoneda U₀ ⟶ X₀` be an affine scheme-valued point of the chosen stage whose
relation `R₀ = U₀ ×_{X₀} U₀` is affine, with projections `t` and `yoneda s` (`hpb`). Both are
morphisms over `X₀`, so each induces a restriction map `Γ(Uᵢ, ⊤) → Γ(Rᵢ, ⊤)` at every stage and
`Γ(U, ⊤) → Γ(R, ⊤)` at the limit. Suppose that `e` identifies `Γ(Xᵢ, ℱᵢ)` with the equalizer of
the two restriction maps at every stage, that `eT` identifies `Γ(X, ℱ)` with the equalizer of the
two maps at the limit, and that these identifications are compatible with the transition maps
(`he`) and with the projections (`heT`). Then `Γ(X, ℱ)` is the filtered colimit of the
`Γ(Xᵢ, ℱᵢ)`.

The hypothesis `e` presents the sections of `F₀` as an equalizer of sections of the structure
sheaf of the charts, so it can hold only when the stagewise sections of `F₀` are those of the
structure sheaf; for other `F₀`, already for `F₀ = 0` over a chart with nonzero sections, the
statement is vacuous. -/
theorem isSectionsColimit_of_equalizerPresentation_of_relationChart
    (hX : IsAlgebraicSpace B S hS X) (hI : #A.I < B.cutoff.ord.cof)
    (f₀' : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base))
    {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
      yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
    {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶
      (BigAffineFppf.inclusion B S hS).obj U₀}
    (hpb : IsPullback t (yoneda.map s) f₀' f₀')
    (e : ∀ i : A.Stages, A.stageSections F₀ i ≃
      {x : Γ((A.chartStagesDiagram U₀ f₀').obj (op i), ⊤) //
        A.chartStagesRestriction (τ := t) (f₀ := f₀') rfl i x
          = A.chartStagesRestriction (τ := yoneda.map s) hpb.w.symm i x})
    (eT : A.limitSections F₀ hX ≃
      {x : Γ((A.chartStagesCone U₀ f₀' hI).pt, ⊤) //
        A.chartStagesRestrictionLimit (τ := t) (f₀ := f₀') rfl hI x
          = A.chartStagesRestrictionLimit (τ := yoneda.map s) hpb.w.symm hI x})
    (he : ∀ (i j : A.Stages) (h : i ≤ j) (σ : A.stageSections F₀ i),
      (e j (A.stageTransition F₀ i j h σ)).1
        = ((A.chartStagesDiagram U₀ f₀').map (homOfLE h).op).appTop.hom (e i σ).1)
    (heT : ∀ (i : A.Stages) (σ : A.stageSections F₀ i),
      (eT (A.stageProjection F₀ hX i σ)).1
        = ((A.chartStagesCone U₀ f₀' hI).π.app (op i)).appTop.hom (e i σ).1) :
    A.IsSectionsColimit F₀ hX :=
  have : ∀ a, IsAffine ((A.chartStagesDiagram U₀ f₀').obj a) :=
    A.isAffine_chartStagesDiagram_obj U₀ f₀'
  have : ∀ a, IsAffine ((A.chartStagesDiagram R₀ (t ≫ f₀')).obj a) :=
    A.isAffine_chartStagesDiagram_obj R₀ (t ≫ f₀')
  A.isSectionsColimit_of_equalizerPresentation_of_isAffine F₀ hX _ _
    (A.isLimit_chartStagesCone U₀ f₀' hI) (A.isLimit_chartStagesCone R₀ (t ≫ f₀') hI)
    (A.chartStagesRestriction_map (τ := t) (f₀ := f₀') rfl)
    (A.chartStagesRestriction_map (τ := yoneda.map s) hpb.w.symm)
    (A.chartStagesRestrictionLimit_π (τ := t) (f₀ := f₀') rfl hI)
    (A.chartStagesRestrictionLimit_π (τ := yoneda.map s) hpb.w.symm hI) e eT he heT

end Relation

end LimitSituation

end Space

end AlgebraicGeometry

end
