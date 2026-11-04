module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections

/-!
# The chart restriction of a module, compared with a direct image along a diagram of charts

Let `a : X ⟶ Z` be a morphism of algebraic spaces, `G` an `𝒪_Z`-module, `V` an étale scheme
chart of `Z` and `W` an étale scheme chart of `X` lying over it through a morphism `g` of the
chart schemes.  `AlgebraicGeometry.Space.restrictToChart` restricts a module to the Zariski site
of a chart's scheme, and the only comparison relating one such restriction to another along `g`
was `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, an isomorphism
`g^*(G|_V) ≅ (a^*G)|_W` with no description: its adjunct would be a morphism of sheaves of
modules `G|_V ⟶ g_*((a^*G)|_W)`, and no such morphism existed to be compared with.

**This file builds that morphism.**  Its components are the chart components
`AlgebraicGeometry.Space.modulePullbackChartSection` of the unit of the Stacks 03D7 adjunction,
at the diagram of étale charts a Zariski open of `V`'s scheme cuts out, and what makes them
assemble is naturality of that component in the *chart diagram* — previously only naturality in
the module (`AlgebraicGeometry.Space.modulePullbackChartSection_map`) was recorded.

## Main definitions

* `AlgebraicGeometry.Space.chartOpenDiagramHom` is the vertical morphism of schemes over a
  Zariski open `O` of `V`'s scheme: the restriction of `g` to the preimage of `O`.
* `AlgebraicGeometry.Space.chartOpenDiagram` is the resulting commutative diagram of étale
  scheme charts over `a`, with the chart `O` cuts out of `V` below and the chart `g⁻¹O` cuts out
  of `W` above.
* `AlgebraicGeometry.Space.chartRestrictionPushforwardHom` is **the morphism of sheaves of
  modules `G|_V ⟶ g_*((a^*G)|_W)`** on the unsheafified reading
  `AlgebraicGeometry.Space.chartRestrictionSheaf` of the chart restriction, and
  `AlgebraicGeometry.Space.restrictToChartPushforwardHom` is the same morphism on
  `AlgebraicGeometry.Space.restrictToChart` itself.

## Main results

* `AlgebraicGeometry.Space.modulePullbackChartSection_naturality`: **the chart component of the
  unit is natural in the chart diagram**, that is, compatible with étale restriction of the
  charts of the source and the target at once.  This is the `naturality` field of
  `AlgebraicGeometry.Space.modulePullbackChartFMap` read on
  `AlgebraicGeometry.Space.modulePullbackChartSection`, and it is what lets the components be
  assembled into a morphism of sheaves.
* `AlgebraicGeometry.Space.topIso_inv_comp_resLE_appTop`: for a morphism of schemes `f` and an
  open `O` of its target, restricting regular functions to `O` and then pulling back along the
  restriction of `f` to `f⁻¹O` is pulling back along `f` and then restricting to `f⁻¹O`.  This is
  the compatibility of coefficients which makes the components semilinear over the right ring
  map.
* `AlgebraicGeometry.Space.chartOpenDiagramHom_comp_ι`: the restriction of `g` to the preimage
  of `O` is compatible with the inclusions of `O` and `g⁻¹O` into the charts, which is what makes
  the chart diagram commute.
* `AlgebraicGeometry.Space.homOfLE_comp_resLE` and
  `AlgebraicGeometry.Space.chartOpenDiagram_restriction`: the two chart diagrams attached to an
  inclusion of Zariski opens are related by simultaneous restriction of both charts, which is the
  hypothesis of the naturality above.
* `AlgebraicGeometry.Space.chartRestrictionPushforward_scalars`: the coefficient map of the
  chart restriction, followed by pullback along the vertical morphism of the chart diagram, is
  pullback along `g` followed by the coefficient map of the chart restriction of `W`.
* `AlgebraicGeometry.Space.chartRestrictionPushforwardHom_val_app`: **the value of the
  comparison on sections is the chart component of the unit**, which is the description that the
  base-change isomorphism of
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean` lacked.

## Implementation notes

**The components are stated and proved at the level of the natural transformation, not of a
single component of a composite functor.**  Comparing the two readings of a composite at a
component unfolds the direct image through its structure map and exhausts the recursion depth;
the sheaf-level statement does not.  Nothing here raises a compiler limit.

**The sheafification is avoided, not undone.**  `AlgebraicGeometry.Space.restrictToChart`
sheafifies, but `AlgebraicGeometry.Space.restrictToChartIsoChartRestrictionSheaf` says the
presheaf being sheafified is already a sheaf, so the morphism is built on
`AlgebraicGeometry.Space.chartRestrictionSheaf`, whose sections over a Zariski open are the
sections of the module over the étale chart that open cuts out, on the nose, and transported
across that isomorphism afterwards.

**Why the module instances are named.**  The source and target of each component are the
sections of a pushforward of presheaves of modules, and instance search does not find the
transported module structure through the spelling it reduces to; so each use of
`CategoryTheory.ModuleCat.ofHom` names both its source and its target explicitly, exactly as
`AlgebraicGeometry.Space.moduleFMapHom` does.

**The coefficient square is Mathlib-level.**  It is `AlgebraicGeometry.Scheme.Hom.appLE` applied
to `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`: both sides are the restriction of regular
functions along the composite `g⁻¹O ↪ W → V`, read through
`AlgebraicGeometry.Scheme.Opens.topIso` on each side.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

/-! ### The chart component of the unit is natural in the chart diagram -/

section ChartSectionNaturality

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- **The chart component of the unit of the Stacks 03D7 adjunction is natural in the diagram of
étale scheme charts**: restricting the chart of `Y` and the chart of `X` compatibly commutes with
it.

Only naturality in the *module* was recorded
(`AlgebraicGeometry.Space.modulePullbackChartSection_map`); this is naturality in the chart
diagram, which is what a family of components indexed by charts needs in order to be a morphism
of sheaves.  It is the `naturality` field of
`AlgebraicGeometry.Space.modulePullbackChartFMap`, whose values are the chart components. -/
theorem modulePullbackChartSection_naturality
    (d d' : ChartDiagram B S hS X.1 Y.1 f.hom) (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (hcond : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y.1).map j)
    (s : M.val.obj (op d.V)) :
    modulePullbackChartSection B S hS f M d' (M.val.map j.op s) =
      ((modulePullback B S hS f).obj M).val.map i.op
        (modulePullbackChartSection B S hS f M d s) := by
  refine Eq.trans
    (modulePullbackChartFMap_app B S hS f M d' (M.val.map j.op s)).symm ?_
  exact ((modulePullbackChartFMap B S hS f M).naturality d d' i j hcond s).trans
    (congrArg (fun z ↦ ((modulePullback B S hS f).obj M).val.map i.op z)
      (modulePullbackChartFMap_app B S hS f M d s))

end ChartSectionNaturality

/-! ### The coefficient square of a restriction to a preimage open -/

/-- **Restricting regular functions to an open `O` of the target and then pulling back along the
restriction of `f` to `f⁻¹O` is pulling back along `f` and then restricting to `f⁻¹O`.**

Both sides are `AlgebraicGeometry.Scheme.Hom.appLE` of the composite `f⁻¹O ↪ X → Y`, which is the
composite `f⁻¹O → O ↪ Y` by `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`. -/
theorem topIso_inv_comp_resLE_appTop {A C : Scheme.{u}} (f : A ⟶ C) (O : C.Opens) :
    O.topIso.inv ≫ (f.resLE O (f ⁻¹ᵁ O) le_rfl).appTop =
      f.app O ≫ (f ⁻¹ᵁ O).topIso.inv := by
  have hι : ∀ {Y : Scheme.{u}} (U : Y.Opens),
      Scheme.Hom.appLE U.ι U ⊤ (Scheme.Opens.ι_preimage_self U).ge = U.topIso.inv :=
    fun U ↦ (Scheme.Opens.ι_appLE U U ⊤ _).trans (Scheme.Opens.topIso_inv U).symm
  have hB : Scheme.Hom.appLE (f.resLE O (f ⁻¹ᵁ O) le_rfl) ⊤ ⊤
        (Scheme.Hom.preimage_top (f.resLE O (f ⁻¹ᵁ O) le_rfl)).ge =
      (f.resLE O (f ⁻¹ᵁ O) le_rfl).appTop := by
    rw [show Scheme.Hom.appLE (f.resLE O (f ⁻¹ᵁ O) le_rfl) ⊤ ⊤
          (Scheme.Hom.preimage_top (f.resLE O (f ⁻¹ᵁ O) le_rfl)).ge =
        (f.resLE O (f ⁻¹ᵁ O) le_rfl).appTop ≫
          (f ⁻¹ᵁ O).toScheme.presheaf.map (𝟙 (op ⊤)) from rfl,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← hι O, ← hB, ← hι (f ⁻¹ᵁ O), ← Scheme.Hom.appLE_eq_app,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  congr 1
  exact Scheme.Hom.resLE_comp_ι f le_rfl

/-- **The restrictions of `f` to the preimages of two nested opens are compatible with the
inclusions of the opens.**  Both composites are cancelled by the inclusion of the larger open,
which is a monomorphism. -/
theorem homOfLE_comp_resLE {A C : Scheme.{u}} (f : A ⟶ C) {O O' : C.Opens} (i : O' ⟶ O) :
    A.homOfLE ((TopologicalSpace.Opens.map f.base).map i).le ≫
        f.resLE O (f ⁻¹ᵁ O) le_rfl =
      f.resLE O' (f ⁻¹ᵁ O') le_rfl ≫ C.homOfLE i.le := by
  rw [← cancel_mono O.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.homOfLE_ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι]

/-! ### The chart diagram cut out by a Zariski open -/

section ChartOpen

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
    (V : SmallEtale B S hS Z.1) (W : SmallEtale B S hS X.1)
    (g : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Z.1).obj V)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom)

/-- The restriction of `g` to the preimage of a Zariski open `O` of the chart of `Z`, as a
morphism of schemes over the base. -/
def chartOpenDiagramHom (O : (etaleChartScheme B S hS V).Opens) :
    chartOpenOver B S hS W ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O) ⟶
      chartOpenOver B S hS V O :=
  Over.homMk (ObjectProperty.homMk
    (((BigFppfOver.toScheme B S hS).map g).resLE O _ le_rfl)) (by
      apply ObjectProperty.hom_ext
      change ((BigFppfOver.toScheme B S hS).map g).resLE O _ le_rfl ≫ O.ι ≫ _ = _
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
      exact congrArg (fun k ↦ ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O).ι ≫ k)
        (congrArg (fun m ↦ m.hom) (Over.w g)))

/-- The restriction of `g` to the preimage of `O` is compatible with the inclusions of the two
opens into their charts. -/
theorem chartOpenDiagramHom_comp_ι (O : (etaleChartScheme B S hS V).Opens) :
    chartOpenOverι B S hS W ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O) ≫ g =
      chartOpenDiagramHom B S hS V W g O ≫ chartOpenOverι B S hS V O := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact (Scheme.Hom.resLE_comp_ι ((BigFppfOver.toScheme B S hS).map g) le_rfl).symm

/-- **The diagram of étale scheme charts over `a` cut out by a Zariski open `O` of the chart of
`Z`**: the chart `O` cuts out of `V` below, the chart `g⁻¹O` cuts out of `W` above, and the
restriction of `g` between them. -/
def chartOpenDiagram (O : (etaleChartScheme B S hS V).Opens) :
    ChartDiagram B S hS X.1 Z.1 a.hom where
  U := (chartOpens B S hS W).obj ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O)
  V := (chartOpens B S hS V).obj O
  g := chartOpenDiagramHom B S hS V W g O
  comm := by
    change (yoneda.map (chartOpenOverι B S hS W _) ≫ W.obj.hom) ≫ a.hom =
      yoneda.map (chartOpenDiagramHom B S hS V W g O) ≫
        yoneda.map (chartOpenOverι B S hS V O) ≫ V.obj.hom
    rw [Category.assoc, ← hg, ← Category.assoc, ← Functor.map_comp, ← Category.assoc,
      ← Functor.map_comp, chartOpenDiagramHom_comp_ι]

/-- **An inclusion of Zariski opens restricts the two charts of the chart diagram at once.**
This is the hypothesis under which
`AlgebraicGeometry.Space.modulePullbackChartSection_naturality` applies to the chart diagrams of
two nested opens. -/
theorem chartOpenDiagram_restriction {O O' : (etaleChartScheme B S hS V).Opens} (i : O' ⟶ O) :
    (SmallEtale.toOver B S hS X.1).map ((chartOpens B S hS W).map
        ((TopologicalSpace.Opens.map
          ((BigFppfOver.toScheme B S hS).map g).base).map i)) ≫
        (chartOpenDiagram B S hS a V W g hg O).g =
      (chartOpenDiagram B S hS a V W g hg O').g ≫
        (SmallEtale.toOver B S hS Z.1).map ((chartOpens B S hS V).map i) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact homOfLE_comp_resLE ((BigFppfOver.toScheme B S hS).map g) i

/-! ### The coefficients of the comparison -/

/-- **The coefficient map of the chart restriction of `Z` at `O`, followed by pullback of
regular functions along the vertical morphism of the chart diagram, is pullback along `g`
followed by the coefficient map of the chart restriction of `W` at `g⁻¹O`.**

This is the semilinearity under which the chart components assemble into a morphism of sheaves
of modules over the structure sheaf of the chart's scheme.  Both coefficient maps are the
restriction-to-`⊤` identification `AlgebraicGeometry.Scheme.Opens.topIso` on the nose, and the
vertical morphism is the restriction of `g` to the preimage of `O`, so this is
`AlgebraicGeometry.Space.topIso_inv_comp_resLE_appTop`. -/
theorem chartRestrictionPushforward_scalars (O : (etaleChartScheme B S hS V).Opens)
    (r : (etaleChartScheme B S hS V).ringCatSheaf.obj.obj (op O)) :
    chartDiagramRestrict B S hS a (chartOpenDiagram B S hS a V W g hg O)
        (((chartRestrictionRingHom B S hS Z.2 V).app (op O)).hom r) =
      ((chartRestrictionRingHom B S hS X.2 W).app
          (op ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O))).hom
        ((((Scheme.Hom.toRingCatSheafHom
            ((BigFppfOver.toScheme B S hS).map g)).hom.app (op O)).hom r :
          (etaleChartScheme B S hS W).ringCatSheaf.obj.obj
            (op ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O))) : _) := by
  have hsource : chartDiagramRestrict B S hS a (chartOpenDiagram B S hS a V W g hg O)
      (((chartRestrictionRingHom B S hS Z.2 V).app (op O)).hom r) =
      ((((BigFppfOver.toScheme B S hS).map g).resLE O
          ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O) le_rfl).appTop).hom
        ((O.topIso.inv).hom r) := rfl
  have htarget : ((chartRestrictionRingHom B S hS X.2 W).app
          (op ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O))).hom
        ((((Scheme.Hom.toRingCatSheafHom
            ((BigFppfOver.toScheme B S hS).map g)).hom.app (op O)).hom r :
          (etaleChartScheme B S hS W).ringCatSheaf.obj.obj
            (op ((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O))) : _) =
      (((BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O).topIso.inv).hom
        ((((BigFppfOver.toScheme B S hS).map g).app O).hom r) := rfl
  refine hsource.trans (Eq.trans ?_ htarget.symm)
  exact ConcreteCategory.congr_hom
    (topIso_inv_comp_resLE_appTop ((BigFppfOver.toScheme B S hS).map g) O) r

/-! ### The morphism of sheaves of modules -/

variable (G : Modules.{u, u} B S hS Z.1 Z.2)

/-- **The morphism of sheaves of modules `G|_V ⟶ g_*((a^*G)|_W)`**, on the unsheafified reading
`AlgebraicGeometry.Space.chartRestrictionSheaf` of the chart restriction.

Its component over a Zariski open `O` of the chart's scheme is the chart component
`AlgebraicGeometry.Space.modulePullbackChartSection` of the unit of the Stacks 03D7 adjunction at
`AlgebraicGeometry.Space.chartOpenDiagram`, the diagram of étale charts `O` cuts out; it is
additive and semilinear by `AlgebraicGeometry.Space.modulePullbackChartSection_add` and
`AlgebraicGeometry.Space.modulePullbackChartSection_smul` together with
`AlgebraicGeometry.Space.chartRestrictionPushforward_scalars`, and it is natural in `O` by
`AlgebraicGeometry.Space.modulePullbackChartSection_naturality`. -/
def chartRestrictionPushforwardHom :
    chartRestrictionSheaf B S hS Z G V ⟶
      (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).obj
        (chartRestrictionSheaf B S hS X ((modulePullback B S hS a).obj G) W) := by
  refine ⟨{ app := fun O ↦ ?_, naturality := ?_ }⟩
  · refine ModuleCat.ofHom
      (X := (chartRestrictionSheaf B S hS Z G V).val.obj O)
      (Y := ((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).obj
        (chartRestrictionSheaf B S hS X ((modulePullback B S hS a).obj G) W)).val.obj O)
      { toFun := fun x ↦ ULift.up (modulePullbackChartSection B S hS a G
          (chartOpenDiagram B S hS a V W g hg O.unop) x.down)
        map_add' := ?_
        map_smul' := ?_ }
    · exact fun x y ↦ congrArg ULift.up
        (modulePullbackChartSection_add B S hS a G
          (chartOpenDiagram B S hS a V W g hg O.unop) x.down y.down)
    · intro m x
      refine congrArg ULift.up (Eq.trans ?_ (congrArg
        (fun c : chartRing B S hS X.1 X.2
            (chartOpenDiagram B S hS a V W g hg O.unop).U ↦
          c • modulePullbackChartSection B S hS a G
            (chartOpenDiagram B S hS a V W g hg O.unop) x.down)
        (chartRestrictionPushforward_scalars B S hS a V W g hg O.unop m)))
      exact modulePullbackChartSection_smul B S hS a G
        (chartOpenDiagram B S hS a V W g hg O.unop) _ x.down
  · intro O₁ O₂ k
    exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ congrArg ULift.up
      (modulePullbackChartSection_naturality B S hS a G
        (chartOpenDiagram B S hS a V W g hg O₁.unop)
        (chartOpenDiagram B S hS a V W g hg O₂.unop)
        ((chartOpens B S hS W).map ((TopologicalSpace.Opens.map
          ((BigFppfOver.toScheme B S hS).map g).base).map k.unop))
        ((chartOpens B S hS V).map k.unop)
        (chartOpenDiagram_restriction B S hS a V W g hg k.unop) x.down))

/-- **The value of the comparison on sections is the chart component of the unit.**  The sections
of the chart restriction over a Zariski open are the sections of the module over the étale chart
that open cuts out, and the comparison is the chart component of the unit of the Stacks 03D7
adjunction at the chart diagram the open cuts out — which is the description that
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso` had none of. -/
theorem chartRestrictionPushforwardHom_val_app (O : (etaleChartScheme B S hS V).Opens)
    (x : (chartRestrictionSheaf B S hS Z G V).val.obj (op O)) :
    ((chartRestrictionPushforwardHom B S hS a V W g hg G).val.app (op O) x).down =
      modulePullbackChartSection B S hS a G
        (chartOpenDiagram B S hS a V W g hg O) x.down := rfl

/-- **The morphism of sheaves of modules `G|_V ⟶ g_*((a^*G)|_W)`.**

This is `AlgebraicGeometry.Space.chartRestrictionPushforwardHom` transported across
`AlgebraicGeometry.Space.restrictToChartIsoChartRestrictionSheaf`, which says that the presheaf
`AlgebraicGeometry.Space.restrictToChart` sheafifies is already a sheaf.

It is the morphism whose absence was recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean`: the adjunct of
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso` is a morphism of this type, and there was
nothing independently given for it to be proved equal to. -/
def restrictToChartPushforwardHom :
    restrictToChart B S hS Z.2 G V ⟶
      (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).obj
        (restrictToChart B S hS X.2 ((modulePullback B S hS a).obj G) W) :=
  (restrictToChartIsoChartRestrictionSheaf B S hS Z G V).hom ≫
    chartRestrictionPushforwardHom B S hS a V W g hg G ≫
      (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).map
        (restrictToChartIsoChartRestrictionSheaf B S hS X
          ((modulePullback B S hS a).obj G) W).inv

end ChartOpen

end AlgebraicGeometry.Space

end
