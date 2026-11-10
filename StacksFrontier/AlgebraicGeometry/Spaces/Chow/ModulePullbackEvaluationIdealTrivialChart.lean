module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChartZeroSchemeSubschemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTrivialChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts

/-!
# The evaluation ideal of an inverse image section over a trivialising chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, let `G` be an `𝒪_Y`-module with a global section `s`, and let

      U ---ψ---> V
      |          |
      v          v
      X ---f---> Y

be a commutative diagram of étale scheme charts.  The evaluation ideal of Stacks 0845,
`AlgebraicGeometry.Space.sectionEvaluationIdealAt`, is defined chartwise, and
`AlgebraicGeometry.Space.sectionEvaluationIdealAt_modulePullback_le_map` compares the one of the
inverse image section `f^*s` at `U` with the one of `s` at `V`: the first is contained in the
extension of the second along the diagram.  **This file proves the reverse containment**, so that
over a chart `V` trivialising an invertible `G` and an affine chart `U` the evaluation ideal of
`f^*s` *is* the extension of the evaluation ideal of `s`.

The reverse containment is the statement that the unit section of a free generator of `G(V)`
generates the sections of `f^*G` over `U`, and the canonical base change comparison
`AlgebraicGeometry.Space.modulePullbackSectionsBaseChange` is of no use for it: its surjectivity
is exactly the assertion wanted
(`AlgebraicGeometry.Space.modulePullbackSectionsBaseChange_surjective_iff_span_eq_top`) and
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackCartesianAffineCharts.lean` declines to prove
it, producing for quasi-coherent `G` and affine charts only the *existence* of an isomorphism of
the two sides.  What is used instead is the local generation of an inverse image by its chart
sections, `AlgebraicGeometry.Space.spanSieve_modulePullbackChart_mem`, which holds with no
hypothesis on `G` at all — together with a covering refinement that brings the chart sections it
produces, which come from arbitrary chart diagrams, under the trivialisation at `V`.

## Main results

* `AlgebraicGeometry.Space.exists_chartDiagram_prod_comm`: **two chart diagrams whose charts of
  the source lie above one chart `W` of `X` have a common refinement with chart `W`**, namely the
  one whose chart of the target is the fibre product of their charts of the target.  This is the
  covering refinement the argument turns on: the two routes from `W` to `Y` agree, so `W` maps to
  the fibre product.
* `AlgebraicGeometry.Space.map_modulePullbackUnitSection_mem_span` and
  `AlgebraicGeometry.Space.spanSubmodule_moduleFMapSpanningSet_le_span`: over a chart of `X` above
  a trivialising chart of `Y`, **every chart section of `f^*G`, and hence the whole local span of
  them, is a multiple of the restriction of the unit section of the free generator**.
* `AlgebraicGeometry.Space.sectionEvaluationIdealAt_map_le_modulePullback`: **the reverse
  containment**, and
  `AlgebraicGeometry.Space.sectionEvaluationIdealAt_modulePullback_eq_map`: **the evaluation ideal
  of the inverse image section is the extension of the evaluation ideal of the section.**

## Implementation notes

**Freeness of `G` is carried along `V`, not at `V`.**  The forward containment needs only a free
generator `t` of `G(V)` with its coordinate functional; the reverse one needs the compatible family
`e` of free generators of `G(W)` for every chart `W ⟶ V`, which is how
`AlgebraicGeometry.Space.chartRatio` and
`AlgebraicGeometry.Space.exists_affine_chart_free_of_chart` state that a chart trivialises an
invertible module, and is what
`AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible` produces over a covering
family of any chart.  A generator at `V` alone says nothing about the charts above `V`, and the
chart sections to be compared live over fibre products of `V` with other charts.  Invertibility of
`G` is then still needed, for the trivialising covering of `U` for `f^*G` and for the two
hypotheses of the descent step; it is the hypothesis Stacks 0846 carries, and
`AlgebraicGeometry.Space.isInvertible_modulePullback_obj` (Stacks 0B8P) transports it to `f^*G`.

**Affineness of `U` is the hypothesis of the descent step** and is used nowhere else:
`AlgebraicGeometry.Space.mem_sectionEvaluationIdealAt_of_sieve` descends membership in the
evaluation ideal along a covering sieve of an affine chart.  The covering sieve descended along is
the trivialising covering of `U` refined by the span sieves of its free generators, assembled by
`CategoryTheory.GrothendieckTopology.bindOfArrows`.

**No surjective-endomorphism argument is needed.**  Once the free generator `ε` of `(f^*G)(W)` is
known to be a multiple `c₀ • u` of the restricted unit section, and `u` is a multiple `μ • ε` of
`ε` because `ε` is a free generator, injectivity of `r ↦ r • ε` gives `c₀ * μ = 1` outright; the
coordinate functional of `ε` at the value of `f^*s` then differs from the sought element by the
unit `c₀`.

**No declaration here carries a `stacks` tag.**  The comparison of the evaluation ideal across a
morphism of algebraic spaces is not the assertion of a tag — Stacks 0845 and 0846 are about the
zero scheme of one section on one space — and the tags used, 0846 at `V` through
`AlgebraicGeometry.Space.sectionEvaluationIdealAt_eq_span_singleton` and 0B8P, 0B8Q for `f^*G`,
are carried where they are proved.

## References

* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The coordinate functional of a free generator -/

/-- **A free generator of the sections of a module over a chart has a coordinate functional.** -/
theorem exists_dual_smul_eq_self_of_bijective {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (t : M.val.obj (op V))
    (ht : Function.Bijective fun r : chartRing B S hS F hF V ↦ r • t) :
    ∃ l : Module.Dual (chartRing B S hS F hF V) (M.val.obj (op V)),
      (∀ x, l x • t = x) ∧ l t = 1 := by
  have hbij : Function.Bijective
      (LinearMap.toSpanSingleton (chartRing B S hS F hF V) (M.val.obj (op V)) t) := ht
  refine ⟨(LinearEquiv.ofBijective _ hbij).symm.toLinearMap,
    fun x ↦ (LinearEquiv.ofBijective _ hbij).apply_symm_apply x, hbij.injective ?_⟩
  change (LinearEquiv.ofBijective _ hbij) ((LinearEquiv.ofBijective _ hbij).symm t) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (one_smul _ t).symm

variable {X Y : AlgebraicSpaces B S hS}

/-! ### Semilinearity of the unit section -/

/-- The unit section is semilinear over pullback of regular functions along the diagram. -/
theorem modulePullbackUnitSection_smul_eval (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (r : chartRing B S hS Y.1 Y.2 d.V)
    (y : G.val.obj (op d.V)) :
    modulePullbackUnitSection B S hS f G d (r • y) =
      chartDiagramRestrict B S hS f d r • modulePullbackUnitSection B S hS f G d y := by
  have h := (modulePullbackUnitFMap B S hS f G).map_smul d r y
  rw [modulePullbackUnitFMap_app, modulePullbackUnitFMap_app] at h
  exact h

/-! ### The common refinement of two chart diagrams -/

/-- **Two chart diagrams whose charts of the source are both above a chart `W` have a common
refinement with chart `W` of the source.** -/
theorem exists_chartDiagram_prod_comm (f : X ⟶ Y) (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
    (W : SmallEtale B S hS X.1) (k : W ⟶ d.U) (i : W ⟶ d'.U) :
    ∃ (V'' : SmallEtale B S hS Y.1) (j : V'' ⟶ d.V) (j' : V'' ⟶ d'.V)
      (g : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V'')
      (_ : W.1.hom ≫ f.hom = yoneda.map g ≫ V''.1.hom),
      ((SmallEtale.toOver B S hS X.1).map k ≫ d.g =
          g ≫ (SmallEtale.toOver B S hS Y.1).map j) ∧
        ((SmallEtale.toOver B S hS X.1).map i ≫ d'.g =
          g ≫ (SmallEtale.toOver B S hS Y.1).map j') := by
  have hroute : ∀ (e : ChartDiagram B S hS X.1 Y.1 f.hom) (a : W ⟶ e.U),
      yoneda.map ((SmallEtale.toOver B S hS X.1).map a ≫ e.g) ≫ e.V.1.hom = W.1.hom ≫ f.hom := by
    intro e a
    have ha : yoneda.map ((SmallEtale.toOver B S hS X.1).map a) ≫ e.U.1.hom = W.1.hom :=
      CostructuredArrow.w a.hom
    rw [Functor.map_comp, Category.assoc, ← e.comm, ← ha, Category.assoc]
  refine ⟨SmallEtale.prodObj B S hS Y.1 d.V d'.V, SmallEtale.prodFst B S hS Y.1 d.V d'.V,
    SmallEtale.prodSnd B S hS Y.1 d.V d'.V,
    d.V.property.rep.lift' ((SmallEtale.toOver B S hS X.1).map k ≫ d.g)
      ((SmallEtale.toOver B S hS X.1).map i ≫ d'.g) ((hroute d k).trans (hroute d' i).symm),
    ?_, ?_, ?_⟩
  · change W.1.hom ≫ f.hom = yoneda.map _ ≫ yoneda.map (d.V.property.rep.snd d'.V.obj.hom) ≫
      d'.V.obj.hom
    rw [← Functor.map_comp_assoc, Functor.relativelyRepresentable.lift'_snd]
    exact (hroute d' i).symm
  · exact (Functor.relativelyRepresentable.lift'_fst _ _ _ _).symm
  · exact (Functor.relativelyRepresentable.lift'_snd _ _ _ _).symm

/-! ### Chart sections of an inverse image over a trivialising chart -/

/-- **Over a common refinement, a chart section of an inverse image is a multiple of another.**
If the section `y` of `G` over the chart of the diagram `d'` restricts, over the chart of the
refining diagram `d''`, to the multiple by `c` of the restriction of the section `x` of `G` over
the chart of `d`, then the unit section of `y` restricts to the multiple by `c` — read on the
regular functions of the refinement — of the restriction of the unit section of `x`. -/
theorem modulePullbackUnitSection_map_eq_smul (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (d d' d'' : ChartDiagram B S hS X.1 Y.1 f.hom)
    (j : d''.V ⟶ d.V) (j' : d''.V ⟶ d'.V) (k : d''.U ⟶ d.U) (i : d''.U ⟶ d'.U)
    (h₁ : (SmallEtale.toOver B S hS X.1).map k ≫ d.g =
      d''.g ≫ (SmallEtale.toOver B S hS Y.1).map j)
    (h₂ : (SmallEtale.toOver B S hS X.1).map i ≫ d'.g =
      d''.g ≫ (SmallEtale.toOver B S hS Y.1).map j')
    (x : G.val.obj (op d.V)) (y : G.val.obj (op d'.V))
    (xr : G.val.obj (op d''.V)) (hxr : G.val.map j.op x = xr)
    (c : chartRing B S hS Y.1 Y.2 d''.V) (hc : G.val.map j'.op y = c • xr)
    (z : ((modulePullback B S hS f).obj G).val.obj (op d''.U))
    (hz : ((modulePullback B S hS f).obj G).val.map k.op
      (modulePullbackUnitSection B S hS f G d x) = z) :
    ((modulePullback B S hS f).obj G).val.map i.op
        (modulePullbackUnitSection B S hS f G d' y) =
      chartDiagramRestrict B S hS f d'' c • z := by
  have hnat₁ : modulePullbackUnitSection B S hS f G d'' (c • xr) =
      ((modulePullback B S hS f).obj G).val.map i.op
        (modulePullbackUnitSection B S hS f G d' y) := by
    rw [← hc]
    exact modulePullbackUnitSection_naturality f G d' d'' i j' h₂ y
  have hnat₂ : modulePullbackUnitSection B S hS f G d'' xr = z := by
    rw [← hxr, ← hz]
    exact modulePullbackUnitSection_naturality f G d d'' k j h₁ x
  rw [← hnat₁, modulePullbackUnitSection_smul_eval, hnat₂]

variable (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (e : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → G.val.obj (op W))

/-- **Every chart section of an inverse image is, over a chart above a trivialising chart, a
multiple of the unit section of the free generator.** -/
theorem map_modulePullbackUnitSection_mem_span
    (hcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (G.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k)
    (W : SmallEtale B S hS X.1) (k : W ⟶ d.U)
    (uW : ((modulePullback B S hS f).obj G).val.obj (op W))
    (huW : ((modulePullback B S hS f).obj G).val.map k.op
      (modulePullbackUnitSection B S hS f G d (e d.V (𝟙 d.V))) = uW)
    (d' : ChartDiagram B S hS X.1 Y.1 f.hom) (i : W ⟶ d'.U) (y : G.val.obj (op d'.V))
    (vW : ((modulePullback B S hS f).obj G).val.obj (op W))
    (hvW : ((modulePullback B S hS f).obj G).val.map i.op
      (modulePullbackUnitSection B S hS f G d' y) = vW) :
    vW ∈ Submodule.span (chartRing B S hS X.1 X.2 W) {uW} := by
  obtain ⟨V'', j, j', gg, hcomm, h₁, h₂⟩ := exists_chartDiagram_prod_comm B S hS f d d' W k i
  obtain ⟨c, hc⟩ := (hfree V'' j).surjective (G.val.map j'.op y)
  have hgen : G.val.map j.op (e d.V (𝟙 d.V)) = e V'' j := by
    have h := hcompat d.V V'' (𝟙 d.V) j
    rwa [Category.comp_id] at h
  rw [← hvW, modulePullbackUnitSection_map_eq_smul B S hS f G d d' ⟨W, V'', gg, hcomm⟩ j j' k i
    h₁ h₂ (e d.V (𝟙 d.V)) y (e V'' j) hgen c hc.symm uW huW]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **Over a chart above a trivialising chart, the local span of the chart sections of an inverse
image lies in the span of the unit section of the free generator.** -/
theorem spanSubmodule_moduleFMapSpanningSet_le_span
    (hcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (G.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k)
    (W : SmallEtale B S hS X.1) (k : W ⟶ d.U)
    (uW : ((modulePullback B S hS f).obj G).val.obj (op W))
    (huW : ((modulePullback B S hS f).obj G).val.map k.op
      (modulePullbackUnitSection B S hS f G d (e d.V (𝟙 d.V))) = uW)
    (z : ((modulePullback B S hS f).obj G).val.obj (op W))
    (hz : z ∈ (Stacks.SheafOfModules.spanSubmodule ((modulePullback B S hS f).obj G)
      (moduleFMapSpanningSet B S hS f G ((modulePullback B S hS f).obj G)
        (modulePullbackChartFMap B S hS f G))).obj (op W)) :
    z ∈ Submodule.span (chartRing B S hS X.1 X.2 W) {uW} := by
  refine Submodule.span_induction ?_ (zero_mem _) (fun _ _ _ _ ha hb ↦ add_mem ha hb)
    (fun r _ _ hw ↦ Submodule.smul_mem _ r hw) hz
  rintro w ⟨Z, γ, v, ⟨d', ι, y, rfl⟩, rfl⟩
  have hw : ((modulePullback B S hS f).obj G).val.map γ
        (((modulePullback B S hS f).obj G).val.map ι.op
          ((modulePullbackChartFMap B S hS f G).app d' y)) =
      ((modulePullback B S hS f).obj G).val.map (γ.unop ≫ ι).op
        (modulePullbackUnitSection B S hS f G d' y) :=
    (congrArg (fun z ↦ ((modulePullback B S hS f).obj G).val.map γ
        (((modulePullback B S hS f).obj G).val.map ι.op z))
      (modulePullbackChartFMap_app_eq_unitSection B S hS f G d' y)).trans
      (PresheafOfModules.map_comp_apply _ ι.op γ _).symm
  rw [hw]
  exact map_modulePullbackUnitSection_mem_span B S hS f G d e hcompat hfree W k uW huW d'
    (γ.unop ≫ ι) y _ rfl

/-! ### The evaluation ideal over a chart carrying a free generator -/

/-- **The local step of the reverse containment.**  Over a chart `W` of the source above the
chart of the diagram, carrying a free generator of the sections of the inverse image which lies
in the span of the restriction of the unit section of the free generator of `G`, the restriction
of the coordinate of the section lies in the evaluation ideal of the inverse image section. -/
theorem mem_sectionEvaluationChartIdeal_map_of_span (s : G.sections)
    (t : G.val.obj (op d.V))
    (l₀ : Module.Dual (chartRing B S hS Y.1 Y.2 d.V) (G.val.obj (op d.V)))
    (hl₀ : ∀ x, l₀ x • t = x)
    (W : SmallEtale B S hS X.1) (k : W ⟶ d.U)
    (uW : ((modulePullback B S hS f).obj G).val.obj (op W))
    (huW : ((modulePullback B S hS f).obj G).val.map k.op
      (modulePullbackUnitSection B S hS f G d t) = uW)
    (eps : ((modulePullback B S hS f).obj G).val.obj (op W))
    (hepsfree : Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • eps)
    (hepsspan : eps ∈ Submodule.span (chartRing B S hS X.1 X.2 W) {uW}) :
    chartRestrict (hF := X.2) k (chartDiagramRestrict B S hS f d (l₀ (s.eval (op d.V)))) ∈
      sectionEvaluationChartIdeal B S hS X ((modulePullback B S hS f).obj G)
        (modulePullbackSections B S hS f G s) W := by
  have hvalU : (modulePullbackSections B S hS f G s).eval (op d.U) =
      chartDiagramRestrict B S hS f d (l₀ (s.eval (op d.V))) •
        modulePullbackUnitSection B S hS f G d t :=
    (modulePullbackSections_eval_eq_modulePullbackUnitSection B S hS f G s d).trans
      ((congrArg (modulePullbackUnitSection B S hS f G d)
          (hl₀ (s.eval (op d.V))).symm).trans
        (modulePullbackUnitSection_smul_eval B S hS f G d (l₀ (s.eval (op d.V))) t))
  have hvalW : (modulePullbackSections B S hS f G s).eval (op W) =
      chartRestrict (hF := X.2) k (chartDiagramRestrict B S hS f d (l₀ (s.eval (op d.V)))) • uW :=
    ((modulePullbackSections B S hS f G s).property k.op).symm.trans
      ((congrArg (fun z ↦ ((modulePullback B S hS f).obj G).val.map k.op z) hvalU).trans
        ((PresheafOfModules.map_smul ((modulePullback B S hS f).obj G).val k.op
            (chartDiagramRestrict B S hS f d (l₀ (s.eval (op d.V))))
            (modulePullbackUnitSection B S hS f G d t)).trans
          (congrArg (fun z : ((modulePullback B S hS f).obj G).val.obj (op W) ↦
            chartRestrict (hF := X.2) k
              (chartDiagramRestrict B S hS f d (l₀ (s.eval (op d.V)))) • z) huW)))
  obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.1 hepsspan
  obtain ⟨μ, hμ⟩ := hepsfree.surjective uW
  have hμ' : μ • eps = uW := hμ
  have hone : c₀ * μ = 1 := by
    refine hepsfree.injective ?_
    show (c₀ * μ) • eps = (1 : chartRing B S hS X.1 X.2 W) • eps
    rw [mul_smul, hμ', hc₀, one_smul]
  obtain ⟨l₁, hl₁smul, hl₁one⟩ := exists_dual_smul_eq_self_of_bijective B S hS X.2
    ((modulePullback B S hS f).obj G) W eps hepsfree
  have hl₁val : l₁ ((modulePullbackSections B S hS f G s).eval (op W)) =
      chartRestrict (hF := X.2) k
        (chartDiagramRestrict B S hS f d (l₀ (s.eval (op d.V)))) * μ := by
    rw [hvalW, map_smul, ← hμ', map_smul, hl₁one, smul_eq_mul, smul_eq_mul, mul_one]
  have hfinal : chartRestrict (hF := X.2) k
        (chartDiagramRestrict B S hS f d (l₀ (s.eval (op d.V)))) =
      l₁ ((modulePullbackSections B S hS f G s).eval (op W)) * c₀ := by
    rw [hl₁val, mul_assoc, mul_comm μ c₀, hone, mul_one]
  rw [hfinal]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨l₁, rfl⟩)

/-! ### The reverse containment -/

/-- **The extension of the evaluation ideal of a section is contained in the evaluation ideal of
its inverse image.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces, let `G` be an invertible
`𝒪_Y`-module with a global section `s`, and let `d` be a commutative diagram of étale scheme
charts, with chart `U` of `X` over chart `V` of `Y`.  If `G` carries over the charts above `V`
the compatible family `e` of free generators and `U` is affine, then the ideal of `𝒪_X(U)`
generated by the restrictions of the evaluation ideal of Stacks 0845 of `s` at `V` is contained
in the evaluation ideal of the inverse image section `f^*s` at `U`.

This is the containment reverse to
`AlgebraicGeometry.Space.sectionEvaluationIdealAt_modulePullback_le_map`, and with it
`AlgebraicGeometry.Space.sectionEvaluationIdealAt_modulePullback_eq_map`: the evaluation ideal of
`f^*s` on a chart of `X` over a trivialising chart of `Y` is *generated by* the restrictions of
the evaluation ideal of `s`.

Three things go into it, and the hypotheses are what they ask for.  The unit sections of `f^*G`
over a chart `W` of `X` above `U` generate `(f^*G)(W)` only locally and only all of them together
(`AlgebraicGeometry.Space.spanSieve_modulePullbackChart_mem`), and the ones appearing there come
from *arbitrary* chart diagrams; the common refinement
`AlgebraicGeometry.Space.exists_chartDiagram_prod_comm` brings each of them over the fibre
product of `V` with the chart of its own diagram, where the family `e` makes it a multiple of the
unit section of `e` — this is what the family `e` is for, a free generator at `V` alone saying
nothing about the charts above it.  Over a member of the trivialising covering of `U` of
Stacks 0B8Q for `f^*G` — invertible by Stacks 0B8P,
`AlgebraicGeometry.Space.isInvertible_modulePullback_obj` — the free generator is therefore a
multiple of the restricted unit section, and a free generator which is a multiple of an element
of which it is a multiple makes both coefficients units.  Finally
`AlgebraicGeometry.Space.mem_sectionEvaluationIdealAt_of_sieve` descends the resulting membership
from that covering to `U`, and affineness of `U` is its hypothesis. -/
theorem sectionEvaluationIdealAt_map_le_modulePullback (s : G.sections)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Y)
      (structureRingSheaf B S hS Y).property G)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (G.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k) :
    Ideal.map (chartDiagramRestrict B S hS f d)
        (sectionEvaluationChartIdeal B S hS Y G s d.V) ≤
      sectionEvaluationChartIdeal B S hS X ((modulePullback B S hS f).obj G)
        (modulePullbackSections B S hS f G s) d.U := by
  classical
  obtain ⟨l₀, hl₀smul, hl₀one⟩ := exists_dual_smul_eq_self_of_bijective B S hS Y.2 G d.V
    (e d.V (𝟙 d.V)) (hfree d.V (𝟙 d.V))
  -- the descent hypotheses, from invertibility of the inverse image
  have hNinv := isInvertible_modulePullback_obj B S hS f G hinv
  have hrank : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      ((modulePullback B S hS f).obj G) 1 :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS X ((modulePullback B S hS f).obj G) hNinv
  have hqc : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B S hS X ((modulePullback B S hS f).obj G) hNinv
  have hpres : SheafOfModules.IsFinitePresentationOnSite ((modulePullback B S hS f).obj G) :=
    SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
      hrank.isFiniteLocallyFreeOnSite
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2
    ((modulePullback B S hS f).obj G) hqc
  have hfp := module_finitePresentation_sections_of_isFinitePresentationOnSite
    ((modulePullback B S hS f).obj G) hqc hpres
  -- the trivialising covering family of the chart of the source, with its free generators
  obtain ⟨I, V₀, a₀, hcov, hgen⟩ := exists_generator_cover_smul_of_isInvertible B S hS X
    ((modulePullback B S hS f).obj G) hNinv d.U
  choose ε hεcompat hεfree using hgen
  -- the covering sieve: refine the trivialising family by the span sieves of its generators
  have hT : Sieve.generate (Presieve.bindOfArrows V₀ a₀ fun i ↦
      (Stacks.SheafOfModules.spanSieve ((modulePullback B S hS f).obj G)
        (moduleFMapSpanningSet B S hS f G ((modulePullback B S hS f).obj G)
          (modulePullbackChartFMap B S hS f G))
        (ε i (V₀ i) (𝟙 (V₀ i)))).arrows) ∈ SmallEtale.topology B S hS X.1 d.U := by
    refine (SmallEtale.topology B S hS X.1).bindOfArrows hcov fun i ↦ ?_
    exact (SmallEtale.topology B S hS X.1).superset_covering (Sieve.le_generate _)
      (spanSieve_modulePullbackChart_mem B S hS f G (V₀ i) (ε i (V₀ i) (𝟙 (V₀ i))))
  have hprin : sectionEvaluationChartIdeal B S hS Y G s d.V =
      Ideal.span {l₀ (s.eval (op d.V))} :=
    sectionEvaluationIdealAt_eq_span_singleton B S hS Y G s d.V (e d.V (𝟙 d.V)) l₀ hl₀smul
  rw [hprin, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
  refine mem_sectionEvaluationIdealAt_of_sieve B S hS X ((modulePullback B S hS f).obj G)
    (modulePullbackSections B S hS f G s) hcart hfp hU hT _ ?_
  rintro W k ⟨Z, g, h, ⟨i, g', hg'⟩, rfl⟩ hWaff
  -- the free generator of the inverse image over `W` lies in the span of the unit section
  obtain ⟨uW, huW⟩ : ∃ z : ((modulePullback B S hS f).obj G).val.obj (op W),
      ((modulePullback B S hS f).obj G).val.map (g ≫ g' ≫ a₀ i).op
        (modulePullbackUnitSection B S hS f G d (e d.V (𝟙 d.V))) = z := ⟨_, rfl⟩
  have hmem : ((modulePullback B S hS f).obj G).val.map (g ≫ g').op (ε i (V₀ i) (𝟙 (V₀ i))) ∈
      (Stacks.SheafOfModules.spanSubmodule ((modulePullback B S hS f).obj G)
        (moduleFMapSpanningSet B S hS f G ((modulePullback B S hS f).obj G)
          (modulePullbackChartFMap B S hS f G))).obj (op W) :=
    Sieve.downward_closed _ hg' g
  have hεW : ((modulePullback B S hS f).obj G).val.map (g ≫ g').op (ε i (V₀ i) (𝟙 (V₀ i))) =
      ε i W (g ≫ g') := by
    have h := hεcompat i (V₀ i) W (𝟙 (V₀ i)) (g ≫ g')
    rwa [Category.comp_id] at h
  refine mem_sectionEvaluationChartIdeal_map_of_span B S hS f G d s (e d.V (𝟙 d.V)) l₀
    hl₀smul W (g ≫ g' ≫ a₀ i) uW huW (ε i W (g ≫ g')) (hεfree i W (g ≫ g')) ?_
  rw [← hεW]
  exact spanSubmodule_moduleFMapSpanningSet_le_span B S hS f G d e hcompat hfree W
    (g ≫ g' ≫ a₀ i) uW huW _ hmem

/-- **The evaluation ideal of an inverse image section is the extension of the evaluation ideal
of the section**, over a commutative diagram of étale scheme charts whose chart of the target
trivialises an invertible module and whose chart of the source is affine.

The two containments are
`AlgebraicGeometry.Space.sectionEvaluationIdealAt_modulePullback_le_map`, which needs only a free
generator over the chart of the target and neither invertibility nor affineness, and
`AlgebraicGeometry.Space.sectionEvaluationIdealAt_map_le_modulePullback`. -/
theorem sectionEvaluationIdealAt_modulePullback_eq_map (s : G.sections)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Y)
      (structureRingSheaf B S hS Y).property G)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (G.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k) :
    sectionEvaluationChartIdeal B S hS X ((modulePullback B S hS f).obj G)
        (modulePullbackSections B S hS f G s) d.U =
      Ideal.map (chartDiagramRestrict B S hS f d)
        (sectionEvaluationChartIdeal B S hS Y G s d.V) := by
  obtain ⟨l₀, hl₀smul, hl₀one⟩ := exists_dual_smul_eq_self_of_bijective B S hS Y.2 G d.V
    (e d.V (𝟙 d.V)) (hfree d.V (𝟙 d.V))
  exact le_antisymm
    (sectionEvaluationIdealAt_modulePullback_le_map B S hS f G s d (e d.V (𝟙 d.V)) l₀ hl₀smul)
    (sectionEvaluationIdealAt_map_le_modulePullback B S hS f G d e s hinv hU hcompat hfree)

end AlgebraicGeometry.Space

end
