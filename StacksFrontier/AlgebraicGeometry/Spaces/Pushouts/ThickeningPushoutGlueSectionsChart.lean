module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutModuleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison

/-!
# Sections of the glued module of a triple over a chart

The declarations of this file are independent of the module
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutGlueSections`,
which treats related material in its own terms.

For a commuting square `U ⟶ V ⟶ V'`, `U ⟶ U' ⟶ V'` of representable morphisms of algebraic
spaces and a triple `(𝒢, ℱ', φ)` over it, the sections of the glued module
`v_*𝒢 ×_{(U ⟶ V')_*ℱ} u'_*ℱ'` over an étale chart `W` of `V'` are the pairs of a section `x` of `𝒢`
over `W_V = W ×_{V'} V` and a section `y` of `ℱ'` over `W_{U'} = W ×_{V'} U'` such that `φ` carries
the chart section of `x` over `W_U` to the chart section of `y`.  This is the description on
which the Milnor patching of Stacks 07RW acts in the proof of Stacks 08KV.

The file also records the chart projection of a direct image as a semilinear map, and the base
change comparison of an inverse image over a chart diagram as an isomorphism of modules
out of an extension of scalars, which are the shapes in which the algebra of
`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/ThickeningPushoutChartAlgebra.lean` consumes them.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeIso`: the base change comparison of an inverse image
  over a chart diagram, as an isomorphism out of an extension of scalars, when it is bijective.
* `AlgebraicGeometry.Space.PushoutModules.targetDiagram` and
  `AlgebraicGeometry.Space.PushoutModules.ambientDiagram`: the chart diagrams `W_U ⟶ W_V` and
  `W_U ⟶ W_{U'}` over the two sides of the square.

## Main results

* `AlgebraicGeometry.Space.chartModProj_smul`: the chart projection is semilinear.
* `AlgebraicGeometry.Space.PushoutModules.glue_sections_ext`,
  `AlgebraicGeometry.Space.PushoutModules.glue_sections_compat` and
  `AlgebraicGeometry.Space.PushoutModules.glue_sections_exists`: the sections of the glued module
  over a chart are the compatible pairs.

## References

* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
* [Stacks Project, Tag 07RW](https://stacks.math.columbia.edu/tag/07RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

section Linear

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The pullback of functions along the cartesian chart diagram of a chart `V`, as a ring map into
the functions on the base-changed chart. -/
abbrev baseChangeChartRestrict (hf : yoneda.relativelyRepresentable f.hom)
    (V : SmallEtale B S hS Y.1) :
    chartRing B S hS Y.1 Y.2 V →+* chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj V) :=
  chartDiagramRestrict B S hS f (baseChangeChartDiagram B S hS f hf V)

/-- **The chart projection of a direct image is semilinear** over the pullback of functions
along the cartesian chart diagram. -/
theorem chartModProj_smul (hf : yoneda.relativelyRepresentable f.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1)
    (r : chartRing B S hS Y.1 Y.2 V)
    (z : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartModProj B S hS f hf N V (r • z) =
      baseChangeChartRestrict B S hS f hf V r • chartModProj B S hS f hf N V z :=
  (chartModProj_eq_modulePushforwardCounitApp B S hS f hf N V (r • z)).trans
    ((modulePushforwardCounitApp_smul B S hS f N (baseChangeChartDiagram B S hS f hf V) r z).trans
      (congrArg
        (fun w => chartDiagramPullback B S hS f (baseChangeChartDiagram B S hS f hf V) r • w)
        (chartModProj_eq_modulePushforwardCounitApp B S hS f hf N V z).symm))

/-- The chart projection of a direct image is additive. -/
theorem chartModProj_add (hf : yoneda.relativelyRepresentable f.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1)
    (z z' : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartModProj B S hS f hf N V (z + z') =
      chartModProj B S hS f hf N V z + chartModProj B S hS f hf N V z' :=
  (chartModProj_eq_modulePushforwardCounitApp B S hS f hf N V (z + z')).trans
    ((modulePushforwardCounitApp_add B S hS f N (baseChangeChartDiagram B S hS f hf V) z z').trans
      (congrArg₂ (· + ·) (chartModProj_eq_modulePushforwardCounitApp B S hS f hf N V z).symm
        (chartModProj_eq_modulePushforwardCounitApp B S hS f hf N V z').symm))

/-- **The base change comparison of an inverse image over a chart diagram**, as an isomorphism
of modules out of the extension of scalars along the pullback of functions, when it is
bijective. -/
def chartBaseChangeIso (M : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hd : letI := chartDiagramAlgebra B S hS f d
      Function.Bijective (modulePullbackChartBaseChange B S hS f M d)) :
    (ModuleCat.extendScalars (chartDiagramRestrict B S hS f d)).obj
        (ModuleCat.of (chartRing B S hS Y.1 Y.2 d.V) (M.val.obj (op d.V))) ≅
      ModuleCat.of (chartRing B S hS X.1 X.2 d.U)
        (((modulePullback B S hS f).obj M).val.obj (op d.U)) :=
  letI := chartDiagramAlgebra B S hS f d
  (LinearEquiv.ofBijective (modulePullbackChartBaseChange B S hS f M d) hd).toModuleIso

/-- The base change comparison carries `1 ⊗ s` to the chart section of `s`. -/
theorem chartBaseChangeIso_hom_one_tmul (M : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hd : letI := chartDiagramAlgebra B S hS f d
      Function.Bijective (modulePullbackChartBaseChange B S hS f M d))
    (s : M.val.obj (op d.V)) :
    (chartBaseChangeIso B S hS f M d hd).hom
        ((1 : chartRing B S hS X.1 X.2 d.U) ⊗ₜ[chartRing B S hS Y.1 Y.2 d.V,
          chartDiagramRestrict B S hS f d] s) =
      modulePullbackChartSection B S hS f M d s :=
  let := chartDiagramAlgebra B S hS f d
  (modulePullbackChartBaseChange_tmul B S hS f M d 1 s).trans (one_smul _ _)

/-- `AlgebraicGeometry.Space.chartBaseChangeIso` at the cartesian chart diagram of a chart `V`,
with the base-changed chart spelled as `(smallBaseChange f hf).obj V`. -/
def baseChangeChartIso (hf : yoneda.relativelyRepresentable f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (hd : letI := chartDiagramAlgebra B S hS f (baseChangeChartDiagram B S hS f hf V)
      Function.Bijective (modulePullbackChartBaseChange B S hS f M
        (baseChangeChartDiagram B S hS f hf V))) :
    (ModuleCat.extendScalars (baseChangeChartRestrict B S hS f hf V)).obj
        (ModuleCat.of (chartRing B S hS Y.1 Y.2 V) (M.val.obj (op V))) ≅
      ModuleCat.of (chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj V))
        (((modulePullback B S hS f).obj M).val.obj (op ((smallBaseChange B S hS f hf).obj V))) :=
  chartBaseChangeIso B S hS f M (baseChangeChartDiagram B S hS f hf V) hd

/-- The base change comparison at the cartesian chart diagram carries `1 ⊗ s` to the chart
section of `s`. -/
theorem baseChangeChartIso_hom_one_tmul (hf : yoneda.relativelyRepresentable f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (hd : letI := chartDiagramAlgebra B S hS f (baseChangeChartDiagram B S hS f hf V)
      Function.Bijective (modulePullbackChartBaseChange B S hS f M
        (baseChangeChartDiagram B S hS f hf V)))
    (s : M.val.obj (op V)) :
    (baseChangeChartIso B S hS f hf M V hd).hom
        ((1 : chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj V)) ⊗ₜ[
          chartRing B S hS Y.1 Y.2 V, baseChangeChartRestrict B S hS f hf V] s) =
      modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf V) s :=
  chartBaseChangeIso_hom_one_tmul B S hS f M (baseChangeChartDiagram B S hS f hf V) hd s

/-- Two equal composites of morphisms of sheaves of modules agree on sections. -/
theorem sheafOfModules_comp_eq_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {P A A' Q : SheafOfModules.{u} R} {f₁ : P ⟶ A} {r : A ⟶ Q}
    {f₂ : P ⟶ A'} {s : A' ⟶ Q} (w : f₁ ≫ r = f₂ ≫ s) (X : Cᵒᵖ) (p : P.val.obj X) :
    r.val.app X (f₁.val.app X p) = s.val.app X (f₂.val.app X p) :=
  congrArg (fun m : P ⟶ Q => m.val.app X p) w

end Linear

namespace PushoutModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U V U' V' : AlgebraicSpaces B S hS} (t : U ⟶ V) (v : V ⟶ V') (a : U ⟶ U') (u' : U' ⟶ V')
    (h : a ≫ u' = t ≫ v)
    (ht : yoneda.relativelyRepresentable t.hom) (hv : yoneda.relativelyRepresentable v.hom)
    (ha : yoneda.relativelyRepresentable a.hom) (hu' : yoneda.relativelyRepresentable u'.hom)
    (htv : yoneda.relativelyRepresentable (t ≫ v).hom)
    (hau : yoneda.relativelyRepresentable (a ≫ u').hom)

/-- The chart diagram `W_U ⟶ W_V` over `t`, for a chart `W` of `V'`. -/
abbrev targetDiagram (W : SmallEtale B S hS V'.1) : ChartDiagram B S hS U.1 V.1 t.hom :=
  (baseChangeChartDiagram B S hS t ht ((smallBaseChange B S hS v hv).obj W)).precompSource
    (chartBaseChangeCompComparison B S hS t v ht hv htv W)

/-- The chart diagram `W_U ⟶ W_{U'}` over `a`, for a chart `W` of `V'`. -/
abbrev ambientDiagram (W : SmallEtale B S hS V'.1) : ChartDiagram B S hS U.1 U'.1 a.hom :=
  (baseChangeChartDiagram B S hS a ha ((smallBaseChange B S hS u' hu').obj W)).precompSource
    (eqToHom (smallBaseChange_obj_congr h.symm htv hau W) ≫
      chartBaseChangeCompComparison B S hS a u' ha hu' hau W)

variable (T : SquareTriple t a) (W : SmallEtale B S hS V'.1)

/-- The first coordinate of a section of the glued module over a chart: its first component,
read on `W_V`. -/
abbrev gluePr₁ (p : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W)) :
    T.target.val.obj (op ((smallBaseChange B S hS v hv).obj W)) :=
  chartModProj B S hS v hv T.target W ((TripleGluing.glueFst (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h) T).val.app _ p)

/-- The second coordinate of a section of the glued module over a chart: its second component,
read on `W_{U'}`. -/
abbrev gluePr₂ (p : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W)) :
    T.ambient.val.obj (op ((smallBaseChange B S hS u' hu').obj W)) :=
  chartModProj B S hS u' hu' T.ambient W ((TripleGluing.glueSnd (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h) T).val.app _ p)

/-- **The two coordinates determine a section of the glued module over a chart.** -/
theorem glue_sections_ext (p q : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W))
    (h₁ : gluePr₁ t v a u' h hv T W p = gluePr₁ t v a u' h hv T W q)
    (h₂ : gluePr₂ t v a u' h hu' T W p = gluePr₂ t v a u' h hu' T W q) : p = q :=
  (sections_of_isPullback (TripleGluing.isPullback_glue (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h) T) W).1 p q
    (chartModProj_injective B S hS v hv T.target W h₁)
    (chartModProj_injective B S hS u' hu' T.ambient W h₂)


/-- **The two coordinates of a section of the glued module over a chart are compatible**: `φ`
carries the chart section of the first over `W_U` to the chart section of the second. -/
theorem glue_sections_compat (p : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W)) :
    T.comparison.hom.val.app _
        (modulePullbackChartSection B S hS t T.target
          (targetDiagram t v ht hv htv W) (gluePr₁ t v a u' h hv T W p)) =
      modulePullbackChartSection B S hS a T.ambient
        (ambientDiagram t v a u' h ha hu' htv hau W) (gluePr₂ t v a u' h hu' T W p) := by
  have hc0 := sheafOfModules_comp_eq_apply (TripleGluing.isPullback_glue
    (qV := modulePushforward B S hS v) (qA := modulePushforward B S hS u')
    (modulePullbackAdjunction B S hS t) (modulePullbackAdjunction B S hS a)
    (modulePushforwardCompIso B S hS t v) (compTransport a u' (t ≫ v) h) T).w _ p
  have hc := congrArg (chartModProj B S hS (t ≫ v) htv
    ((modulePullback B S hS a).obj T.ambient) W) hc0
  have h1 := chartModProj_targetMap_of_comp t v a ht hv htv T W
  have h2 := chartModProj_ambientMap_of_comp t a u' ha hu' hau h htv T W
  exact ((h1 _).symm.trans hc).trans (h2 _)

/-- **A compatible pair of coordinates is a section of the glued module over a chart.** -/
theorem glue_sections_exists (x : T.target.val.obj (op ((smallBaseChange B S hS v hv).obj W)))
    (y : T.ambient.val.obj (op ((smallBaseChange B S hS u' hu').obj W)))
    (hxy : T.comparison.hom.val.app _
        (modulePullbackChartSection B S hS t T.target (targetDiagram t v ht hv htv W) x) =
      modulePullbackChartSection B S hS a T.ambient
        (ambientDiagram t v a u' h ha hu' htv hau W) y) :
    ∃ p : ((TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u') (modulePullbackAdjunction B S hS t)
    (modulePullbackAdjunction B S hS a) (modulePushforwardCompIso B S hS t v)
    (compTransport a u' (t ≫ v) h)).obj T).val.obj (op W),
      gluePr₁ t v a u' h hv T W p = x ∧ gluePr₂ t v a u' h hu' T W p = y := by
  obtain ⟨x', hx'⟩ := (bijective_chartModProj B S hS v hv T.target W).2 x
  obtain ⟨y', hy'⟩ := (bijective_chartModProj B S hS u' hu' T.ambient W).2 y
  have h1 := chartModProj_targetMap_of_comp t v a ht hv htv T W x'
  have h2 := chartModProj_ambientMap_of_comp t a u' ha hu' hau h htv T W y'
  rw [hx'] at h1
  rw [hy'] at h2
  have hpb := (sections_of_isPullback (TripleGluing.isPullback_glue
    (qV := modulePushforward B S hS v) (qA := modulePushforward B S hS u')
    (modulePullbackAdjunction B S hS t) (modulePullbackAdjunction B S hS a)
    (modulePushforwardCompIso B S hS t v) (compTransport a u' (t ≫ v) h) T) W).2 x' y'
    (chartModProj_injective B S hS (t ≫ v) htv ((modulePullback B S hS a).obj T.ambient) W
      (h1.trans (hxy.trans h2.symm)))
  obtain ⟨p, hp₁, hp₂⟩ := hpb
  refine ⟨p, ?_, ?_⟩
  · exact (congrArg (chartModProj B S hS v hv T.target W) hp₁).trans hx'
  · exact (congrArg (chartModProj B S hS u' hu' T.ambient W) hp₂).trans hy'

end PushoutModules

end AlgebraicGeometry.Space

end
