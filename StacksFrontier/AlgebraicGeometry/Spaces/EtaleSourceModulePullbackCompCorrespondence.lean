module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapChartHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondenceComp

/-!
# Stacks 083K's chart bijectivity, reduced to one chart formula for a direct image

Let `p_U : X' ⟶ X` be an **étale** morphism of algebraic spaces over a scheme `S` of a big fppf
site `B` and let `f : X ⟶ Y` be arbitrary.  The mixed comparison
`AlgebraicGeometry.Space.modulePullbackEtaleSourceComparison`

`(p_U ≫ f)^*M ⟶ (f^*M)|_{X'}`

is what the chart bijectivity of Stacks 083K reduces to
(`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_bijective_etaleSource`), and
`AlgebraicGeometry.Space.ModulePullbackEtaleSourceCoherence` makes it an isomorphism out of
*two* equations: one about the comparison of inverse images of Stacks 03LU on chart sections, and
one about the identification of Stacks 03LW on the same sections.

**This file replaces that pair by a single hypothesis, and the hypothesis mentions neither
Stacks 03LW nor the comparison of inverse images.**  What it asks for is the chart formula for
composition with the counit of the direct image along `p_U`: that linear maps of sections along
`f` out of `p_{U*}N` are, bijectively, linear maps of sections along `p_U ≫ f` out of `N`, by the
assignment whose value at a chart diagram `e` is the counit at the identity-vertical diagram of
`e.U` applied to the value at `AlgebraicGeometry.Space.ChartDiagram.postcompSource`.  That is the
declaration the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleChartCorrespondenceComp.lean` record as owed for
`AlgebraicGeometry.Space.ModuleFMap.comp`, specialised to an étale first factor — where, because
every chart diagram over `p_U ≫ f` factors through an étale chart of `X`, it is the chart formula
at *every* diagram rather than only at the factoring ones.

The passage from `p_U^*` to `p_U^*_{ét}`, which was the second coherence, is gone: it is supplied
by `AlgebraicGeometry.Space.moduleFMapEtaleRestrictHomEquiv`, the chart form of the étale
restriction adjunction, which is elementary.

## Main definitions

* `AlgebraicGeometry.Space.ModuleFMapEtaleSourceCompCorrespondence`: **the single hypothesis.**
* `AlgebraicGeometry.Space.moduleFMapOfEtaleSourceHom`: the linear map of sections along `f` out
  of `p_{U*}N` attached to a morphism `(f^*M)|_{X'} ⟶ N`.

## Main results

* `AlgebraicGeometry.Space.bijective_moduleFMapOfEtaleSourceHom`: that assignment is a
  bijection — the chart form of the étale restriction adjunction, the module chart
  correspondence at `p_U` and the chartwise transpose at `f`, in succession.
* `AlgebraicGeometry.Space.modulePushforwardCounit_app_moduleFMapOfEtaleSourceHom`: the counit at
  the identity-vertical diagram cancels the two transposes, leaving the morphism applied to the
  chart section of `f` at the source-postcomposed diagram.  This is the computation that makes
  the hypothesis match the defining property of the mixed comparison.
* `AlgebraicGeometry.Space.bijective_comp_modulePullbackEtaleSourceComparison`: granted the
  hypothesis, composition with the mixed comparison is bijective on morphisms out of it.
* `AlgebraicGeometry.Space.isIso_modulePullbackEtaleSourceComparison` and
  `AlgebraicGeometry.Space.bijective_modulePullbackEtaleSourceComparison_val_app`: so the mixed
  comparison is an isomorphism, hence bijective on the sections over every chart.
* `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_compCorrespondence`:
  **the chart bijectivity of Stacks 083K for every diagram of affine étale charts and every
  quasi-coherent `M`, granted the one hypothesis.**  No presentation of `M` is assumed.

## Implementation notes

The hypothesis is stated as the *existence* of a bijection with the chart formula rather than as
an equation about `AlgebraicGeometry.Space.ModuleFMap.comp`.  That is deliberate and is what
keeps this file short: the consumers need only that some bijection has those values, and a
`ModuleFMap.comp`-valued statement would drag the comparison of direct images into every proof
below.

**The hypothesis is discharged in a companion file, and not by the route described below.**
`AlgebraicGeometry.Space.moduleFMapEtaleSourceCompCorrespondence` in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModuleFMapCompDischarge.lean` proves it
unconditionally, and with it
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite` —
the chart bijectivity of Stacks 083K with no coherence hypothesis.  It goes through
`AlgebraicGeometry.Space.ModuleFMap.compOfIso`, whose comparison of direct images is a
*parameter*, instantiated only inside a theorem: the proof lift that defeats the route below
runs on definitions and not on theorems.  The observations below concern the direct route; in
particular `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` need not become a
component-wise natural isomorphism.

**What that route costs.**  Discharging it here means composing the
three bijections — the module chart correspondence at `f`, the composition comparison of
Stacks 03LU for the direct images, and the module chart correspondence at `p_U ≫ f` — and
identifying the composite's values on chart diagrams with the counit, through
`AlgebraicGeometry.Space.FMap.comp_unique` and `AlgebraicGeometry.Space.FMap.comp_app`.  Every
input to that is in the library, including the Stacks 03LU clause
`AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app` identifying the comparison
with the geometric comparison of Stacks 03G2, part (3), on underlying sheaves of sets.  What
blocks it is the comparison's *spelling*, and the obstructions are these.

* The comparison is a natural transformation out of `f_* ∘ g_*` as a composite functor, so its
  component at a module has `(modulePushforward f ⋙ modulePushforward g).obj F` as its source.
  Restating the Stacks 03LU clause with that source **ascribed** to
  `(modulePushforward g).obj ((modulePushforward f).obj F)` — the spelling every other
  lemma about these morphisms uses — is a kernel deterministic timeout, whether the ascription is
  made by a definition or inline.  The two spellings are definitionally equal, and the
  elaborator accepts the ascription; it is the kernel that does not.
* Conversely, with the source left at the composite-functor spelling the clause restates
  instantly, and so does the module chart correspondence at `f` read at that spelling
  (`moduleFMapHom`'s codomain ascribed to the composite functor's value).
* But then the composite of the two factors cannot be given a name: `rfl` between a definition
  whose body is that composite and the body itself is a `whnf` deterministic timeout, because
  reducing a `≫` whose second factor is a component of
  `CategoryTheory.Functor.compIsoCongr` descends into the `CategoryTheory.eqToIso` of
  `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`, and deciding *that* equality
  of functors is the non-termination the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean` record.  Naming the
  comparison's component instead makes the `rfl` succeed and the Stacks 03LU clause unusable.
* With nothing named, the chain does elaborate — and the kernel then times out on the assembled
  term, for the reason the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModuleChartCorrespondenceComp.lean` record for the
  composite presentation: a proof lifted out of a definition's value leaves an argument whose
  type is not syntactically the parameter type, the kernel's structural shortcut fails, and the
  full definitional check reaches `AlgebraicGeometry.Space.modulePushforwardCompIso'` and the
  comparison equivalence of Stacks 03G1, whose inverse is a `Classical.choose`.

So the obstruction on *this* route is the one already recorded for the composite presentation,
met from the inverse-image side.  What gets past it is not a refactor of the comparison's
spelling but keeping the comparison a parameter until the last moment, which is what the
companion file does; and the Stacks 03LU clause it needs is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`, which is
proved by reading the comparison on a single local section rather than by assembling its factors.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

section Source

/-- The chartwise transpose of `u` at a chart diagram, read through the chart section. -/
private theorem modulePullbackHomFMap_app_chartSection {A A' : AlgebraicSpaces B S hS}
    (g : A ⟶ A') (M : Modules.{u, u} B S hS A'.1 A'.2) (N : Modules.{u, u} B S hS A.1 A.2)
    (u : (modulePullback B S hS g).obj M ⟶ N) (d : ChartDiagram B S hS A.1 A'.1 g.hom)
    (s : M.val.obj (op d.V)) :
    (modulePullbackHomFMap B S hS g M N u).app d s =
      u.val.app (op d.U) (modulePullbackChartSection B S hS g M d s) :=
  (modulePullbackHomFMap_app B S hS g M N u d s).trans
    (congrArg (fun w ↦ u.val.app (op d.U) w)
      (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g M d s))

variable {X' : AlgebraicSpaces B S hS} (pU : X' ⟶ X) (f : X ⟶ Y)
    (hU : IsEtale B S hS pU.hom)

/-- **The chart formula for composition with the counit of the direct image along an étale
`p_U`**: linear maps of sections along `f` out of `p_{U*}N` are, bijectively, linear maps of
sections along `p_U ≫ f` out of `N`, by the assignment whose value at a chart diagram `e` is the
counit of the direct image along `p_U` at the identity-vertical diagram of `e.U`, applied to the
value of the given map at the source-postcomposed diagram of `e`.

This is `AlgebraicGeometry.Space.ModuleFMap.comp` with the counit, together with the chart
formula it is owed, for an **étale** first factor — where, every chart diagram over `p_U ≫ f`
factoring through an étale chart of `X`, the formula holds at every diagram.  It is stated as the
existence of such a bijection because that is all the consumers need, and it is a hypothesis
because the composite of the three bijections cannot at present be identified with it; see
the implementation notes of this file. -/
structure ModuleFMapEtaleSourceCompCorrespondence : Prop where
  /-- Composition with the counit is a bijection with the stated values on chart diagrams. -/
  exists_bijective : ∀ (N : Modules.{u, u} B S hS X'.1 X'.2)
      (M : Modules.{u, u} B S hS Y.1 Y.2),
    ∃ Ξ : ModuleFMap B S hS f ((modulePushforward B S hS pU).obj N) M →
        ModuleFMap B S hS (pU ≫ f) N M,
      Function.Bijective Ξ ∧
        ∀ (ξ : ModuleFMap B S hS f ((modulePushforward B S hS pU).obj N) M)
          (e : ChartDiagram B S hS X'.1 Y.1 (pU ≫ f).hom) (s : M.val.obj (op e.V)),
          (Ξ ξ).app e s =
            (modulePushforwardCounit B S hS pU N).app
              (ChartDiagram.etaleUnit B S hS pU hU e.U)
              (ξ.app (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s)

variable (M : Modules.{u, u} B S hS Y.1 Y.2) (N : Modules.{u, u} B S hS X'.1 X'.2)

/-- The linear map of sections along `f` attached to a morphism out of the étale restriction of
`f^*M`: read the morphism as a linear map of sections along `p_U`, transpose it to a morphism of
modules into the direct image along `p_U`, and take its chartwise transpose at `f`. -/
noncomputable def moduleFMapOfEtaleSourceHom
    (u : (etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M) ⟶ N) :
    ModuleFMap B S hS f ((modulePushforward B S hS pU).obj N) M :=
  modulePullbackFMapEquiv B S hS f ((modulePushforward B S hS pU).obj N) M
    (moduleFMapHom B S hS pU N ((modulePullback B S hS f).obj M)
      (moduleFMapOfEtaleRestrictHom B S hS pU hU N ((modulePullback B S hS f).obj M) u))

/-- That assignment is a bijection: it is the chart form of the étale restriction adjunction,
the module chart correspondence at `p_U` and the chartwise transpose at `f`, in succession. -/
theorem bijective_moduleFMapOfEtaleSourceHom :
    Function.Bijective (moduleFMapOfEtaleSourceHom B S hS pU f hU M N) :=
  ((modulePullbackFMapEquiv B S hS f ((modulePushforward B S hS pU).obj N) M).bijective.comp
    ((modulePushforwardHomEquiv B S hS pU N
      ((modulePullback B S hS f).obj M)).symm.bijective.comp
      (moduleFMapEtaleRestrictHomEquiv B S hS pU hU N
        ((modulePullback B S hS f).obj M)).bijective))

/-- **The values of that linear map of sections at a source-postcomposed diagram**, read through
the counit of the direct image along `p_U`: the counit at the identity-vertical diagram cancels
the two transposes and leaves the morphism itself. -/
theorem modulePushforwardCounit_app_moduleFMapOfEtaleSourceHom
    (u : (etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M) ⟶ N)
    (e : ChartDiagram B S hS X'.1 Y.1 (pU ≫ f).hom) (s : M.val.obj (op e.V)) :
    (modulePushforwardCounit B S hS pU N).app (ChartDiagram.etaleUnit B S hS pU hU e.U)
        ((moduleFMapOfEtaleSourceHom B S hS pU f hU M N u).app
          (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s) =
      u.val.app (op e.U)
        (modulePullbackChartSection B S hS f M
          (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s) := by
  refine Eq.trans (congrArg
    ((modulePushforwardCounit B S hS pU N).app (ChartDiagram.etaleUnit B S hS pU hU e.U))
    (modulePullbackHomFMap_app_chartSection B S hS f M ((modulePushforward B S hS pU).obj N)
      (moduleFMapHom B S hS pU N ((modulePullback B S hS f).obj M)
        (moduleFMapOfEtaleRestrictHom B S hS pU hU N
          ((modulePullback B S hS f).obj M) u))
      (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s)) ?_
  refine Eq.trans (congrArg
    (fun ζ ↦ ζ.app (ChartDiagram.etaleUnit B S hS pU hU e.U)
      (modulePullbackChartSection B S hS f M
        (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s))
    (modulePushforwardHomFMap_moduleFMapHom B S hS pU N
      ((modulePullback B S hS f).obj M)
      (moduleFMapOfEtaleRestrictHom B S hS pU hU N
        ((modulePullback B S hS f).obj M) u))) ?_
  exact moduleFMapOfEtaleRestrictHom_app_etaleUnit B S hS pU hU N
    ((modulePullback B S hS f).obj M) u e.U
    (modulePullbackChartSection B S hS f M
      (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s)

/-- **The chartwise transpose of the composite with the mixed comparison is the bijection of the
hypothesis applied to the linear map of sections of the morphism.**  Both sides are read on a
chart diagram over `p_U ≫ f`: the left-hand side is the morphism applied to the chart section of
`f` at the source-postcomposed diagram, by the defining property of the mixed comparison, and so
is the right-hand side, by the chart formula of the hypothesis together with
`AlgebraicGeometry.Space.modulePushforwardCounit_app_moduleFMapOfEtaleSourceHom`. -/
theorem modulePullbackFMapEquiv_comp_modulePullbackEtaleSourceComparison
    (Ξ : ModuleFMap B S hS f ((modulePushforward B S hS pU).obj N) M →
      ModuleFMap B S hS (pU ≫ f) N M)
    (happ : ∀ (ξ : ModuleFMap B S hS f ((modulePushforward B S hS pU).obj N) M)
        (e : ChartDiagram B S hS X'.1 Y.1 (pU ≫ f).hom) (s : M.val.obj (op e.V)),
      (Ξ ξ).app e s =
        (modulePushforwardCounit B S hS pU N).app
          (ChartDiagram.etaleUnit B S hS pU hU e.U)
          (ξ.app (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s))
    (u : (etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M) ⟶ N) :
    modulePullbackFMapEquiv B S hS (pU ≫ f) N M
        (modulePullbackEtaleSourceComparison B S hS pU f hU (pU ≫ f) rfl M ≫ u) =
      Ξ (moduleFMapOfEtaleSourceHom B S hS pU f hU M N u) := by
  refine ModuleFMap.ext B S hS (funext fun e ↦ funext fun s ↦ ?_)
  refine Eq.trans (modulePullbackHomFMap_app_chartSection B S hS (pU ≫ f) M N
    (modulePullbackEtaleSourceComparison B S hS pU f hU (pU ≫ f) rfl M ≫ u) e s) ?_
  refine Eq.trans (congrArg (fun w ↦ u.val.app (op e.U) w)
    (modulePullbackEtaleSourceComparison_chartSection B S hS pU f hU (pU ≫ f) rfl M e s)) ?_
  exact ((happ (moduleFMapOfEtaleSourceHom B S hS pU f hU M N u) e s).trans
    (modulePushforwardCounit_app_moduleFMapOfEtaleSourceHom B S hS pU f hU M N u e s)).symm

/-- **Composition with the mixed comparison is a bijection on morphisms out of it**, granted the
chart formula.  It is conjugate, by the chartwise transpose of Stacks 03D7, to the bijection of
the hypothesis composed with
`AlgebraicGeometry.Space.moduleFMapOfEtaleSourceHom`, which is a bijection. -/
theorem bijective_comp_modulePullbackEtaleSourceComparison
    (hco : ModuleFMapEtaleSourceCompCorrespondence B S hS pU f hU) :
    Function.Bijective
      (fun u : (etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M) ⟶ N ↦
        modulePullbackEtaleSourceComparison B S hS pU f hU (pU ≫ f) rfl M ≫ u) := by
  obtain ⟨Ξ, hbij, happ⟩ := hco.exists_bijective N M
  have hcomp : Function.Bijective
      (fun u : (etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M) ⟶ N ↦
        Ξ (moduleFMapOfEtaleSourceHom B S hS pU f hU M N u)) :=
    hbij.comp (bijective_moduleFMapOfEtaleSourceHom B S hS pU f hU M N)
  have key := modulePullbackFMapEquiv_comp_modulePullbackEtaleSourceComparison
    B S hS pU f hU M N Ξ happ
  refine ⟨fun u v huv ↦ ?_, fun w ↦ ?_⟩
  · refine hcomp.1 ?_
    exact (key u).symm.trans
      ((congrArg (modulePullbackFMapEquiv B S hS (pU ≫ f) N M) huv).trans (key v))
  · obtain ⟨u, hu⟩ := hcomp.2 (modulePullbackFMapEquiv B S hS (pU ≫ f) N M w)
    exact ⟨u, (modulePullbackFMapEquiv B S hS (pU ≫ f) N M).injective ((key u).trans hu)⟩

end Source

section Iso

variable {X' : AlgebraicSpaces B S hS} (pU : X' ⟶ X) (f : X ⟶ Y)
    (hU : IsEtale B S hS pU.hom) (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- **Granted the chart formula, the mixed comparison is an isomorphism.**  Composition with it
is bijective on morphisms out of it, so it has a right inverse, and that right inverse is a left
inverse by injectivity of composition with it. -/
theorem isIso_modulePullbackEtaleSourceComparison
    (hco : ModuleFMapEtaleSourceCompCorrespondence B S hS pU f hU) (k : X' ⟶ Y)
    (hk : pU ≫ f = k) :
    IsIso (modulePullbackEtaleSourceComparison B S hS pU f hU k hk M) := by
  subst hk
  obtain ⟨v, hv⟩ := (bijective_comp_modulePullbackEtaleSourceComparison B S hS pU f hU M
    ((modulePullback B S hS (pU ≫ f)).obj M) hco).2 (𝟙 _)
  have hv' : modulePullbackEtaleSourceComparison B S hS pU f hU (pU ≫ f) rfl M ≫ v = 𝟙 _ := hv
  refine ⟨v, hv', ?_⟩
  refine (bijective_comp_modulePullbackEtaleSourceComparison B S hS pU f hU M
    ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M)) hco).1 ?_
  show modulePullbackEtaleSourceComparison B S hS pU f hU (pU ≫ f) rfl M ≫ v ≫
      modulePullbackEtaleSourceComparison B S hS pU f hU (pU ≫ f) rfl M =
    modulePullbackEtaleSourceComparison B S hS pU f hU (pU ≫ f) rfl M ≫ 𝟙 _
  rw [← Category.assoc, hv', Category.id_comp, Category.comp_id]

/-- **Granted the chart formula, the mixed comparison is bijective on the sections over every
chart.** -/
theorem bijective_modulePullbackEtaleSourceComparison_val_app
    (hco : ModuleFMapEtaleSourceCompCorrespondence B S hS pU f hU) (k : X' ⟶ Y)
    (hk : pU ≫ f = k) (W : SmallEtale B S hS X'.1) :
    Function.Bijective
      ((modulePullbackEtaleSourceComparison B S hS pU f hU k hk M).val.app (op W)) :=
  have := isIso_modulePullbackEtaleSourceComparison B S hS pU f hU M hco k hk
  SheafOfModules.bijective_iso_hom_val_app
    (asIso (modulePullbackEtaleSourceComparison B S hS pU f hU k hk M)) (op W)

end Iso

/-- **The chart bijectivity of Stacks 083K, for every diagram of affine étale charts, granted the
chart formula for composition with the counit of a direct image along an étale morphism.**

This is `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_coherence` with its
two-field hypothesis replaced by the single hypothesis of this file: no presentation of `M` is
assumed, no square appears, and the identification of Stacks 03LW has left the chain entirely —
what remains is one statement about the direct image along `p_U` and the direct image along
`f`. -/
theorem bijective_modulePullbackChartBaseChange_of_compCorrespondence (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (hco : ModuleFMapEtaleSourceCompCorrespondence B S hS (chartToSpace B S hS X d.U) f
      (isEtale_chartToSpace B S hS X d.U)) :
    letI := chartDiagramAlgebra B S hS f d
    Function.Bijective (modulePullbackChartBaseChange B S hS f M d) :=
  bijective_modulePullbackChartBaseChange_of_bijective_etaleSource B S hS f M hM d hU hV
    (bijective_modulePullbackEtaleSourceComparison_val_app B S hS
      (chartToSpace B S hS X d.U) f (isEtale_chartToSpace B S hS X d.U) M hco
      (chartSpaceMapOver B S hS d.g ≫ chartToSpace B S hS Y d.V)
      (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm).symm
      (chartSpaceIdChartDiagram B S hS f d).U)

end AlgebraicGeometry.Space

end
