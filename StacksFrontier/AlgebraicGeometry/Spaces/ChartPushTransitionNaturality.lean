module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartAlphaBaseCase
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleHomEquivComp

/-!
# The chart transport of Stacks 07UM and the transition maps of the two direct systems

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `ℐ ⊆ 𝒪_X` be a sheaf
of ideals which is cartesian on affine charts, let `𝒢` be coherent and `ℱ` quasi-coherent, and let
`A` be an étale scheme chart of `X`.  `AlgebraicGeometry.Space.chartIdealPowHomEquiv` identifies
the `k`-th term of the direct system of the first display of [Stacks, Tag 07UM] at the chart with
the `k`-th term of the direct system of the first display of [Stacks, Tag 01YB] on the chart's
scheme, **degreewise**; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartIdealPowHomEquiv.lean` record that this is not enough,
the transition maps of both systems being precomposition with a monomorphism and so not
injective.

This file upgrades the degreewise identification to an identification **of direct systems**.  The
scheme-side compatibility of the factorization with the two transitions is
`AlgebraicGeometry.Space.chartPushFactor_comp_idealPowSmulMap`, and the naturality of the Hom-set
transport under precomposition with a morphism of quasi-coherent `𝒪_X`-modules is
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv_overFunctor_map_comp`.  What was missing, and
is supplied here, is the **naturality in the module of the comparison between the chosen and the
direct-image spellings of the chart restriction** — the remaining leg of
`AlgebraicGeometry.Space.chartAlpha`.

## Main results

* `Stacks.CategoryTheory.comp_congr`, `Stacks.CategoryTheory.comp_comp_congr` and
  `Stacks.CategoryTheory.comp_assoc₃`: congruence in a factor of a composite and the
  reassociation of a quadruple composite, stated generically so that no associativity step is
  taken at the chart.
* `Stacks.SheafOfModules.hom_ext_val_app_apply`,
  `Stacks.SheafOfModules.comp_eq_of_forall_val_app_apply` and
  `Stacks.SheafOfModules.comp_eq_of_forall_val_app_apply_unop`: **a morphism of sheaves of modules
  is determined by its components on sections**, and the form of that for two composites.
* `AlgebraicGeometry.Space.chartPushEquiv_pushforward_map_apply`: the direct image of a morphism,
  read on the sections over a Zariski open of the chart's scheme, by `rfl`.
* `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush_naturality`: **the comparison between the
  chosen and the direct-image spellings of the chart restriction is natural in the module.**
* `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush_hom_comp_chartPushFactor_transition`:
  **the comparison intertwines the transition maps of the two direct systems.**
* `AlgebraicGeometry.Space.chartAlpha_idealPowSmulMap_comp`: **the chart transport of
  [Stacks, Tag 07UM] is compatible with the transition maps of the two direct systems** — raising
  the exponent of the ideal on the chart's scheme and reading the result on the slice of the small
  étale site at the chart is reading it at the lower exponent and precomposing with the
  restriction of the inclusion `ℐⁿ𝒢 ⟶ ℐᵏ𝒢`.  This is the `k`-increase the descent from the chart
  needs.

## Implementation notes

**The naturality is proved on sections and nowhere else.**
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` is
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` followed by the
`CategoryTheory.eqToIso` of the equality of the two spellings of the chart restriction, and the
implementation notes of `StacksFrontier/AlgebraicGeometry/Spaces/ChartAlphaBaseCase.lean` record
that
a composite with that isomorphism as its *second* factor cannot have its `val` field projected
inside the heartbeat budget.  Here too the transport of the fourfold-versus-single pushforward
across that equality, read on morphisms, times out in every spelling considered, including
the instantiation of a generic four-layer statement; and so does the component of a composite
whose second factor is the isomorphism.  What does fit is
`Stacks.SheafOfModules.comp_eq_of_forall_val_app_apply`, where both decompositions are performed
generically and the consumer supplies only the component square.

**The hypothesis of the generic ext is quantified over the object of the site, not of its
opposite.**  This is the decisive difference between a version that compiles and one that
does not: a consumer holding a component lemma stated at `Opposite.op V` and supplying it to a
hypothesis quantified over `Z : Cᵒᵖ` pays, at the chart, for converting `Z` to
`Opposite.op Z.unop` in the type of a section, and that conversion exhausts the budget.
`Stacks.SheafOfModules.comp_eq_of_forall_val_app_apply_unop` performs it generically.

**Every associativity step is an instantiation of a generic lemma.**  The two direct systems live
in `AlgebraicGeometry.Scheme.Modules` and in `CategoryTheory.SheafOfModules`, whose `Category`
instances are definitionally but not syntactically equal; a `congrArg` whose binder is written out
at the chart, or a reassociation performed there, is a cross-spelling definitional check.  The
three statements in `Stacks.CategoryTheory` take the factors as arguments, so each check is made
once, generically.

**The statements are split one associativity step per declaration.**  The heartbeat budget is
per-declaration, and the combined forms of
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush_hom_comp_chartPushFactor_transition` and of
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush_hom_comp_chartPushFactor_transition_comp`
both exceed it.

**No declaration here carries a `stacks` tag.**  This is an input to [Stacks, Tag 07UM], not an
assertion of it: the descent from the chart is not proved here, and the surjectivity clause of
Tag 07UM is therefore still unavailable.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.CategoryTheory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- **Congruence in the last factor of a triple composite.**  Stated generically: at the chart
the two outer factors carry the chart data, and a `congrArg` whose binder has to be elaborated
there is what the heartbeat budget is spent on. -/
theorem comp_comp_congr {W X Y Z : C} (a : W ⟶ X) (b : X ⟶ Y) {m m' : Y ⟶ Z} (h : m = m') :
    a ≫ b ≫ m = a ≫ b ≫ m' :=
  congrArg (fun z : Y ⟶ Z => a ≫ b ≫ z) h

/-- **Congruence in the second factor of a composite.** -/
theorem comp_congr {W Y Z : C} (a : W ⟶ Y) {m m' : Y ⟶ Z} (h : m = m') : a ≫ m = a ≫ m' :=
  congrArg (fun z : Y ⟶ Z => a ≫ z) h

/-- **Reassociation of a quadruple composite**, grouping the first three factors.  This is how a
factorization of a triple composite is postcomposed without any associativity rewriting at the
chart. -/
theorem comp_assoc₃ {W X Y Z T : C} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (t : Z ⟶ T) :
    a ≫ b ≫ c ≫ t = (a ≫ b ≫ c) ≫ t :=
  (comp_congr a (Category.assoc b c t).symm).trans (Category.assoc a (b ≫ c) t).symm

end Stacks.CategoryTheory

namespace Stacks.SheafOfModules

universe w m v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : CategoryTheory.Sheaf J RingCat.{w}}

/-- **A morphism of sheaves of modules is determined by its components on sections.**  Stated
generically: at a chart the ring over which a component is linear is reached only by unfolding the
chart data, and `CategoryTheory.ModuleCat.hom_ext` asked to infer it from a chart-level goal
exhausts the heartbeat budget. -/
theorem hom_ext_val_app_apply {M N : _root_.SheafOfModules.{m} R} {f g : M ⟶ N}
    (h : ∀ (Z : Cᵒᵖ) (x : M.val.obj Z), (f.val.app Z).hom x = (g.val.app Z).hom x) : f = g :=
  _root_.SheafOfModules.hom_ext
    (_root_.PresheafOfModules.hom_ext fun Z => ModuleCat.hom_ext (LinearMap.ext (h Z)))

/-- **Two composites of morphisms of sheaves of modules agree as soon as their components do.**
The two decompositions happen inside this generic statement, so a consumer instantiating it never
matches a composite against its decomposition — which at the chart is exactly the definitional
check that does not fit. -/
theorem comp_eq_of_forall_val_app_apply {M N P Q : _root_.SheafOfModules.{m} R}
    (a : M ⟶ N) (b : N ⟶ P) (c : M ⟶ Q) (d : Q ⟶ P)
    (h : ∀ (Z : Cᵒᵖ) (x : M.val.obj Z),
      (b.val.app Z).hom ((a.val.app Z).hom x) = (d.val.app Z).hom ((c.val.app Z).hom x)) :
    a ≫ b = c ≫ d :=
  hom_ext_val_app_apply fun Z x =>
    (comp_val_app_hom_apply a b Z x).trans
      ((h Z x).trans (comp_val_app_hom_apply c d Z x).symm)

/-- **`Stacks.SheafOfModules.comp_eq_of_forall_val_app_apply` with the object of the site
unopped.**  With the hypothesis quantified over an object of the *opposite* category, a
consumer supplying a lemma stated at `Opposite.op V` pays for the conversion at the chart and the
heartbeat budget is gone; with it quantified over the object itself the conversion happens here,
generically. -/
theorem comp_eq_of_forall_val_app_apply_unop {M N P Q : _root_.SheafOfModules.{m} R}
    (a : M ⟶ N) (b : N ⟶ P) (c : M ⟶ Q) (d : Q ⟶ P)
    (h : ∀ (Y : C) (x : M.val.obj (op Y)),
      (b.val.app (op Y)).hom ((a.val.app (op Y)).hom x) =
        (d.val.app (op Y)).hom ((c.val.app (op Y)).hom x)) :
    a ≫ b = c ≫ d :=
  comp_eq_of_forall_val_app_apply a b c d fun Z x => h Z.unop x

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The direct image of a morphism of `𝒪_X`-modules, read on the sections over a Zariski open
of a chart's scheme.**  Through the sections identification it is the morphism itself on the
sections over the étale chart which the open cuts out, by `rfl`: a pushforward does nothing to a
morphism on sections except restrict the scalars it is linear over.

This is `AlgebraicGeometry.Space.chartPushEquiv_chartPushι_apply` for an arbitrary morphism in
place of the inclusion `ℐᵏ𝒢 ⟶ 𝒢`. -/
theorem chartPushEquiv_pushforward_map_apply
    (M N : SheafOfModules.{u} (structureRingSheaf B S hS X)) (f : M ⟶ N)
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (y : (chartPush B S hS X M A).val.obj (op V)) :
    chartPushEquiv B S hS X N A V
        ((((SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).map f).val.app
          (op V)).hom y) =
      (f.val.app (op (openChartOfComparison B S hS X A V))).hom
        (chartPushEquiv B S hS X M A V y) := rfl

/-- **The naturality of the chart transport isomorphism, read on a section.**  This is
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule_naturality` — an equality of morphisms
of sheaves — evaluated at a Zariski open of the chart's scheme and a section there. -/
theorem chartSchemeModuleIsoRestrictModule_naturality_val_app_apply (A : SmallEtale B S hS X.1)
    {M' L' : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (u : M' ⟶ L')
    (V : (chartScheme A).Opens)
    (x : (chartSchemeModule B S hS X M'.obj M'.property A).val.obj (op V)) :
    ((chartSchemeModuleIsoRestrictModule B S hS X L'.obj L'.property A).hom.val.app (op V)).hom
        ((((chartSchemeModuleFunctor B S hS X A).map u).val.app (op V)).hom x) =
      (chartSectionsMap B S hS X A u V).hom
        (((chartSchemeModuleIsoRestrictModule B S hS X M'.obj M'.property A).hom.val.app
          (op V)).hom x) :=
  (Stacks.SheafOfModules.comp_val_app_hom_apply ((chartSchemeModuleFunctor B S hS X A).map u)
        (chartSchemeModuleIsoRestrictModule B S hS X L'.obj L'.property A).hom
        (op V) x).symm.trans
    ((congrArg
        (fun m : chartSchemeModule B S hS X M'.obj M'.property A ⟶
            (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property).obj
              (chartSchemeEtaleModule B S hS X L'.obj L'.property A) =>
          (m.val.app (op V)).hom x)
        (chartSchemeModuleIsoRestrictModule_naturality B S hS X A u)).trans
      (Stacks.SheafOfModules.comp_val_app_hom_apply
        (chartSchemeModuleIsoRestrictModule B S hS X M'.obj M'.property A).hom
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            (chartScheme A) (chartFppfObject B S hS X A).left.property).map
          ((chartSchemeEtaleModuleFunctor B S hS X A).map u))
        (op V) x))

/-- **The naturality of the comparison with the direct-image spelling, read through the sections
identification.**  The two halves are the naturality of
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` and the naturality of the chart
sections identification, `AlgebraicGeometry.Space.chartSectionsLinearEquiv_naturality_apply`;
`AlgebraicGeometry.Space.chartPushEquiv_chartSchemeModuleIsoChartPush_apply` passes between the
two sections identifications. -/
theorem chartPushEquiv_chartSchemeModuleIsoChartPush_naturality_apply (A : SmallEtale B S hS X.1)
    {M' L' : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (u : M' ⟶ L')
    (V : (chartScheme A).Opens)
    (x : (chartSchemeModule B S hS X M'.obj M'.property A).val.obj (op V)) :
    chartPushEquiv B S hS X L'.obj A V
        (((chartSchemeModuleIsoChartPush B S hS X L'.obj L'.property A).hom.val.app (op V)).hom
          ((((chartSchemeModuleFunctor B S hS X A).map u).val.app (op V)).hom x)) =
      (u.hom.val.app (op (openChartOfComparison B S hS X A V))).hom
        (chartPushEquiv B S hS X M'.obj A V
          (((chartSchemeModuleIsoChartPush B S hS X M'.obj M'.property A).hom.val.app
            (op V)).hom x)) :=
  (chartPushEquiv_chartSchemeModuleIsoChartPush_apply B S hS X L'.obj L'.property A V
        ((((chartSchemeModuleFunctor B S hS X A).map u).val.app (op V)).hom x)).trans
    ((congrArg
        (fun z : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
            (chartSchemeEtaleModule B S hS X L'.obj L'.property A)).val.obj (op V) =>
          chartSectionsLinearEquiv B S hS X L'.obj L'.property A V z)
        (chartSchemeModuleIsoRestrictModule_naturality_val_app_apply B S hS X A u V x)).trans
      ((chartSectionsLinearEquiv_naturality_apply B S hS X A u V
            (((chartSchemeModuleIsoRestrictModule B S hS X M'.obj M'.property A).hom.val.app
              (op V)).hom x)).trans
        (congrArg
          (fun w : M'.obj.val.obj (op (openChartOfComparison B S hS X A V)) =>
            (u.hom.val.app (op (openChartOfComparison B S hS X A V))).hom w)
          (chartPushEquiv_chartSchemeModuleIsoChartPush_apply B S hS X M'.obj M'.property A V
            x).symm)))

/-- **The naturality of the comparison with the direct-image spelling, on a section.**  The
sections identification of the direct-image spelling is injective, so it cancels. -/
theorem chartSchemeModuleIsoChartPush_naturality_val_app_apply (A : SmallEtale B S hS X.1)
    {M' L' : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (u : M' ⟶ L')
    (V : (chartScheme A).Opens)
    (x : (chartSchemeModule B S hS X M'.obj M'.property A).val.obj (op V)) :
    ((chartSchemeModuleIsoChartPush B S hS X L'.obj L'.property A).hom.val.app (op V)).hom
        ((((chartSchemeModuleFunctor B S hS X A).map u).val.app (op V)).hom x) =
      (((SheafOfModules.pushforward.{u}
            (chartComparisonRingMap B S hS X A)).map u.hom).val.app (op V)).hom
        (((chartSchemeModuleIsoChartPush B S hS X M'.obj M'.property A).hom.val.app
          (op V)).hom x) :=
  (chartPushEquiv B S hS X L'.obj A V).injective
    ((chartPushEquiv_chartSchemeModuleIsoChartPush_naturality_apply B S hS X A u V x).trans
      (chartPushEquiv_pushforward_map_apply B S hS X M'.obj L'.obj u.hom A V
        (((chartSchemeModuleIsoChartPush B S hS X M'.obj M'.property A).hom.val.app
          (op V)).hom x)).symm)

/-- **The comparison between the chosen and the direct-image spellings of the chart restriction
is natural in the module.**

This is what the tree did not have: `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` is
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` followed by a
`CategoryTheory.eqToIso`, and while the first factor is natural
(`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule_naturality`) the transport across
the second cannot be matched against a decomposition at the chart.  It is therefore proved on
sections, where the transport is the chart sections identification and its naturality is
available. -/
theorem chartSchemeModuleIsoChartPush_naturality (A : SmallEtale B S hS X.1)
    {M' L' : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (u : M' ⟶ L') :
    (chartSchemeModuleFunctor B S hS X A).map u ≫
        (chartSchemeModuleIsoChartPush B S hS X L'.obj L'.property A).hom =
      (chartSchemeModuleIsoChartPush B S hS X M'.obj M'.property A).hom ≫
        (SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).map u.hom :=
  Stacks.SheafOfModules.comp_eq_of_forall_val_app_apply_unop
    ((chartSchemeModuleFunctor B S hS X A).map u)
    (chartSchemeModuleIsoChartPush B S hS X L'.obj L'.property A).hom
    (chartSchemeModuleIsoChartPush B S hS X M'.obj M'.property A).hom
    ((SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).map u.hom)
    fun V x => chartSchemeModuleIsoChartPush_naturality_val_app_apply B S hS X A u V x


section KIncrease

variable (I : IdealSheaves B S hS X.1 X.2)
    (hIc : IsCartesianOnAffineCharts I.toSheafOfModules)
    (G F : Modules.{u, u} B S hS X.1 X.2)

/-- Factoring at `n` and lowering the exponent on the chart's scheme, read after the comparison
with the direct-image spelling.  This is
`AlgebraicGeometry.Space.chartPushFactor_comp_idealPowSmulMap` with the comparison prefixed. -/
theorem chartSchemeModuleIsoChartPush_hom_comp_chartPushFactor_comp_idealPowSmulMap
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) {k n : ℕ} (h : k ≤ n)
    (hqn : (idealPowModule I n G).IsQuasicoherentOnSite) :
    (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I n G) hqn A).hom ≫
        chartPushFactor B S hS X I hIc G hIq hGq A n ≫
          Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
            (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) h =
      (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I n G) hqn A).hom ≫
        chartPushHomOfLE B S hS X I G A h ≫
          chartPushFactor B S hS X I hIc G hIq hGq A k :=
  Stacks.CategoryTheory.comp_congr _
    (chartPushFactor_comp_idealPowSmulMap B S hS X I hIc G hIq hGq A h)

/-- The comparison with the direct-image spelling absorbs the chart restriction of the inclusion
`ℐⁿ𝒢 ⟶ ℐᵏ𝒢`.  This is
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush_naturality` at that inclusion, postcomposed
with the factorization at `k`. -/
theorem chartSchemeModuleIsoChartPush_hom_comp_chartPushHomOfLE_comp_chartPushFactor
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) {k n : ℕ} (h : k ≤ n)
    (hqn : (idealPowModule I n G).IsQuasicoherentOnSite)
    (hqk : (idealPowModule I k G).IsQuasicoherentOnSite) :
    (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I n G) hqn A).hom ≫
        chartPushHomOfLE B S hS X I G A h ≫
          chartPushFactor B S hS X I hIc G hIq hGq A k =
      ((chartSchemeModuleFunctor B S hS X A).map
          (ObjectProperty.homMk
            (X := (⟨idealPowModule I n G, hqn⟩ :
              (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                (structureRingSheaf B S hS X)).FullSubcategory))
            (Y := (⟨idealPowModule I k G, hqk⟩ :
              (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                (structureRingSheaf B S hS X)).FullSubcategory))
            (idealPowModuleHomOfLE I G h)) ≫
        (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I k G) hqk A).hom) ≫
      chartPushFactor B S hS X I hIc G hIq hGq A k :=
  (Category.assoc (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I n G) hqn A).hom
      (chartPushHomOfLE B S hS X I G A h)
      (chartPushFactor B S hS X I hIc G hIq hGq A k)).symm.trans
    (CategoryTheory.eq_whisker
      (chartSchemeModuleIsoChartPush_naturality B S hS X A
        (ObjectProperty.homMk
          (X := (⟨idealPowModule I n G, hqn⟩ :
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              (structureRingSheaf B S hS X)).FullSubcategory))
          (Y := (⟨idealPowModule I k G, hqk⟩ :
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              (structureRingSheaf B S hS X)).FullSubcategory))
          (idealPowModuleHomOfLE I G h))).symm _)

/-- **The comparison with the direct-image spelling intertwines the transition maps of the two
direct systems.**  Comparing at `n` and then factoring and lowering the exponent on the chart's
scheme is lowering the exponent on `X` and then comparing at `k` and factoring.

This is the identification of the chart-level direct system `k ↦ Hom(ℐᵏ𝒢|_A, ℱ|_A)` with the
direct system of the first display of [Stacks, Tag 01YB] on the chart's scheme *as a direct
system*; the degreewise identification is
`AlgebraicGeometry.Space.chartIdealPowHomEquiv`. -/
theorem chartSchemeModuleIsoChartPush_hom_comp_chartPushFactor_transition
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) {k n : ℕ} (h : k ≤ n)
    (hqn : (idealPowModule I n G).IsQuasicoherentOnSite)
    (hqk : (idealPowModule I k G).IsQuasicoherentOnSite) :
    (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I n G) hqn A).hom ≫
        chartPushFactor B S hS X I hIc G hIq hGq A n ≫
          Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
            (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) h =
      (chartSchemeModuleFunctor B S hS X A).map
          (ObjectProperty.homMk
            (X := (⟨idealPowModule I n G, hqn⟩ :
              (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                (structureRingSheaf B S hS X)).FullSubcategory))
            (Y := (⟨idealPowModule I k G, hqk⟩ :
              (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                (structureRingSheaf B S hS X)).FullSubcategory))
            (idealPowModuleHomOfLE I G h)) ≫
        (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I k G) hqk A).hom ≫
          chartPushFactor B S hS X I hIc G hIq hGq A k :=
  (chartSchemeModuleIsoChartPush_hom_comp_chartPushFactor_comp_idealPowSmulMap
        B S hS X I hIc G hIq hGq A h hqn).trans
    ((chartSchemeModuleIsoChartPush_hom_comp_chartPushHomOfLE_comp_chartPushFactor
        B S hS X I hIc G hIq hGq A h hqn hqk).trans
      (Category.assoc _ _ _))

/-- The transition intertwining, postcomposed with an arbitrary morphism. -/
theorem chartPushFactor_transition_comp_right (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) {k n : ℕ} (h : k ≤ n)
    (hqn : (idealPowModule I n G).IsQuasicoherentOnSite)
    (hqk : (idealPowModule I k G).IsQuasicoherentOnSite)
    (t : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartSchemeModule B S hS X F hFq A) :
    ((chartSchemeModuleIsoChartPush B S hS X (idealPowModule I n G) hqn A).hom ≫
          chartPushFactor B S hS X I hIc G hIq hGq A n ≫
            Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
              (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) h) ≫ t =
      ((chartSchemeModuleFunctor B S hS X A).map
            (ObjectProperty.homMk
              (X := (⟨idealPowModule I n G, hqn⟩ :
                (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                  (structureRingSheaf B S hS X)).FullSubcategory))
              (Y := (⟨idealPowModule I k G, hqk⟩ :
                (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                  (structureRingSheaf B S hS X)).FullSubcategory))
              (idealPowModuleHomOfLE I G h)) ≫
          (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I k G) hqk A).hom ≫
            chartPushFactor B S hS X I hIc G hIq hGq A k) ≫ t :=
  CategoryTheory.eq_whisker
    (chartSchemeModuleIsoChartPush_hom_comp_chartPushFactor_transition
      B S hS X I hIc G hIq hGq A h hqn hqk) t

/-- **The transition intertwining, reassociated so that both sides are the composites which
`AlgebraicGeometry.Space.chartAlpha` is built from.** -/
theorem chartSchemeModuleIsoChartPush_hom_comp_chartPushFactor_transition_comp
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) {k n : ℕ} (h : k ≤ n)
    (hqn : (idealPowModule I n G).IsQuasicoherentOnSite)
    (hqk : (idealPowModule I k G).IsQuasicoherentOnSite)
    (t : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartSchemeModule B S hS X F hFq A) :
    (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I n G) hqn A).hom ≫
        chartPushFactor B S hS X I hIc G hIq hGq A n ≫
          Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
            (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) h ≫ t =
      (chartSchemeModuleFunctor B S hS X A).map
          (ObjectProperty.homMk
            (X := (⟨idealPowModule I n G, hqn⟩ :
              (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                (structureRingSheaf B S hS X)).FullSubcategory))
            (Y := (⟨idealPowModule I k G, hqk⟩ :
              (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                (structureRingSheaf B S hS X)).FullSubcategory))
            (idealPowModuleHomOfLE I G h)) ≫
        (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I k G) hqk A).hom ≫
          chartPushFactor B S hS X I hIc G hIq hGq A k ≫ t :=
  (Stacks.CategoryTheory.comp_assoc₃ _ _ _ t).trans
    ((chartPushFactor_transition_comp_right B S hS X I hIc G F hIq hGq hFq A h hqn hqk t).trans
      (Stacks.CategoryTheory.comp_assoc₃ _ _ _ t).symm)

/-- **The Hom-set transport of `AlgebraicGeometry.Space.chartAlpha` is the composite it is built
from.**  `AlgebraicGeometry.Space.chartAlpha` is the inverse Hom-set transport of that composite,
so this is `CategoryTheory.Equiv.apply_symm_apply`. -/
theorem chartSchemeModuleHomEquiv_chartAlpha (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1) (k : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A) :
    chartSchemeModuleHomEquiv B S hS X (idealPowModule I k G) F
        (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k) hFq A
        (chartAlpha B S hS X I hIc G F hZ hN hIq hFq hG A k φ) =
      (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I k G)
          (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k) A).hom ≫
        chartPushFactor B S hS X I hIc G hIq hG.toIsQuasicoherentOnSite A k ≫ φ ≫
          (chartSchemeModuleIsoChartPush B S hS X F hFq A).inv :=
  (chartSchemeModuleHomEquiv B S hS X (idealPowModule I k G) F
    (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k) hFq A).apply_symm_apply _

/-- **The chart transport of [Stacks, Tag 07UM] is compatible with the transition maps of the two
direct systems.**  Lowering the exponent on the chart's scheme and then reading the morphism on
the slice of the small étale site at the chart is reading it at the lower exponent and then
precomposing with the restriction to the slice of the inclusion `ℐⁿ𝒢 ⟶ ℐᵏ𝒢`.

**This is the `k`-increase the descent from the chart needs.**  The transition maps of both
systems are precomposition with a monomorphism, hence not injective, so an agreement which holds
in the colimit does not hold at the degree a given `k` names; what this says is that the two
systems are identified *as direct systems*, so that an agreement obtained at a higher degree on
the chart's scheme can be read back on the slice at the chart. -/
theorem chartAlpha_idealPowSmulMap_comp (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1) {k n : ℕ} (h : k ≤ n)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A) :
    chartAlpha B S hS X I hIc G F hZ hN hIq hFq hG A n
        (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
          (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) h ≫ φ) =
      (SheafOfModules.overFunctor (structureRingSheaf B S hS X) A).map
          (idealPowModuleHomOfLE I G h) ≫
        chartAlpha B S hS X I hIc G F hZ hN hIq hFq hG A k φ :=
  (chartSchemeModuleHomEquiv B S hS X (idealPowModule I n G) F
      (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG n) hFq A).injective
    ((chartSchemeModuleHomEquiv_chartAlpha B S hS X I hIc G F hZ hN hIq hFq hG A n
          (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
            (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) h ≫ φ)).trans
      ((Stacks.CategoryTheory.comp_comp_congr
            (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I n G)
              (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG n) A).hom
            (chartPushFactor B S hS X I hIc G hIq hG.toIsQuasicoherentOnSite A n)
            (Category.assoc
              (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
                (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) h)
              φ (chartSchemeModuleIsoChartPush B S hS X F hFq A).inv)).trans
        ((chartSchemeModuleIsoChartPush_hom_comp_chartPushFactor_transition_comp
              B S hS X I hIc G F hIq hG.toIsQuasicoherentOnSite hFq A h
              (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG n)
              (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k)
              (φ ≫ (chartSchemeModuleIsoChartPush B S hS X F hFq A).inv)).trans
          ((Stacks.CategoryTheory.comp_congr _
              (chartSchemeModuleHomEquiv_chartAlpha
                B S hS X I hIc G F hZ hN hIq hFq hG A k φ).symm).trans
            (chartSchemeModuleHomEquiv_overFunctor_map_comp B S hS X F hFq A
              (ObjectProperty.homMk
                (X := (⟨idealPowModule I n G,
                    isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG n⟩ :
                  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                    (structureRingSheaf B S hS X)).FullSubcategory))
                (Y := (⟨idealPowModule I k G,
                    isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k⟩ :
                  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                    (structureRingSheaf B S hS X)).FullSubcategory))
                (idealPowModuleHomOfLE I G h))
              (chartAlpha B S hS X I hIc G F hZ hN hIq hFq hG A k φ)).symm))))

end KIncrease

end AlgebraicGeometry.Space

end
