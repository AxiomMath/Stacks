module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Hom

/-!
# The stalks of a glued sheaf of modules

Stacks 00AM glues a sheaf of modules on a scheme `S` from sheaves of modules on the members of a
family of charts `f i : Y i ⟶ S` of open immersions. This file identifies the stalks of the glued
sheaf with the stalks of the chart sheaves, and reads short exactness of a complex of glued
sheaves off short exactness of the complexes of chart sheaves.

Nothing about stalks is built here. Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` already identifies the stalk at `y` of the
restriction of a sheaf of modules along an open immersion with the stalk at the image of `y`, as
an isomorphism *natural in the sheaf*; the glueing datum supplies the identification
`Stacks.SheafOfModules.ModulesGlueData.chartIso` of the restriction of the glued sheaf with the
chart sheaf. The only thing missing was that the latter identification carries a morphism of
glueing data to its chart morphisms, which is `ModulesGlueData.Hom.chartIso_glued` below, and
once it is in hand the two combine.

## Main definitions

* `Stacks.SheafOfModules.stalkAbFunctor`: the stalk of a sheaf of modules on a scheme at a point,
  as an abelian group, functorially.
* `Stacks.SheafOfModules.ModulesGlueData.stalkChartIso` and
  `Stacks.SheafOfModules.ModulesDirectedGlueData.stalkChartIso`: **the stalk of the glued sheaf at
  a point of a chart is the stalk of that chart's sheaf.**

## Main results

* `Stacks.SheafOfModules.ModulesGlueData.Hom.chartIso_glued` and its directed analogue: **the
  glued morphism, restricted along a chart, is the chart morphism** read through the comparison
  isomorphisms of the two glueing data.
* `Stacks.SheafOfModules.ModulesGlueData.stalkChartIso_naturality` and its directed analogue:
  **the stalk comparison is compatible with morphisms of glueing data.**
* `Stacks.SheafOfModules.shortExact_iff_forall_stalkAb`: short exactness of a complex of sheaves
  of modules on a scheme is short exactness of its complexes of abelian-group stalks.
* `Stacks.SheafOfModules.shortExact_of_forall_restrict`: **a complex of sheaves of modules whose
  restriction along every member of a covering family of open immersions is short exact is short
  exact.**
* `Stacks.SheafOfModules.ModulesDirectedGlueData.shortExact_glued`: **a complex of glued sheaves
  of modules is short exact as soon as all of its complexes of chart sheaves are**, for a
  covering family of charts.
* `Stacks.SheafOfModules.ModulesDirectedGlueData.Hom.glued_eq_zero`: a family of zero chart
  morphisms induces the zero morphism, which is what supplies the zero-composite witness of the
  glued complex.

## Implementation notes

**Abelian groups, not stalk modules.** The stalk comparison is stated for the *abelian-group*
stalks. That is forced: the stalk of a sheaf of modules on `S` at `f i y` is a module over
`𝒪_{S, f i y}` and the stalk of the chart sheaf at `y` is a module over `𝒪_{Y i, y}`, two
different rings, so a comparison of stalk modules could only be semilinear over the comparison of
the stalk rings, and Mathlib's `restrictStalkNatIso` — the input — is itself stated in
`AddCommGrpCat`. Nothing is lost for the purpose at hand: injectivity, surjectivity and
exactness of a map of stalk modules are properties of the underlying map of abelian groups, and
`AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap`,
`AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap` and
`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact` are exactly in that form.
(The semilinear comparison over a ringed space is
`StacksFrontier/Topology/Sheaves/Modules/StalkRestrictOpen.lean`; it is stated for
`restrictSheafOfModules` along an open embedding of topological spaces, not for
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, and bridging the two is not needed here.)

`Stacks.SheafOfModules.stalkAbFunctor X x` is `Scheme.Modules.toPresheaf X` followed by Mathlib's
abelian-group stalk functor. It is the same functor as
`AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x` — they are equal by
`rfl`, recorded as `stalkAbFunctor_eq` — and exists only because this is the spelling in which
`restrictStalkNatIso` is stated, so that the two compose without transport.

`AlgebraicGeometry.Scheme.Modules.restrictFunctor` carries no `Functor.Additive` instance in
Mathlib, which `ShortComplex.map` needs; it is supplied here by transport along
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

The covering hypothesis is asked for pointwise, as `∀ x : S, ∃ i y, f i y = x`, rather than as an
inequality of opens: that is the form in which it is consumed — a point of `S` is pushed into a
chart and the stalk comparison is applied there — and it is what an inequality
`⊤ ≤ ⨆ i, (f i).opensRange` unpacks to.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)

## Not done here

No Stacks tag is carried. Stacks 00AM is the glueing construction itself and says nothing about
stalks; Tag 01AG, that exactness of a complex of sheaves of modules is measured on stalks, is
already carried by `AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`, which is
used here rather than reproved.

Nothing here is about a relative projective spectrum.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Restriction of sheaves of modules along an open immersion is additive, being isomorphic to
the inverse image. -/
instance instAdditiveRestrictFunctor : (restrictFunctor f).Additive :=
  Functor.additive_of_iso (restrictFunctorIsoPullback f).symm

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.SheafOfModules

/-! ### Abelian-group stalks of sheaves of modules on a scheme -/

/-- The stalk at `x` of the presheaf of abelian groups underlying a sheaf of modules on a scheme,
as a functor. -/
abbrev stalkAbFunctor (X : Scheme.{u}) (x : X) : X.Modules ⥤ AddCommGrpCat.{u} :=
  Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

/-- The abelian-group stalk functor on sheaves of modules over a scheme is the one of
`StacksFrontier/Topology/Sheaves/Modules/Exactness.lean`, at the spelling in which Mathlib states
the comparison of stalks across a restriction. -/
theorem stalkAbFunctor_eq (X : Scheme.{u}) (x : X) :
    stalkAbFunctor X x =
      AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x := rfl

/-- The map on abelian-group stalks induced by a morphism of sheaves of modules is the one
induced on stalk modules. -/
theorem stalkAbFunctor_map_coe {X : Scheme.{u}} (x : X) {M N : X.Modules} (φ : M ⟶ N) :
    ⇑(ConcreteCategory.hom ((stalkAbFunctor X x).map φ)) =
      ⇑(AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x φ).hom := rfl

/-- **Short exactness of a complex of sheaves of modules on a scheme is short exactness of its
complexes of abelian-group stalks.** This is the module-level criterion of Tag 01AG for short
exactness rather than exactness; it is read off the three stalkwise criteria for exactness,
monomorphy and epimorphy. -/
theorem shortExact_iff_forall_stalkAb {X : Scheme.{u}} (C : ShortComplex X.Modules) :
    C.ShortExact ↔ ∀ x : X, (C.map (stalkAbFunctor X x)).ShortExact := by
  refine ⟨fun hC x => ?_, fun h => ?_⟩
  · refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
        X.ringCatSheaf C).1 hC.exact x
    · rw [AddCommGrpCat.mono_iff_injective]
      exact (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap C.f).1 hC.mono_f x
    · rw [AddCommGrpCat.epi_iff_surjective]
      exact (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap C.g).1 hC.epi_g x
  · refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
        X.ringCatSheaf C).2 fun x => (h x).exact
    · refine (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap C.f).2 fun x => ?_
      exact (AddCommGrpCat.mono_iff_injective _).1 (h x).mono_f
    · refine (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap C.g).2 fun x => ?_
      exact (AddCommGrpCat.epi_iff_surjective _).1 (h x).epi_g

section Cover

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
  [∀ i, IsOpenImmersion (f i)]

/-- **A complex of sheaves of modules whose restriction along every chart of a covering family of
open immersions is short exact is itself short exact.** Short exactness is measured on stalks, and
the stalk at a point of `S` lying in the `i`-th chart is the stalk of the restriction to that
chart at the point above it, by
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`. -/
theorem shortExact_of_forall_restrict (C : ShortComplex S.Modules)
    (hcov : ∀ x : S, ∃ (i : ι) (y : Y i), (f i) y = x)
    (h : ∀ i, (C.map (Scheme.Modules.restrictFunctor (f i))).ShortExact) :
    C.ShortExact := by
  refine (shortExact_iff_forall_stalkAb C).2 fun x => ?_
  obtain ⟨i, y, rfl⟩ := hcov x
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.mapNatIso C (Scheme.Modules.restrictStalkNatIso (f i) y))
    ((shortExact_iff_forall_stalkAb (C.map (Scheme.Modules.restrictFunctor (f i)))).1 (h i) y)

end Cover

/-! ### Morphisms of glueing data on the charts -/

namespace OModuleGlueData

variable {X : TopCat.{u}} {O : TopCat.Sheaf RingCat.{u} X} {ι : Type u} {U : ι → Opens X}

attribute [local instance] sectionsProductModule

/-- **A family of zero chart morphisms induces the zero morphism of glued sheaves.** -/
theorem Hom.glued_eq_zero {D E : OModuleGlueData O U} (τ : Hom D E)
    (h : ∀ (i : ι) {V : Opens X} (hV : V ≤ U i) (s : (D.sheaf i).obj V hV),
      τ.app i hV s = 0) :
    τ.glued = 0 :=
  _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun s =>
      Subtype.ext (funext fun i => h i inf_le_right (s.1 i))))

end OModuleGlueData

section Scheme

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ S}
  [∀ i, IsOpenImmersion (f i)]

namespace ModulesGlueData

/-- The comparison isomorphism of the glued sheaf with the `i`-th chart sheaf, read on sections
over an open of the `i`-th chart: the identification of the sections of the glued sheaf over the
image open, followed by restriction along the identification of that image's preimage with the
open itself. -/
theorem chartIso_hom_app (D : ModulesGlueData S f) (i : ι) (V : (Y i).Opens)
    (x : ToType (D.glued.val.obj (op (f i ''ᵁ V)))) :
    ((D.chartIso i).hom.val.app (op V)).hom x =
      (D.mod i).val.presheaf.map (eqToHom ((f i).preimage_image_eq V).symm).op
        ((D.chartSectionsIso i ((f i).image_le_opensRange V)).hom x) := rfl

namespace Hom

variable {D E : ModulesGlueData S f}

/-- **The glued morphism, restricted along the `i`-th chart, is the `i`-th chart morphism**, read
through the comparison isomorphisms `chartIso` of the two glueing data with their chart sheaves. -/
theorem chartIso_glued (τ : Hom D E) (i : ι) :
    (Scheme.Modules.restrictFunctor (f i)).map τ.glued ≫ (E.chartIso i).hom =
      (D.chartIso i).hom ≫ τ.chart i := by
  ext V x
  show (E.mod i).val.presheaf.map (eqToHom ((f i).preimage_image_eq V).symm).op
      ((E.chartSectionsIso i ((f i).image_le_opensRange V)).hom
        ((τ.glued.val.app (op (f i ''ᵁ V))).hom x))
    = ((τ.chart i).val.app (op V)).hom
      ((D.mod i).val.presheaf.map (eqToHom ((f i).preimage_image_eq V).symm).op
        ((D.chartSectionsIso i ((f i).image_le_opensRange V)).hom x))
  rw [τ.chartSectionsIso_glued i ((f i).image_le_opensRange V) x]
  exact (PresheafOfModules.naturality_apply (τ.chart i).val
    (eqToHom ((f i).preimage_image_eq V).symm).op _).symm

/-- **A family of zero chart morphisms induces the zero morphism of glued sheaves.** -/
theorem glued_eq_zero (τ : Hom D E) (h : ∀ i, τ.chart i = 0) : τ.glued = 0 := by
  refine τ.toOModuleGlueHom.glued_eq_zero ?_
  intro i V hV s
  have e : (Scheme.Modules.pushforward (f i)).map (τ.chart i) = 0 := by
    rw [h i]
    exact (Scheme.Modules.pushforward (f i)).map_zero _ _
  exact congrArg (fun φ : (Scheme.Modules.pushforward (f i)).obj (D.mod i) ⟶
    (Scheme.Modules.pushforward (f i)).obj (E.mod i) => (φ.val.app (op V)).hom s) e

end Hom

/-- **The stalk of the glued sheaf of modules at a point of the `i`-th chart is the stalk of the
`i`-th chart's sheaf** at that point: the glued sheaf restricted along the chart is the chart
sheaf, and restriction along an open immersion does not change stalks. -/
def stalkChartIso (D : ModulesGlueData S f) (i : ι) (y : Y i) :
    (stalkAbFunctor S ((f i) y)).obj D.glued ≅ (stalkAbFunctor (Y i) y).obj (D.mod i) :=
  ((Scheme.Modules.restrictStalkNatIso (f i) y).app D.glued).symm ≪≫
    (stalkAbFunctor (Y i) y).mapIso (D.chartIso i)

/-- **The stalk comparison is compatible with morphisms of glueing data**: the map on stalks
induced by a glued morphism is, through the comparisons, the map induced by its chart morphism. -/
theorem stalkChartIso_naturality {D E : ModulesGlueData S f} (τ : Hom D E) (i : ι) (y : Y i) :
    (stalkAbFunctor S ((f i) y)).map τ.glued ≫ (E.stalkChartIso i y).hom =
      (D.stalkChartIso i y).hom ≫ (stalkAbFunctor (Y i) y).map (τ.chart i) := by
  have hnat : (stalkAbFunctor S ((f i) y)).map τ.glued ≫
      ((Scheme.Modules.restrictStalkNatIso (f i) y).app E.glued).inv =
      ((Scheme.Modules.restrictStalkNatIso (f i) y).app D.glued).inv ≫
        (stalkAbFunctor (Y i) y).map ((Scheme.Modules.restrictFunctor (f i)).map τ.glued) :=
    (Scheme.Modules.restrictStalkNatIso (f i) y).inv.naturality τ.glued
  simp only [stalkChartIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp, τ.chartIso_glued i,
    Functor.map_comp]

end ModulesGlueData

namespace ModulesDirectedGlueData

variable [Preorder ι]

namespace Hom

variable {D E : ModulesDirectedGlueData S f}

/-- **The glued morphism, restricted along the `i`-th chart, is the `i`-th chart morphism**, read
through the comparison isomorphisms of the two glueing data with their chart sheaves. -/
theorem chartIso_glued (τ : Hom D E) (i : ι) :
    (Scheme.Modules.restrictFunctor (f i)).map τ.glued ≫ (E.chartIso i).hom =
      (D.chartIso i).hom ≫ τ.chart i :=
  τ.toModulesGlueHom.chartIso_glued i

/-- **A family of zero chart morphisms induces the zero morphism of glued sheaves.** -/
theorem glued_eq_zero (τ : Hom D E) (h : ∀ i, τ.chart i = 0) : τ.glued = 0 :=
  τ.toModulesGlueHom.glued_eq_zero fun i => h i

end Hom

/-- **The stalk of the glued sheaf of modules at a point of the `i`-th chart is the stalk of the
`i`-th chart's sheaf** at that point. -/
def stalkChartIso (D : ModulesDirectedGlueData S f) (i : ι) (y : Y i) :
    (stalkAbFunctor S ((f i) y)).obj D.glued ≅ (stalkAbFunctor (Y i) y).obj (D.mod i) :=
  D.toModulesGlueData.stalkChartIso i y

/-- **The stalk comparison is compatible with morphisms of locally directed glueing data.** -/
theorem stalkChartIso_naturality {D E : ModulesDirectedGlueData S f} (τ : Hom D E) (i : ι)
    (y : Y i) :
    (stalkAbFunctor S ((f i) y)).map τ.glued ≫ (E.stalkChartIso i y).hom =
      (D.stalkChartIso i y).hom ≫ (stalkAbFunctor (Y i) y).map (τ.chart i) :=
  ModulesGlueData.stalkChartIso_naturality τ.toModulesGlueHom i y

/-- Restriction to sections of a composite of chart morphisms. -/
theorem chartSec_comp {D E F : ModulesDirectedGlueData S f} (a : ∀ i, D.mod i ⟶ E.mod i)
    (b : ∀ i, E.mod i ⟶ F.mod i) (i : ι) (V : S.Opens)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    chartSec (fun k => a k ≫ b k) i V t = chartSec b i V (chartSec a i V t) :=
  congrArg (fun φ : (Scheme.Modules.pushforward (f i)).obj (D.mod i) ⟶
      (Scheme.Modules.pushforward (f i)).obj (F.mod i) => (φ.val.app (op V)).hom t)
    ((Scheme.Modules.pushforward (f i)).map_comp (a i) (b i))

/-- **The composite of two morphisms of locally directed glueing data.** -/
def Hom.comp {D E F : ModulesDirectedGlueData S f} (τ : Hom D E) (σ : Hom E F) : Hom D F where
  chart i := τ.chart i ≫ σ.chart i
  chart_trans := fun {i j} hij V hV t =>
    ((chartSec_comp τ.chart σ.chart j V (D.trans hij hV t)).trans
      ((congrArg (chartSec σ.chart j V) (τ.chart_trans hij hV t)).trans
        (σ.chart_trans hij hV (chartSec τ.chart i V t)))).trans
      (congrArg (fun z => F.trans hij hV z)
        (chartSec_comp τ.chart σ.chart i V t).symm)

/-- The `i`-th chart morphism of a composite is the composite of the `i`-th chart morphisms. -/
@[simp] theorem Hom.comp_chart {D E F : ModulesDirectedGlueData S f} (τ : Hom D E) (σ : Hom E F)
    (i : ι) : (τ.comp σ).chart i = τ.chart i ≫ σ.chart i := rfl

/-- **The glued morphism of a composite is the composite of the glued morphisms.** -/
theorem Hom.glued_comp {D E F : ModulesDirectedGlueData S f} (τ : Hom D E) (σ : Hom E F) :
    (τ.comp σ).glued = τ.glued ≫ σ.glued :=
  τ.glued_eq_comp σ (τ.comp σ) fun _ => rfl

/-- The complex of glued sheaves of modules attached to a composable pair of morphisms of locally
directed glueing data whose chart morphisms compose to zero. -/
def gluedShortComplex {D E F : ModulesDirectedGlueData S f} (τ : Hom D E) (σ : Hom E F)
    (h : ∀ i, τ.chart i ≫ σ.chart i = 0) : ShortComplex S.Modules :=
  ShortComplex.mk τ.glued σ.glued ((τ.glued_comp σ).symm.trans ((τ.comp σ).glued_eq_zero h))

/-- The complex of chart sheaves attached to such a pair, on the `i`-th chart. -/
def chartShortComplex {D E F : ModulesDirectedGlueData S f} (τ : Hom D E) (σ : Hom E F)
    (h : ∀ i, τ.chart i ≫ σ.chart i = 0) (i : ι) : ShortComplex (Y i).Modules :=
  ShortComplex.mk (τ.chart i) (σ.chart i) (h i)

/-- **The complex of glued sheaves, restricted along the `i`-th chart, is the complex of chart
sheaves there.** -/
def restrictGluedShortComplexIso {D E F : ModulesDirectedGlueData S f} (τ : Hom D E)
    (σ : Hom E F) (h : ∀ i, τ.chart i ≫ σ.chart i = 0) (i : ι) :
    (gluedShortComplex τ σ h).map (Scheme.Modules.restrictFunctor (f i)) ≅
      chartShortComplex τ σ h i :=
  ShortComplex.isoMk (D.chartIso i) (E.chartIso i) (F.chartIso i)
    (τ.chartIso_glued i).symm (σ.chartIso_glued i).symm

/-- **A complex of glued sheaves of modules is short exact as soon as its complexes of chart
sheaves are**, for a covering family of charts. Short exactness is measured on stalks, and the
stalk of the glued sheaf at a point of a chart is the stalk of that chart's sheaf. -/
theorem shortExact_glued {D E F : ModulesDirectedGlueData S f} (τ : Hom D E) (σ : Hom E F)
    (h : ∀ i, τ.chart i ≫ σ.chart i = 0)
    (hcov : ∀ x : S, ∃ (i : ι) (y : Y i), (f i) y = x)
    (hchart : ∀ i, (chartShortComplex τ σ h i).ShortExact) :
    (gluedShortComplex τ σ h).ShortExact :=
  shortExact_of_forall_restrict f _ hcov fun i =>
    ShortComplex.shortExact_of_iso (restrictGluedShortComplexIso τ σ h i).symm (hchart i)

end ModulesDirectedGlueData

end Scheme

end Stacks.SheafOfModules

end
