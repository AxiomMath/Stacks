module

public import StacksFrontier.AlgebraicGeometry.AffineOpensDirectedGlue
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueChartAdjunct
public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiHomAmalgamation
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# Morphisms between sheaves of modules glued from the affine opens of a scheme

`AlgebraicGeometry.AffineOpensGlue.ChartComparison` glues a sheaf of modules on a scheme `X` out
of a sheaf of modules on each affine open together with a comparison isomorphism for each
inclusion of affine opens. This file does the same for *morphisms*: a family of morphisms on the
charts, one for each affine open, commuting with the comparisons, assembles into a single morphism
of the glued modules, and that morphism is the only one which restricts to the family.

The two corollaries are what make the construction functorial — the family of identities glues to
the identity, and the family of composites glues to the composite — and together they turn a
compatible family of *isomorphisms* on the charts into an isomorphism of the glued modules.

## Main definitions

* `AlgebraicGeometry.AffineOpensGlue.pushRes`: the pushforward along the chart of an affine open of
  a morphism of sheaves of modules there, restricted to an open of `X`. This is the shape in which
  a morphism on a chart is compared with the comparison isomorphisms of the glueing datum.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.IsCompatible`: **the compatibility condition**
  on a family of morphisms on the charts: for each inclusion `V ≤ W` of affine opens the square
  formed by the two comparisons and the pushforwards of the morphisms at `V` and at `W` commutes.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.localHom`: the morphism of the restrictions
  to a chart that a member of the family defines, read through the chart isomorphisms.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueHom`: **the glued morphism** of the two
  glued sheaves of modules.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueIso`: **the glued isomorphism**, from a
  compatible family of isomorphisms on the charts.

## Main results

* `AlgebraicGeometry.AffineOpensGlue.localApp_restrictFunctor_map`: the sections map over an open
  `O ≤ W` of the restriction to `W` of a morphism of sheaves of modules on `X` is the component of
  that morphism at `O`. This is what makes every sections map below computable.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.localAppFun_comp_chartSec`: **reading a
  section of the glued module on a chart and comparing it upwards gives the reading on the larger
  chart.** This is the functoriality of the glueing datum, read through the transposed chart
  isomorphism.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.localApp_localHom_eq`: **the local morphisms
  agree over an open contained in two charts.** This is the hypothesis that
  `AlgebraicGeometry.exists_hom_of_localHoms` consumes, and it is where local directedness of the
  affine opens is used.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueHom_chartIso`: **the characterisation of
  the glued morphism**: on each chart it is the member of the family, under the chart
  isomorphisms.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.eq_glueHom`: **uniqueness**: a morphism of the
  glued modules satisfying that characterisation is the glued morphism.
* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueHom_id` and
  `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueHom_comp`: the glued morphism is
  functorial in the family.

## Implementation notes

The glued morphism is produced by `AlgebraicGeometry.exists_hom_of_localHoms` — the Zariski
glueing of a morphism of sheaves of modules from morphisms of its restrictions to the members of
an open covering — applied to the covering of `X` by its affine opens. That tool asks only for the
agreement of the sections maps over an open contained in two members, so neither additivity nor
linearity of the glued morphism has to be checked by hand; and it characterises the result by its
restrictions, which is exactly `glueHom_chartIso`.

Everything is computed on sections through `AlgebraicGeometry.localAppFun`, and three auxiliary
spellings keep the statements in one and the same form, so that `rw` matches them: `pushRes` for
the restricted pushforward of a morphism on a chart, `pushSec` for its sections map, and
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartSec` for reading a section of the glued
module on a chart. The last one is the *transposed* chart isomorphism
`Stacks.SheafOfModules.ModulesGlueData.chartAdjunct`, a morphism of sheaves of modules on `X`
rather than on a chart, which is what lets its sections map be a plain component `app`; its
restriction to the chart is the chart isomorphism followed by the counit of the restriction
adjunction, and that is `chartHomIso`.

The agreement of the local morphisms over an open `O` contained in two affine opens is local on
`O`: by `AlgebraicGeometry.AffineOpensGlue.locallyDirected` every point of `O` lies in an affine
open below both, and over an open contained in such an affine open the two local morphisms agree
because each of them agrees with the one attached to the smaller chart
(`localAppFun_localHom_eq_of_le`). The separation half of the sheaf condition for the second glued
module then propagates the agreement to `O`.

## References

* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Lemma 6.33.1 (Tag 04TN)](https://stacks.math.columbia.edu/tag/04TN)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.AffineOpensGlue

variable {X : Scheme.{u}}

/-! ### Sections maps of a restricted global morphism -/

/-- Conjugating the component at an open `P` of a morphism of sheaves of modules on `X` by a pair
of restriction maps between `O` and `P` gives its component at `O`. -/
theorem app_conj_eq {A B : X.Modules} (g : A ⟶ B) {O P : X.Opens} (a : op O ⟶ op P)
    (b : op P ⟶ op O) : A.presheaf.map a ≫ g.app P ≫ B.presheaf.map b = g.app O := by
  have hnat : A.presheaf.map a ≫ g.app P = g.app O ≫ B.presheaf.map a :=
    g.mapPresheaf.naturality a
  rw [← Category.assoc, hnat, Category.assoc, presheaf_map_comp₂ B a b (𝟙 _),
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The sections map over an open `O ≤ W` of the restriction to `W` of a morphism of sheaves of
modules on `X` is the component of that morphism at `O`.**
`AlgebraicGeometry.localApp_restrictFunctor_map_image` is the case of an open of the form
`W.ι ''ᵁ U`; for an arbitrary `O ≤ W` the two restriction maps in `AlgebraicGeometry.localApp`
cancel against each other by the naturality of the morphism. -/
theorem localApp_restrictFunctor_map {A B : X.Modules} {O W : X.Opens} (g : A ⟶ B) (hO : O ≤ W) :
    localApp ((Scheme.Modules.restrictFunctor W.ι).map g) O hO = g.app O := by
  rw [localApp, restrictFunctor_map_app]
  simp only [Scheme.Modules.restrictAppIso, Iso.refl_inv, Iso.refl_hom]
  exact app_conj_eq g _ _

/-- `AlgebraicGeometry.AffineOpensGlue.localApp_restrictFunctor_map`, read on an individual
section. -/
theorem localAppFun_restrictFunctor_map {A B : X.Modules} {O W : X.Opens} (g : A ⟶ B)
    (hO : O ≤ W) (s : ToType (A.val.obj (op O))) :
    localAppFun ((Scheme.Modules.restrictFunctor W.ι).map g) O hO s = g.app O s :=
  congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _))
    (localApp_restrictFunctor_map g hO)) s

/-! ### The affine opens as a covering family -/

/-- An open contained in an affine open is contained in the range of its chart. This is the
converse of `AlgebraicGeometry.AffineOpensGlue.le_of_le_opensRange_chart`. -/
theorem le_opensRange_chart_of_le {V : X.affineOpens} {O : X.Opens}
    (hO : O ≤ (V.1 : X.Opens)) : O ≤ (chart X V).opensRange := by
  rw [opensRange_chart]
  exact hO

/-- Every point of a scheme lies in an affine open. This is
`AlgebraicGeometry.AffineOpensGlue.isOpenCover_affineOpens` in the pointwise form that
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover` asks for. -/
theorem exists_mem_affineOpens (x : X) : ∃ V : X.affineOpens, x ∈ (V.1 : X.Opens) := by
  have hx : x ∈ (⨆ V : X.affineOpens, (V.1 : X.Opens) : X.Opens) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

/-! ### Pushing a morphism on a chart forward -/

/-- **The pushforward along the chart of an affine open `W` of a morphism of sheaves of modules on
that chart, restricted to an open `O` of `X`.** This is the shape in which a morphism on a chart
is composed with the comparison isomorphisms of a chart comparison, which live on the restrictions
of the pushforwards. -/
abbrev pushRes (O : X.Opens) (W : X.affineOpens)
    {M N : ((W.1 : X.Opens) : Scheme.{u}).Modules} (α : M ⟶ N) :
    Scheme.Modules.restrict ((Scheme.Modules.pushforward (chart X W)).obj M) O.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pushforward (chart X W)).obj N) O.ι :=
  (Scheme.Modules.restrictFunctor O.ι).map ((Scheme.Modules.pushforward (chart X W)).map α)

/-- `AlgebraicGeometry.AffineOpensGlue.pushRes` is unital. -/
theorem pushRes_id (O : X.Opens) (W : X.affineOpens)
    (M : ((W.1 : X.Opens) : Scheme.{u}).Modules) : pushRes O W (𝟙 M) = 𝟙 _ := by
  simp only [pushRes, CategoryTheory.Functor.map_id]

/-- `AlgebraicGeometry.AffineOpensGlue.pushRes` is multiplicative. -/
theorem pushRes_comp (O : X.Opens) (W : X.affineOpens)
    {M N P : ((W.1 : X.Opens) : Scheme.{u}).Modules} (α : M ⟶ N) (β : N ⟶ P) :
    pushRes O W (α ≫ β) = pushRes O W α ≫ pushRes O W β := by
  simp only [pushRes, Functor.map_comp]

/-- `AlgebraicGeometry.AffineOpensGlue.pushRes` carries an isomorphism of sheaves of modules on a
chart to an isomorphism. -/
theorem pushRes_hom_inv_id (O : X.Opens) (W : X.affineOpens)
    {M N : ((W.1 : X.Opens) : Scheme.{u}).Modules} (e : M ≅ N) :
    pushRes O W e.hom ≫ pushRes O W e.inv = 𝟙 _ := by
  rw [← pushRes_comp, e.hom_inv_id, pushRes_id]

/-- `AlgebraicGeometry.AffineOpensGlue.pushRes_hom_inv_id` in the other order. -/
theorem pushRes_inv_hom_id (O : X.Opens) (W : X.affineOpens)
    {M N : ((W.1 : X.Opens) : Scheme.{u}).Modules} (e : M ≅ N) :
    pushRes O W e.inv ≫ pushRes O W e.hom = 𝟙 _ := by
  rw [← pushRes_comp, e.inv_hom_id, pushRes_id]

/-- The sections map over an open `O` of `X` of the pushforward along the chart of `W` of a
morphism of sheaves of modules on that chart. -/
def pushSec (W : X.affineOpens) {M N : ((W.1 : X.Opens) : Scheme.{u}).Modules} (α : M ⟶ N)
    (O : X.Opens)
    (s : ToType (((Scheme.Modules.pushforward (chart X W)).obj M).val.obj (op O))) :
    ToType (((Scheme.Modules.pushforward (chart X W)).obj N).val.obj (op O)) :=
  ((Scheme.Modules.pushforward (chart X W)).map α).app O s

/-- The sections map of `AlgebraicGeometry.AffineOpensGlue.pushRes` over any open contained in the
open it was restricted to is `AlgebraicGeometry.AffineOpensGlue.pushSec`: it does not depend on
that open. -/
theorem localAppFun_pushRes {O P : X.Opens} (W : X.affineOpens)
    {M N : ((W.1 : X.Opens) : Scheme.{u}).Modules} (α : M ⟶ N) (hO : O ≤ P)
    (s : ToType (((Scheme.Modules.pushforward (chart X W)).obj M).val.obj (op O))) :
    localAppFun (pushRes P W α) O hO s = pushSec W α O s :=
  localAppFun_restrictFunctor_map _ hO s

namespace ChartComparison

variable (D D' : ChartComparison X)

/-! ### Reading a section of the glued module on a chart -/

/-- **The chart isomorphism of the glued module, transposed into a morphism of sheaves of modules
on `X`**: it lands in the pushforward along the chart of the member of the family there. Being a
morphism on `X`, its sections maps are plain components, which is why every computation below goes
through it rather than through
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartIso` directly. -/
def chartHom (V : X.affineOpens) :
    D.glued ⟶ (Scheme.Modules.pushforward (chart X V)).obj (D.mod V) :=
  D.toGlueData.toModulesGlueData.chartAdjunct V

/-- The restriction to the chart of `V` of
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartHom` is the chart isomorphism followed by
the inverse of the counit of the restriction adjunction. In particular it is an isomorphism. -/
theorem restrictFunctor_map_chartHom (V : X.affineOpens) :
    (Scheme.Modules.restrictFunctor (chart X V)).map (D.chartHom V) =
      (D.chartIso V).hom ≫
        ((Scheme.Modules.restrictFunctorAdjCounitIso (chart X V)).app (D.mod V)).inv := by
  refine (Iso.eq_comp_inv _).mpr ?_
  exact D.toGlueData.toModulesGlueData.restrictFunctor_map_chartAdjunct V

/-- The restriction to the chart of `V` of
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartHom`, as an isomorphism of the restriction
of the glued module with the restriction of the pushforward of the member of the family. -/
def chartHomIso (V : X.affineOpens) :
    Scheme.Modules.restrict D.glued (chart X V) ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward (chart X V)).obj (D.mod V))
        (chart X V) :=
  D.chartIso V ≪≫
    ((Scheme.Modules.restrictFunctorAdjCounitIso (chart X V)).app (D.mod V)).symm

/-- `AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartHomIso` is the restriction of
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartHom`. -/
theorem chartHomIso_hom (V : X.affineOpens) :
    (D.chartHomIso V).hom = (Scheme.Modules.restrictFunctor (chart X V)).map (D.chartHom V) :=
  (D.restrictFunctor_map_chartHom V).symm

/-- **Reading a section of the glued module over an open `O` on the chart of `V`.** -/
def chartSec (V : X.affineOpens) (O : X.Opens) (x : ToType (D.glued.val.obj (op O))) :
    ToType (((Scheme.Modules.pushforward (chart X V)).obj (D.mod V)).val.obj (op O)) :=
  (D.chartHom V).app O x

/-- The sections map of `AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartHomIso` is
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartSec`. -/
theorem localAppFun_chartHomIso_hom (V : X.affineOpens) {O : X.Opens}
    (hO : O ≤ (V.1 : X.Opens)) (x : ToType (D.glued.val.obj (op O))) :
    localAppFun (D.chartHomIso V).hom O hO x = D.chartSec V O x := by
  have h := D.chartHomIso_hom V
  rw [h]
  exact localAppFun_restrictFunctor_map _ hO x

/-- Reading a section of the glued module on a chart is undone by the inverse of
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartHomIso`. -/
theorem localAppFun_chartHomIso_inv_chartSec (V : X.affineOpens) {O : X.Opens}
    (hO : O ≤ (V.1 : X.Opens)) (x : ToType (D.glued.val.obj (op O))) :
    localAppFun (D.chartHomIso V).inv O hO (D.chartSec V O x) = x := by
  rw [← D.localAppFun_chartHomIso_hom V hO x, ← localAppFun_comp, (D.chartHomIso V).hom_inv_id,
    localAppFun_id]

/-- `AlgebraicGeometry.AffineOpensGlue.ChartComparison.localAppFun_chartHomIso_inv_chartSec` in
the other order. -/
theorem chartSec_localAppFun_chartHomIso_inv (V : X.affineOpens) {O : X.Opens}
    (hO : O ≤ (V.1 : X.Opens))
    (y : ToType (((Scheme.Modules.pushforward (chart X V)).obj (D.mod V)).val.obj (op O))) :
    D.chartSec V O (localAppFun (D.chartHomIso V).inv O hO y) = y := by
  rw [← D.localAppFun_chartHomIso_hom V hO, ← localAppFun_comp, (D.chartHomIso V).inv_hom_id,
    localAppFun_id]

/-- **The pairwise transition of the glueing datum, between two charts ordered by inclusion, is
the sections map of the comparison attached to that inclusion.** The pairwise transition is glued
from the comparisons through the charts below both; passing through the smaller of the two charts
itself leaves only one leg of that comparison, by
`Stacks.SheafOfModules.ModulesDirectedGlueData.trans_rfl`. -/
theorem toModulesGlueData_trans_eq {V W : X.affineOpens} (h : V ≤ W) {O : X.Opens}
    (hV : O ≤ (chart X V).opensRange) (hW : O ≤ (chart X W).opensRange)
    (t : ToType (openSections (chart X V) (D.mod V) O)) :
    D.toGlueData.toModulesGlueData.trans V W hV hW t
      = localAppFun (D.comp h).hom O (le_of_le_opensRange_chart hV) t := by
  have h0 : (D.toGlueData.trans (le_refl V) hV).symm t = t :=
    (D.toGlueData.trans (le_refl V) hV).injective
      (((D.toGlueData.trans (le_refl V) hV).apply_symm_apply t).trans
        (D.toGlueData.trans_rfl hV t).symm)
  have h1 : D.toGlueData.toModulesGlueData.trans V W hV hW t
      = D.toGlueData.pairEquiv V le_rfl h hV t :=
    D.toGlueData.pairTrans_eq V W le_rfl h hV t
  have h2 : D.toGlueData.pairEquiv V le_rfl h hV t
      = D.toGlueData.trans h hV ((D.toGlueData.trans (le_refl V) hV).symm t) :=
    D.toGlueData.pairEquiv_apply V le_rfl h hV t
  have h3 : D.toGlueData.trans h hV ((D.toGlueData.trans (le_refl V) hV).symm t)
      = D.toGlueData.trans h hV t := congrArg (D.toGlueData.trans h hV) h0
  exact h1.trans (h2.trans h3)

/-- **Reading a section of the glued module on a chart and comparing it upwards gives the reading
on the larger chart.** This is the functoriality of the glueing datum, read through
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartHom`. -/
theorem localAppFun_comp_chartSec {V W : X.affineOpens} (h : V ≤ W) {O : X.Opens}
    (hO : O ≤ (V.1 : X.Opens)) (x : ToType (D.glued.val.obj (op O))) :
    localAppFun (D.comp h).hom O hO (D.chartSec V O x) = D.chartSec W O x := by
  have hV : O ≤ (chart X V).opensRange := le_opensRange_chart_of_le hO
  have hW : O ≤ (chart X W).opensRange := le_opensRange_chart_of_le (hO.trans h)
  exact (D.toModulesGlueData_trans_eq h hV hW (D.chartSec V O x)).symm.trans
    (D.toGlueData.toModulesGlueData.trans_chartAdjunct V W hV hW x)

/-! ### A compatible family of morphisms on the charts -/

variable {D D'}

/-- **A family of morphisms on the charts is compatible with the comparisons** when, for every
inclusion `V ≤ W` of affine opens, the square formed by the comparison of `D` at that inclusion,
the comparison of `D'` at that inclusion, and the pushforwards of the members of the family at `V`
and at `W` — all restricted to the smaller chart, where all four are defined — commutes. -/
def IsCompatible (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V) : Prop :=
  ∀ {V W : X.affineOpens} (h : V ≤ W),
    (D.comp h).hom ≫ pushRes (V.1 : X.Opens) W (α W)
      = pushRes (V.1 : X.Opens) V (α V) ≫ (D'.comp h).hom

variable (D D')

/-- The morphism of the restrictions of the two glued modules to the chart of `V` that the member
of the family at `V` defines, read through the chart isomorphisms. -/
def localHom (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V) (V : X.affineOpens) :
    Scheme.Modules.restrict D.glued (chart X V) ⟶
      Scheme.Modules.restrict D'.glued (chart X V) :=
  (D.chartIso V).hom ≫ α V ≫ (D'.chartIso V).inv

/-- `AlgebraicGeometry.AffineOpensGlue.ChartComparison.localHom`, read through the transposed
chart isomorphisms. The counits of the restriction adjunction cancel against the pushforward of
the member of the family, by the naturality of the counit. -/
theorem localHom_eq (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V) (V : X.affineOpens) :
    D.localHom D' α V =
      (D.chartHomIso V).hom ≫ pushRes (V.1 : X.Opens) V (α V) ≫ (D'.chartHomIso V).inv := by
  have hnat : pushRes (V.1 : X.Opens) V (α V) ≫
      ((Scheme.Modules.restrictFunctorAdjCounitIso (chart X V)).app (D'.mod V)).hom =
      ((Scheme.Modules.restrictFunctorAdjCounitIso (chart X V)).app (D.mod V)).hom ≫ α V :=
    (Scheme.Modules.restrictFunctorAdjCounitIso (chart X V)).hom.naturality (α V)
  rw [localHom, chartHomIso, chartHomIso]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [← Category.assoc (pushRes (V.1 : X.Opens) V (α V)), hnat, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- The sections map of `AlgebraicGeometry.AffineOpensGlue.ChartComparison.localHom`: read the
section on the chart, push it forward along the member of the family, and read the result back as
a section of the second glued module. -/
theorem localAppFun_localHom (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V) (V : X.affineOpens)
    {O : X.Opens} (hO : O ≤ (V.1 : X.Opens)) (x : ToType (D.glued.val.obj (op O))) :
    localAppFun (D.localHom D' α V) O hO x
      = localAppFun (D'.chartHomIso V).inv O hO (pushSec V (α V) O (D.chartSec V O x)) :=
  calc localAppFun (D.localHom D' α V) O hO x
      = localAppFun ((D.chartHomIso V).hom ≫ pushRes (V.1 : X.Opens) V (α V) ≫
          (D'.chartHomIso V).inv) O hO x :=
        congrArg (fun φ => localAppFun φ O hO x) (D.localHom_eq D' α V)
    _ = localAppFun (pushRes (V.1 : X.Opens) V (α V) ≫ (D'.chartHomIso V).inv) O hO
          (localAppFun (D.chartHomIso V).hom O hO x) := localAppFun_comp _ _ O hO x
    _ = localAppFun (D'.chartHomIso V).inv O hO
          (localAppFun (pushRes (V.1 : X.Opens) V (α V)) O hO
            (localAppFun (D.chartHomIso V).hom O hO x)) := localAppFun_comp _ _ O hO _
    _ = localAppFun (D'.chartHomIso V).inv O hO
          (localAppFun (pushRes (V.1 : X.Opens) V (α V)) O hO (D.chartSec V O x)) :=
        congrArg (fun z => localAppFun (D'.chartHomIso V).inv O hO
            (localAppFun (pushRes (V.1 : X.Opens) V (α V)) O hO z))
          (D.localAppFun_chartHomIso_hom V hO x)
    _ = localAppFun (D'.chartHomIso V).inv O hO (pushSec V (α V) O (D.chartSec V O x)) :=
        congrArg (fun z => localAppFun (D'.chartHomIso V).inv O hO z)
          (localAppFun_pushRes V (α V) hO _)

/-- **The compatibility condition, read on sections.** -/
theorem pushSec_localAppFun_comp {α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V}
    (hα : IsCompatible α) {V W : X.affineOpens} (h : V ≤ W) {O : X.Opens}
    (hO : O ≤ (V.1 : X.Opens)) (s : ToType (openSections (chart X V) (D.mod V) O)) :
    pushSec W (α W) O (localAppFun (D.comp h).hom O hO s)
      = localAppFun (D'.comp h).hom O hO (pushSec V (α V) O s) :=
  calc pushSec W (α W) O (localAppFun (D.comp h).hom O hO s)
      = localAppFun (pushRes (V.1 : X.Opens) W (α W)) O hO
          (localAppFun (D.comp h).hom O hO s) := (localAppFun_pushRes W (α W) hO _).symm
    _ = localAppFun ((D.comp h).hom ≫ pushRes (V.1 : X.Opens) W (α W)) O hO s :=
        (localAppFun_comp _ _ O hO s).symm
    _ = localAppFun (pushRes (V.1 : X.Opens) V (α V) ≫ (D'.comp h).hom) O hO s :=
        congrArg (fun φ => localAppFun φ O hO s) (hα h)
    _ = localAppFun (D'.comp h).hom O hO
          (localAppFun (pushRes (V.1 : X.Opens) V (α V)) O hO s) := localAppFun_comp _ _ O hO s
    _ = localAppFun (D'.comp h).hom O hO (pushSec V (α V) O s) :=
        congrArg (fun z => localAppFun (D'.comp h).hom O hO z) (localAppFun_pushRes V (α V) hO s)

/-- **The local morphism attached to a chart agrees with the one attached to a larger chart**, on
sections over an open contained in the smaller one. This is the compatibility condition, read on
sections and conjugated by the chart isomorphisms. -/
theorem localAppFun_localHom_eq_of_le {α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V}
    (hα : IsCompatible α) {V W : X.affineOpens} (h : V ≤ W) {O : X.Opens}
    (hO : O ≤ (V.1 : X.Opens)) (x : ToType (D.glued.val.obj (op O))) :
    localAppFun (D.localHom D' α V) O hO x
      = localAppFun (D.localHom D' α W) O (hO.trans h) x := by
  have hA : ∀ (U : X.affineOpens) (hU : O ≤ (U.1 : X.Opens)),
      D'.chartSec U O (localAppFun (D.localHom D' α U) O hU x)
        = pushSec U (α U) O (D.chartSec U O x) := fun U hU =>
    (congrArg (fun z => D'.chartSec U O z) (D.localAppFun_localHom D' α U hU x)).trans
      (D'.chartSec_localAppFun_chartHomIso_inv U hU _)
  have hinj : ∀ a b : ToType (D'.glued.val.obj (op O)),
      D'.chartSec W O a = D'.chartSec W O b → a = b := fun a b hab =>
    (D'.localAppFun_chartHomIso_inv_chartSec W (hO.trans h) a).symm.trans
      ((congrArg (fun z => localAppFun (D'.chartHomIso W).inv O (hO.trans h) z) hab).trans
        (D'.localAppFun_chartHomIso_inv_chartSec W (hO.trans h) b))
  refine hinj _ _ ?_
  calc D'.chartSec W O (localAppFun (D.localHom D' α V) O hO x)
      = localAppFun (D'.comp h).hom O hO
          (D'.chartSec V O (localAppFun (D.localHom D' α V) O hO x)) :=
        (D'.localAppFun_comp_chartSec h hO _).symm
    _ = localAppFun (D'.comp h).hom O hO (pushSec V (α V) O (D.chartSec V O x)) :=
        congrArg (fun z => localAppFun (D'.comp h).hom O hO z) (hA V hO)
    _ = pushSec W (α W) O (localAppFun (D.comp h).hom O hO (D.chartSec V O x)) :=
        (pushSec_localAppFun_comp D D' hα h hO _).symm
    _ = pushSec W (α W) O (D.chartSec W O x) :=
        congrArg (fun z => pushSec W (α W) O z) (D.localAppFun_comp_chartSec h hO x)
    _ = D'.chartSec W O (localAppFun (D.localHom D' α W) O (hO.trans h) x) :=
        (hA W (hO.trans h)).symm

/-- **The local morphisms agree over an open contained in two charts.** Every point of such an
open lies in an affine open contained in both, and over an open inside that affine open the two
local morphisms agree with the one attached to it; the separation half of the sheaf condition for
the second glued module propagates the agreement. This is the hypothesis that
`AlgebraicGeometry.exists_hom_of_localHoms` consumes. -/
theorem localApp_localHom_eq {α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V}
    (hα : IsCompatible α) (V W : X.affineOpens) (O : X.Opens) (hV : O ≤ (V.1 : X.Opens))
    (hW : O ≤ (W.1 : X.Opens)) :
    localApp (D.localHom D' α V) O hV = localApp (D.localHom D' α W) O hW := by
  refine ConcreteCategory.ext_apply fun x => ?_
  show localAppFun (D.localHom D' α V) O hV x = localAppFun (D.localHom D' α W) O hW x
  refine D'.glued.isSheaf.section_ext (U := op O) ?_
  intro p hp
  have hpVW : p ∈ (chart X V).opensRange ⊓ (chart X W).opensRange := by
    rw [opensRange_chart, opensRange_chart]
    exact ⟨hV hp, hW hp⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (locallyDirected V W hpVW)
  have hpk : p ∈ (k.1.1 : X.Opens) := by
    have h' := hk
    rwa [opensRange_chart] at h'
  refine ⟨O ⊓ (k.1.1 : X.Opens), inf_le_left, ⟨hp, hpk⟩, ?_⟩
  have key : ∀ (U : X.affineOpens) (hU : O ≤ (U.1 : X.Opens)), k.1.1 ≤ U →
      D'.glued.val.map (homOfLE (inf_le_left : O ⊓ (k.1.1 : X.Opens) ≤ O)).op
        (localAppFun (D.localHom D' α U) O hU x)
      = localAppFun (D.localHom D' α k.1) (O ⊓ (k.1.1 : X.Opens)) inf_le_right
        (D.glued.val.map (homOfLE (inf_le_left : O ⊓ (k.1.1 : X.Opens) ≤ O)).op x) :=
    fun U hU hkU =>
      (localAppFun_naturality (D.localHom D' α U) hU (inf_le_left.trans hU)
        (homOfLE (inf_le_left : O ⊓ (k.1.1 : X.Opens) ≤ O)) x).trans
        (localAppFun_localHom_eq_of_le D D' hα hkU inf_le_right _).symm
  exact (key V hV k.2.1).trans (key W hW k.2.2).symm

/-! ### The glued morphism -/

/-- The existence statement behind
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueHom`: the local morphisms attached to the
affine opens come from a morphism of the glued modules. -/
theorem exists_glueHom (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V) (hα : IsCompatible α) :
    ∃ ψ : D.glued ⟶ D'.glued, ∀ V : X.affineOpens,
      (Scheme.Modules.restrictFunctor (chart X V)).map ψ = D.localHom D' α V :=
  exists_hom_of_localHoms (AlgebraicGeometry.iSup_affineOpens_eq_top X) (D.localHom D' α)
    (localApp_localHom_eq D D' hα)

/-- **The morphism of two glued sheaves of modules glued from a compatible family of morphisms on
the affine opens.** -/
def glueHom (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V) (hα : IsCompatible α) :
    D.glued ⟶ D'.glued :=
  (D.exists_glueHom D' α hα).choose

/-- The glued morphism restricts on each chart to the local morphism there. -/
theorem restrictFunctor_map_glueHom (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V)
    (hα : IsCompatible α) (V : X.affineOpens) :
    (Scheme.Modules.restrictFunctor (chart X V)).map (D.glueHom D' α hα)
      = D.localHom D' α V :=
  (D.exists_glueHom D' α hα).choose_spec V

/-- **The characterisation of the glued morphism**: on the chart of an affine open it is the
member of the family there, read through the chart isomorphisms. -/
theorem glueHom_chartIso (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V) (hα : IsCompatible α)
    (V : X.affineOpens) :
    (D.chartIso V).inv ≫ (Scheme.Modules.restrictFunctor (chart X V)).map (D.glueHom D' α hα)
        ≫ (D'.chartIso V).hom = α V := by
  rw [D.restrictFunctor_map_glueHom D' α hα V, localHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- A morphism of the glued modules which satisfies the characterisation
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueHom_chartIso` restricts on each chart to the
local morphism there. -/
theorem restrictFunctor_map_eq_localHom {α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V}
    (ψ : D.glued ⟶ D'.glued) (V : X.affineOpens)
    (h : (D.chartIso V).inv ≫ (Scheme.Modules.restrictFunctor (chart X V)).map ψ
      ≫ (D'.chartIso V).hom = α V) :
    (Scheme.Modules.restrictFunctor (chart X V)).map ψ = D.localHom D' α V := by
  rw [localHom, ← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Uniqueness of the glued morphism.** A morphism of the glued modules which is the member of
the family on every chart is the glued morphism, because equality of morphisms of sheaves of
modules is local and the affine opens cover `X`. -/
theorem eq_glueHom (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V) (hα : IsCompatible α)
    (ψ : D.glued ⟶ D'.glued)
    (hψ : ∀ V : X.affineOpens, (D.chartIso V).inv ≫
      (Scheme.Modules.restrictFunctor (chart X V)).map ψ ≫ (D'.chartIso V).hom = α V) :
    ψ = D.glueHom D' α hα :=
  Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover
    (fun V : X.affineOpens => (V.1 : X.Opens)) exists_mem_affineOpens fun V =>
      (restrictFunctor_map_eq_localHom D D' ψ V (hψ V)).trans
        (D.restrictFunctor_map_glueHom D' α hα V).symm

/-! ### Functoriality -/

/-- The family of identities is compatible with the comparisons of a chart comparison with
itself. -/
theorem isCompatible_id : IsCompatible (D := D) (D' := D) (fun V => 𝟙 (D.mod V)) := by
  intro V W h
  rw [pushRes_id, pushRes_id, Category.comp_id, Category.id_comp]

/-- **The family of identities glues to the identity.** -/
theorem glueHom_id : D.glueHom D (fun V => 𝟙 (D.mod V)) (isCompatible_id D) = 𝟙 D.glued :=
  (eq_glueHom D D _ (isCompatible_id D) (𝟙 D.glued) fun V => by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]).symm

/-- The family of composites of two compatible families is compatible. -/
theorem isCompatible_comp (D'' : ChartComparison X)
    {α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V}
    {β : ∀ V : X.affineOpens, D'.mod V ⟶ D''.mod V}
    (hα : IsCompatible α) (hβ : IsCompatible β) :
    IsCompatible (fun V => α V ≫ β V) := by
  intro V W h
  calc (D.comp h).hom ≫ pushRes (V.1 : X.Opens) W (α W ≫ β W)
      = ((D.comp h).hom ≫ pushRes (V.1 : X.Opens) W (α W)) ≫
          pushRes (V.1 : X.Opens) W (β W) := by
        rw [pushRes_comp, Category.assoc]
    _ = (pushRes (V.1 : X.Opens) V (α V) ≫ (D'.comp h).hom) ≫
          pushRes (V.1 : X.Opens) W (β W) := by rw [hα h]
    _ = pushRes (V.1 : X.Opens) V (α V) ≫
          (pushRes (V.1 : X.Opens) V (β V) ≫ (D''.comp h).hom) := by
        rw [Category.assoc, hβ h]
    _ = pushRes (V.1 : X.Opens) V (α V ≫ β V) ≫ (D''.comp h).hom := by
        rw [pushRes_comp, Category.assoc]

/-- **The family of composites glues to the composite of the glued morphisms.** -/
theorem glueHom_comp (D'' : ChartComparison X)
    (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V)
    (β : ∀ V : X.affineOpens, D'.mod V ⟶ D''.mod V)
    (hα : IsCompatible α) (hβ : IsCompatible β) :
    D.glueHom D'' (fun V => α V ≫ β V) (isCompatible_comp D D' D'' hα hβ)
      = D.glueHom D' α hα ≫ D'.glueHom D'' β hβ :=
  (eq_glueHom D D'' _ (isCompatible_comp D D' D'' hα hβ)
    (D.glueHom D' α hα ≫ D'.glueHom D'' β hβ) fun V => by
      rw [CategoryTheory.Functor.map_comp, D.restrictFunctor_map_glueHom D' α hα V,
        D'.restrictFunctor_map_glueHom D'' β hβ V, localHom, localHom]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]).symm

/-- The family of inverses of a compatible family of isomorphisms is compatible. The comparisons
are isomorphisms, so the commuting square of the forward directions can be read backwards. -/
theorem isCompatible_symm {α : ∀ V : X.affineOpens, D.mod V ≅ D'.mod V}
    (hα : IsCompatible (fun V => (α V).hom)) : IsCompatible (fun V => (α V).inv) := by
  intro V W h
  calc (D'.comp h).hom ≫ pushRes (V.1 : X.Opens) W (α W).inv
      = (pushRes (V.1 : X.Opens) V (α V).inv ≫ pushRes (V.1 : X.Opens) V (α V).hom) ≫
          (D'.comp h).hom ≫ pushRes (V.1 : X.Opens) W (α W).inv := by
        rw [pushRes_inv_hom_id, Category.id_comp]
    _ = pushRes (V.1 : X.Opens) V (α V).inv ≫ ((pushRes (V.1 : X.Opens) V (α V).hom ≫
          (D'.comp h).hom) ≫ pushRes (V.1 : X.Opens) W (α W).inv) := by
        simp only [Category.assoc]
    _ = pushRes (V.1 : X.Opens) V (α V).inv ≫ (((D.comp h).hom ≫
          pushRes (V.1 : X.Opens) W (α W).hom) ≫ pushRes (V.1 : X.Opens) W (α W).inv) := by
        rw [← hα h]
    _ = pushRes (V.1 : X.Opens) V (α V).inv ≫ (D.comp h).hom := by
        rw [Category.assoc, pushRes_hom_inv_id, Category.comp_id]

/-- **The isomorphism of two glued sheaves of modules glued from a compatible family of
isomorphisms on the affine opens.** -/
def glueIso (α : ∀ V : X.affineOpens, D.mod V ≅ D'.mod V)
    (hα : IsCompatible (fun V => (α V).hom)) : D.glued ≅ D'.glued where
  hom := D.glueHom D' (fun V => (α V).hom) hα
  inv := D'.glueHom D (fun V => (α V).inv) (isCompatible_symm D D' hα)
  hom_inv_id := by
    refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover
      (fun V : X.affineOpens => (V.1 : X.Opens)) exists_mem_affineOpens fun V => ?_
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      D.restrictFunctor_map_glueHom D' _ hα V,
      D'.restrictFunctor_map_glueHom D _ (isCompatible_symm D D' hα) V, localHom, localHom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    exact (D.chartIso V).hom_inv_id
  inv_hom_id := by
    refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover
      (fun V : X.affineOpens => (V.1 : X.Opens)) exists_mem_affineOpens fun V => ?_
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      D'.restrictFunctor_map_glueHom D _ (isCompatible_symm D D' hα) V,
      D.restrictFunctor_map_glueHom D' _ hα V, localHom, localHom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact (D'.chartIso V).hom_inv_id

end ChartComparison

end AlgebraicGeometry.AffineOpensGlue

end
