module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Descent

/-!
# Morphisms of glueing data of sheaves of modules

A glueing datum of sheaves of `O`-modules is a sheaf on each member of a family of opens together
with comparison isomorphisms over the overlaps. A family of morphisms of the chart sheaves
commuting with the comparisons induces a morphism of the glued sheaves, acting coordinatewise on
the glued sections
`F(W) = eq( ∏ i, F i (W ⊓ U i)  ⇉  ∏ i j, F i (W ⊓ U i ⊓ U j) )`
of `Stacks.SheafOfModules.OModuleGlueData.sectionsSubmodule`. The induced morphism is determined
by, and functorial in, that family.

This is done for three shapes of glueing datum:

* for an `OModuleGlueData` on a topological space, a family of morphisms of local presheaves;
* for a `ModulesGlueData` on a scheme, a family of morphisms of the chart sheaves of modules;
* for a `ModulesDirectedGlueData` on a scheme, the same family, asked to commute only with the
  comparisons attached to *inclusions* of charts.

## Main definitions

* `Stacks.SheafOfModules.OModuleGlueData.Hom`: a morphism of glueing data — a family of morphisms
  of the chart sheaves commuting with the restriction maps and with the comparisons.
* `Stacks.SheafOfModules.OModuleGlueData.Hom.glued`: **the induced morphism of glued sheaves.**
* `Stacks.SheafOfModules.ModulesGlueData.Hom` and
  `Stacks.SheafOfModules.ModulesGlueData.Hom.glued`: the same on a scheme, with the chart data a
  family of morphisms of sheaves of modules.
* `Stacks.SheafOfModules.ModulesDirectedGlueData.Hom` and
  `Stacks.SheafOfModules.ModulesDirectedGlueData.Hom.glued`: the same for a locally directed
  datum.

## Main results

* `Stacks.SheafOfModules.OModuleGlueData.Hom.chartIso_glued`,
  `Stacks.SheafOfModules.ModulesGlueData.Hom.chartSectionsIso_glued` and
  `Stacks.SheafOfModules.ModulesDirectedGlueData.Hom.chartSectionsIso_glued`: the glued morphism
  is the given one on the charts.
* `Stacks.SheafOfModules.OModuleGlueData.Hom.glued_eq_id` and
  `Stacks.SheafOfModules.OModuleGlueData.Hom.glued_eq_comp`, with their scheme and directed
  analogues: a family of identities induces the identity, and a family of composites induces the
  composite.
* `Stacks.SheafOfModules.ModulesDirectedGlueData.Hom.app_pairTrans`: a family commuting with the
  comparisons of the inclusions commutes with the pairwise comparisons glued from them.

## Implementation notes

The `O(W)`-action on the ambient product `∏ i, F i (W ⊓ U i)` is the local instance
`Stacks.SheafOfModules.OModuleGlueData.sectionsProductModule`, installed locally here; a statement
mentioning `sectionsSubmodule` does not elaborate without it.

A goal naming the comparisons of two different glueing data over the same open is not
type-correct at `implicit` transparency, so such goals are handled by `Eq.trans` and `congrArg`
on explicit morphisms rather than by `rw`.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {O : TopCat.Sheaf RingCat.{u} X} {ι : Type u} {U : ι → Opens X}

attribute [local instance] OModuleGlueData.sectionsProductModule

namespace OModuleGlueData

/-- **A morphism of glueing data of sheaves of `O`-modules.** For each index a morphism of the
chart sheaves — a family of linear maps on sections over the opens contained in that chart,
compatible with the restriction maps — such that the comparison isomorphisms of the two data are
intertwined by it over every overlap. -/
structure Hom (D E : OModuleGlueData O U) where
  /-- The morphism of the `i`-th chart sheaves, on sections over an open contained in `U i`. -/
  app : ∀ (i : ι) {V : Opens X} (hV : V ≤ U i),
    (D.sheaf i).obj V hV →ₗ[O.obj.obj (op V)] (E.sheaf i).obj V hV
  /-- The morphism of chart sheaves commutes with the restriction maps. -/
  app_map : ∀ (i : ι) {V W : Opens X} (hV : V ≤ U i) (hWV : W ≤ V) (s : (D.sheaf i).obj V hV),
    app i (hWV.trans hV) ((D.sheaf i).map hWV s) = (E.sheaf i).map hWV (app i hV s)
  /-- The morphism of chart sheaves intertwines the comparison isomorphisms. -/
  app_trans : ∀ (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j)
      (s : (D.sheaf i).obj V hi),
    app j hj (D.trans i j hi hj s) = E.trans i j hi hj (app i hi s)

namespace Hom

variable {D E : OModuleGlueData O U}

/-- **Coordinatewise application carries the glued sections into the glued sections.** -/
theorem sections_mem (τ : Hom D E) (W : Opens X) (s : D.sectionsSubmodule W) :
    (fun i => τ.app i (inf_le_right : W ⊓ U i ≤ U i) (s.1 i)) ∈ E.sectionsSubmodule W := by
  intro i j
  rw [← τ.app_map i (inf_le_right : W ⊓ U i ≤ U i)
      (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i) (s.1 i),
    ← τ.app_trans i j (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right),
    s.2 i j,
    τ.app_map j (inf_le_right : W ⊓ U j ≤ U j)
      (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j) (s.1 j)]

/-- The induced map on glued sections over an open `W`: coordinatewise application. -/
def sectionsFun (τ : Hom D E) (W : Opens X) (s : D.sectionsSubmodule W) :
    E.sectionsSubmodule W :=
  ⟨_, τ.sections_mem W s⟩

/-- The `i`-th coordinate of the induced map on glued sections. -/
theorem sectionsFun_val (τ : Hom D E) (W : Opens X) (s : D.sectionsSubmodule W) (i : ι) :
    (τ.sectionsFun W s).1 i = τ.app i inf_le_right (s.1 i) := rfl

/-- The induced map on glued sections is linear over the functions on `W`. -/
def sectionsLinearMap (τ : Hom D E) (W : Opens X) :
    ModuleCat.of (ToType (O.obj.obj (op W))) (D.sectionsSubmodule W) →ₗ[ToType (O.obj.obj (op W))]
      ModuleCat.of (ToType (O.obj.obj (op W))) (E.sectionsSubmodule W) where
  toFun := τ.sectionsFun W
  map_add' s t := Subtype.ext (funext fun i => map_add (τ.app i inf_le_right) (s.1 i) (t.1 i))
  map_smul' r s := Subtype.ext (funext fun i =>
    map_smul (τ.app i (inf_le_right : W ⊓ U i ≤ U i))
      (O.obj.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r) (s.1 i))

/-- **The morphism of glued presheaves of `O`-modules induced by a morphism of glueing data.** -/
def gluedPresheafHom (τ : Hom D E) : D.gluedPresheafOfModules ⟶ E.gluedPresheafOfModules where
  app W := ModuleCat.ofHom (τ.sectionsLinearMap W.unop)
  naturality {W W'} g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun s => Subtype.ext (funext fun i => ?_))
    exact τ.app_map i inf_le_right (inf_le_inf_right (U i) g.unop.le) (s.1 i)

/-- **The morphism of glued sheaves of `O`-modules induced by a morphism of glueing data.** -/
def glued (τ : Hom D E) : D.glued ⟶ E.glued := ⟨τ.gluedPresheafHom⟩

/-- The induced morphism is coordinatewise application on sections. -/
theorem glued_app_val (τ : Hom D E) (W : Opens X) (s : ToType (D.glued.val.obj (op W)))
    (i : ι) :
    ((τ.glued.val.app (op W)).hom s).1 i = τ.app i inf_le_right (s.1 i) := rfl

/-- **The induced morphism is the given one on the charts.** Reading a section of the glued sheaf
on the `i`-th chart and then applying the `i`-th chart morphism is the same as applying the
induced morphism and then reading on the `i`-th chart. -/
theorem chartIso_glued (τ : Hom D E) (i : ι) {V : Opens X} (hV : V ≤ U i)
    (x : ToType (D.glued.val.obj (op V))) :
    (E.chartIso i hV).hom ((τ.glued.val.app (op V)).hom x)
      = τ.app i hV ((D.chartIso i hV).hom x) :=
  (τ.app_map i inf_le_right (le_inf le_rfl hV) (x.1 i)).symm

/-- Two morphisms of glued sheaves agree if they agree coordinatewise on glued sections. -/
private theorem glued_hom_ext {φ ψ : D.glued ⟶ E.glued}
    (h : ∀ (W : Opens X) (s : ToType (D.glued.val.obj (op W))) (i : ι),
      ((φ.val.app (op W)).hom s).1 i = ((ψ.val.app (op W)).hom s).1 i) :
    φ = ψ :=
  _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun s => Subtype.ext (funext (h _ s))))

/-- **A morphism of glueing data is determined by its chart morphisms.** -/
theorem glued_eq_of_app (τ σ : Hom D E)
    (h : ∀ (i : ι) {V : Opens X} (hV : V ≤ U i) (s : (D.sheaf i).obj V hV),
      τ.app i hV s = σ.app i hV s) :
    τ.glued = σ.glued :=
  glued_hom_ext fun _ s i => h i inf_le_right (s.1 i)

/-- **A family of identities induces the identity morphism.** -/
theorem glued_eq_id (τ : Hom D D)
    (h : ∀ (i : ι) {V : Opens X} (hV : V ≤ U i) (s : (D.sheaf i).obj V hV),
      τ.app i hV s = s) :
    τ.glued = 𝟙 D.glued :=
  glued_hom_ext fun _ s i => h i inf_le_right (s.1 i)

/-- **A family of composites induces the composite morphism.** -/
theorem glued_eq_comp {F : OModuleGlueData O U} (τ : Hom D E) (σ : Hom E F) (ρ : Hom D F)
    (h : ∀ (i : ι) {V : Opens X} (hV : V ≤ U i) (s : (D.sheaf i).obj V hV),
      ρ.app i hV s = σ.app i hV (τ.app i hV s)) :
    ρ.glued = τ.glued ≫ σ.glued :=
  glued_hom_ext fun _ s i => h i inf_le_right (s.1 i)

end Hom

end OModuleGlueData

/-! ### Morphisms of glueing data of sheaves of modules on a scheme -/

section Scheme

open AlgebraicGeometry

variable {S : Scheme.{u}} {Y : ι → Scheme.{u}}

namespace ModulesGlueData

variable {f : ∀ i, Y i ⟶ S} [∀ i, IsOpenImmersion (f i)]

/-- The chart morphism of a family of morphisms of the chart sheaves, read on sections over an
open of the base, as a map linear over the functions on that open. -/
abbrev chartSecMap {D E : ModulesGlueData S f} (chart : ∀ i, D.mod i ⟶ E.mod i) (i : ι)
    (V : S.Opens) :
    openSections (f i) (D.mod i) V →ₗ[ToType (S.ringCatSheaf.obj.obj (op V))]
      openSections (f i) (E.mod i) V :=
  (((Scheme.Modules.pushforward (f i)).map (chart i)).val.app (op V)).hom

/-- The chart morphism on a section. -/
abbrev chartSec {D E : ModulesGlueData S f} (chart : ∀ i, D.mod i ⟶ E.mod i) (i : ι)
    (V : S.Opens) (t : ToType (openSections (f i) (D.mod i) V)) :
    ToType (openSections (f i) (E.mod i) V) :=
  chartSecMap chart i V t

/-- **A morphism of glueing data of sheaves of modules on a scheme.** A morphism of the sheaves
of modules on each chart, such that the comparison isomorphisms of the two data are intertwined
by it on sections over every open contained in two charts. -/
structure Hom (D E : ModulesGlueData S f) where
  /-- The morphism of the sheaves of modules on the `i`-th chart. -/
  chart : ∀ i, D.mod i ⟶ E.mod i
  /-- The chart morphisms intertwine the comparison isomorphisms, on sections over an open
  contained in both charts. -/
  chart_trans : ∀ (i j : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange)
      (hj : V ≤ (f j).opensRange) (t : ToType (openSections (f i) (D.mod i) V)),
    chartSec chart j V (D.trans i j hi hj t)
      = E.trans i j hi hj (chartSec chart i V t)

namespace Hom

variable {D E : ModulesGlueData S f}

/-- The chart morphism of `τ` on sections over an open of the base. -/
abbrev sec (τ : Hom D E) (i : ι) (V : S.Opens)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    ToType (openSections (f i) (E.mod i) V) :=
  chartSec τ.chart i V t

/-- The underlying morphism of glueing data of sheaves of `O_S`-modules. -/
def toOModuleGlueHom (τ : Hom D E) :
    OModuleGlueData.Hom D.toOModuleGlueData E.toOModuleGlueData where
  app i {V} _ := chartSecMap τ.chart i V
  app_map i {_ _} _ hWV s := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pushforward (f i)).map (τ.chart i)).val (homOfLE hWV).op s
  app_trans i j {_} hi hj s := τ.chart_trans i j hi hj s

/-- The `app` of the underlying morphism of glueing data is the chart morphism on sections. -/
theorem toOModuleGlueHom_app (τ : Hom D E) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) (t : ToType (openSections (f i) (D.mod i) V)) :
    τ.toOModuleGlueHom.app i hV t = chartSec τ.chart i V t := rfl

/-- **The morphism of glued sheaves of modules induced by a morphism of glueing data.** -/
def glued (τ : Hom D E) : D.glued ⟶ E.glued := τ.toOModuleGlueHom.glued

/-- **The induced morphism is the given one on the charts**, read on sections over an open
contained in the `i`-th chart. -/
theorem chartSectionsIso_glued (τ : Hom D E) (i : ι) {V : S.Opens} (hV : V ≤ (f i).opensRange)
    (x : ToType (D.glued.val.obj (op V))) :
    (E.chartSectionsIso i hV).hom ((τ.glued.val.app (op V)).hom x)
      = τ.sec i V ((D.chartSectionsIso i hV).hom x) :=
  τ.toOModuleGlueHom.chartIso_glued i hV x

/-- **A morphism of glueing data is determined by its chart morphisms.** -/
theorem glued_eq_of_chart (τ σ : Hom D E) (h : ∀ i, τ.chart i = σ.chart i) :
    τ.glued = σ.glued :=
  τ.toOModuleGlueHom.glued_eq_of_app σ.toOModuleGlueHom fun i {V} _ s =>
    congrArg (fun φ : D.mod i ⟶ E.mod i =>
      (((Scheme.Modules.pushforward (f i)).map φ).val.app (op V)).hom s) (h i)

/-- **A family of identities induces the identity morphism.** -/
theorem glued_eq_id (τ : Hom D D) (h : ∀ i, τ.chart i = 𝟙 (D.mod i)) :
    τ.glued = 𝟙 D.glued := by
  refine τ.toOModuleGlueHom.glued_eq_id ?_
  intro i V hV s
  have e : (Scheme.Modules.pushforward (f i)).map (τ.chart i)
      = 𝟙 ((Scheme.Modules.pushforward (f i)).obj (D.mod i)) := by
    rw [h i]
    exact (Scheme.Modules.pushforward (f i)).map_id (D.mod i)
  exact congrArg (fun φ => (φ.val.app (op V)).hom s) e

/-- **A family of composites induces the composite morphism.** -/
theorem glued_eq_comp {F : ModulesGlueData S f} (τ : Hom D E) (σ : Hom E F) (ρ : Hom D F)
    (h : ∀ i, ρ.chart i = τ.chart i ≫ σ.chart i) :
    ρ.glued = τ.glued ≫ σ.glued := by
  refine τ.toOModuleGlueHom.glued_eq_comp σ.toOModuleGlueHom ρ.toOModuleGlueHom ?_
  intro i V hV s
  have e : (Scheme.Modules.pushforward (f i)).map (ρ.chart i)
      = (Scheme.Modules.pushforward (f i)).map (τ.chart i)
        ≫ (Scheme.Modules.pushforward (f i)).map (σ.chart i) := by
    rw [h i, Functor.map_comp]
  exact congrArg (fun φ => (φ.val.app (op V)).hom s) e

end Hom

end ModulesGlueData

/-! ### Morphisms of locally directed glueing data -/

namespace ModulesDirectedGlueData

variable [Preorder ι] {f : ∀ i, Y i ⟶ S} [∀ i, IsOpenImmersion (f i)]

/-- The chart morphism of a family of morphisms of the chart sheaves, read on sections over an
open of the base. -/
abbrev chartSec {D E : ModulesDirectedGlueData S f} (chart : ∀ i, D.mod i ⟶ E.mod i) (i : ι)
    (V : S.Opens) (t : ToType (openSections (f i) (D.mod i) V)) :
    ToType (openSections (f i) (E.mod i) V) :=
  (((Scheme.Modules.pushforward (f i)).map (chart i)).val.app (op V)).hom t

/-- The chart morphism of a morphism of pairwise glueing data agrees with the directed one. -/
theorem chartSec_eq {D E : ModulesDirectedGlueData S f} (chart : ∀ i, D.mod i ⟶ E.mod i)
    (i : ι) (V : S.Opens) (t : ToType (openSections (f i) (D.mod i) V)) :
    ModulesGlueData.chartSec (D := D.toModulesGlueData) (E := E.toModulesGlueData) chart i V t
      = chartSec chart i V t := rfl

/-- **A morphism of locally directed glueing data of sheaves of modules on a scheme.** A morphism
of the sheaves of modules on each chart, asked to intertwine only the comparison isomorphisms
attached to *inclusions* `i ≤ j` of charts. -/
structure Hom (D E : ModulesDirectedGlueData S f) where
  /-- The morphism of the sheaves of modules on the `i`-th chart. -/
  chart : ∀ i, D.mod i ⟶ E.mod i
  /-- The chart morphisms intertwine the comparison isomorphism attached to an inclusion of
  charts, on sections over an open contained in the smaller chart. -/
  chart_trans : ∀ {i j : ι} (h : i ≤ j) {V : S.Opens} (hV : V ≤ (f i).opensRange)
      (t : ToType (openSections (f i) (D.mod i) V)),
    chartSec chart j V (D.trans h hV t) = E.trans h hV (chartSec chart i V t)

namespace Hom

variable {D E : ModulesDirectedGlueData S f}

/-- The chart morphism of `τ` on sections over an open of the base. -/
abbrev sec (τ : Hom D E) (i : ι) (V : S.Opens)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    ToType (openSections (f i) (E.mod i) V) :=
  chartSec τ.chart i V t

/-- The chart morphisms commute with the restriction maps of the sections over the base. -/
theorem sec_res (τ : Hom D E) (i : ι) {V W : S.Opens} (hWV : W ≤ V)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    τ.sec i W (D.res i hWV t) = E.res i hWV (τ.sec i V t) :=
  PresheafOfModules.naturality_apply
    ((Scheme.Modules.pushforward (f i)).map (τ.chart i)).val (homOfLE hWV).op t

/-- The chart morphisms intertwine the inverse of the comparison of an inclusion of charts. -/
theorem sec_trans_symm (τ : Hom D E) {i j : ι} (h : i ≤ j) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) (t : ToType (openSections (f j) (D.mod j) V)) :
    τ.sec i V ((D.trans h hV).symm t) = (E.trans h hV).symm (τ.sec j V t) := by
  have key := τ.chart_trans h hV ((D.trans h hV).symm t)
  rw [LinearEquiv.apply_symm_apply] at key
  exact (LinearEquiv.eq_symm_apply (E.trans h hV)).mpr key.symm

/-- The chart morphisms intertwine the comparison through a chart below both. -/
theorem sec_pairEquiv (τ : Hom D E) {i j : ι} (k : ι) (hki : k ≤ i) (hkj : k ≤ j)
    {V : S.Opens} (hV : V ≤ (f k).opensRange)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    τ.sec j V (D.pairEquiv k hki hkj hV t) = E.pairEquiv k hki hkj hV (τ.sec i V t) :=
  (τ.chart_trans hkj hV ((D.trans hki hV).symm t)).trans
    (congrArg (E.trans hkj hV) (τ.sec_trans_symm hki hV t))

/-- **The chart morphisms intertwine the pairwise comparisons** glued from the comparisons of the
inclusions. -/
theorem app_pairTrans (τ : Hom D E) (i j : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange ⊓ (f j).opensRange)
    (t : ToType (openSections (f i) (D.mod i) V)) :
    τ.sec j V (D.pairTrans i j hV t) = E.pairTrans i j hV (τ.sec i V t) := by
  have key : ∀ m : {m : ι // m ≤ i ∧ m ≤ j},
      E.res j (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) (τ.sec j V (D.pairTrans i j hV t))
        = E.res j (inf_le_left : V ⊓ (f m.1).opensRange ≤ V)
            (E.pairTrans i j hV (τ.sec i V t)) := by
    intro m
    calc E.res j (inf_le_left : V ⊓ (f m.1).opensRange ≤ V)
              (τ.sec j V (D.pairTrans i j hV t))
        = τ.sec j (V ⊓ (f m.1).opensRange)
            (D.res j (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) (D.pairTrans i j hV t)) :=
          (τ.sec_res j inf_le_left _).symm
      _ = τ.sec j (V ⊓ (f m.1).opensRange)
            (D.pairTrans i j (inf_le_left.trans hV)
              (D.res i (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) t)) :=
          congrArg (τ.sec j (V ⊓ (f m.1).opensRange))
            (D.pairTrans_map i j hV inf_le_left t).symm
      _ = τ.sec j (V ⊓ (f m.1).opensRange)
            (D.pairEquiv m.1 m.2.1 m.2.2
              (inf_le_right : V ⊓ (f m.1).opensRange ≤ (f m.1).opensRange)
              (D.res i (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) t)) :=
          congrArg (τ.sec j (V ⊓ (f m.1).opensRange))
            (D.pairTrans_eq i j m.2.1 m.2.2 inf_le_right _)
      _ = E.pairEquiv m.1 m.2.1 m.2.2
            (inf_le_right : V ⊓ (f m.1).opensRange ≤ (f m.1).opensRange)
            (τ.sec i (V ⊓ (f m.1).opensRange)
              (D.res i (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) t)) :=
          τ.sec_pairEquiv m.1 m.2.1 m.2.2 inf_le_right _
      _ = E.pairEquiv m.1 m.2.1 m.2.2
            (inf_le_right : V ⊓ (f m.1).opensRange ≤ (f m.1).opensRange)
            (E.res i (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) (τ.sec i V t)) :=
          congrArg (E.pairEquiv m.1 m.2.1 m.2.2 inf_le_right) (τ.sec_res i inf_le_left t)
      _ = E.pairTrans i j (inf_le_left.trans hV)
            (E.res i (inf_le_left : V ⊓ (f m.1).opensRange ≤ V) (τ.sec i V t)) :=
          (E.pairTrans_eq i j m.2.1 m.2.2 inf_le_right _).symm
      _ = E.res j (inf_le_left : V ⊓ (f m.1).opensRange ≤ V)
            (E.pairTrans i j hV (τ.sec i V t)) :=
          E.pairTrans_map i j hV inf_le_left (τ.sec i V t)
  exact (E.pre_isSheaf j ((f i).opensRange ⊓ (f j).opensRange)).eq_of_locally_eq
    (hV := hV)
    (fun m : {m : ι // m ≤ i ∧ m ≤ j} => V ⊓ (f m.1).opensRange) (fun _ => inf_le_left)
    (D.le_iSup_inf_opensRange (hV.trans inf_le_left) (hV.trans inf_le_right)) key

/-- The underlying morphism of the pairwise glueing data. -/
def toModulesGlueHom (τ : Hom D E) :
    ModulesGlueData.Hom D.toModulesGlueData E.toModulesGlueData where
  chart := τ.chart
  chart_trans i j {_} hi hj t := τ.app_pairTrans i j (le_inf hi hj) t

/-- **The morphism of glued sheaves of modules induced by a morphism of locally directed glueing
data.** -/
def glued (τ : Hom D E) : D.glued ⟶ E.glued := τ.toModulesGlueHom.glued

/-- **The induced morphism is the given one on the charts**, read on sections over an open
contained in the `i`-th chart. -/
theorem chartSectionsIso_glued (τ : Hom D E) (i : ι) {V : S.Opens} (hV : V ≤ (f i).opensRange)
    (x : ToType (D.glued.val.obj (op V))) :
    (E.chartSectionsIso i hV).hom ((τ.glued.val.app (op V)).hom x)
      = τ.sec i V ((D.chartSectionsIso i hV).hom x) :=
  τ.toModulesGlueHom.chartSectionsIso_glued i hV x

/-- **A morphism of locally directed glueing data is determined by its chart morphisms.** -/
theorem glued_eq_of_chart (τ σ : Hom D E) (h : ∀ i, τ.chart i = σ.chart i) :
    τ.glued = σ.glued :=
  τ.toModulesGlueHom.glued_eq_of_chart σ.toModulesGlueHom fun i => h i

/-- **A family of identities induces the identity morphism.** -/
theorem glued_eq_id (τ : Hom D D) (h : ∀ i, τ.chart i = 𝟙 (D.mod i)) :
    τ.glued = 𝟙 D.glued :=
  τ.toModulesGlueHom.glued_eq_id fun i => h i

/-- **A family of composites induces the composite morphism.** -/
theorem glued_eq_comp {F : ModulesDirectedGlueData S f} (τ : Hom D E) (σ : Hom E F)
    (ρ : Hom D F) (h : ∀ i, ρ.chart i = τ.chart i ≫ σ.chart i) :
    ρ.glued = τ.glued ≫ σ.glued :=
  τ.toModulesGlueHom.glued_eq_comp σ.toModulesGlueHom ρ.toModulesGlueHom fun i => h i

end Hom

end ModulesDirectedGlueData

end Scheme

end Stacks.SheafOfModules

end
