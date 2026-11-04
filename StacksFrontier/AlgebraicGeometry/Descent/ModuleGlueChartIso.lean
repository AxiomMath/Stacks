module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueOverlapCocycle

/-!
# A glueing datum of sheaves of modules from comparisons on the charts themselves

`Stacks.SheafOfModules.ModulesGlueData.ofOverlapIsoOfCocycle` builds a glueing datum out of one
isomorphism per pair of charts, taken between the restrictions to the overlap of the two chart
images of the **pushforwards** of the chart modules, with the cocycle condition an equality of
morphisms over the triple overlap. A construction, however, produces its comparison between the
chart modules themselves, on a scheme mapping into both charts: the two modules live on
different schemes, and the overlap of the chart images, viewed through either chart, is the only
place they can be compared.

`Stacks.SheafOfModules.restrictPushforwardIso` converts one such comparison into the other. What
was missing, and is supplied here, is that the conversion **commutes with passing to a smaller
open**: the restriction to the triple overlap of a converted comparison is the conversion of the
restricted comparison. Without it the cocycle condition of `ofOverlapIsoOfCocycle`, which lives
over the triple overlap, cannot be read off a cocycle for the comparisons themselves, because
the three converted comparisons are restrictions to three different overlaps and nothing relates
them.

## The shape of the conversion

`AlgebraicGeometry.restrictLocal`, which restricts a morphism of the restrictions to an open `W`
of the base to the restrictions to a smaller open `V`, is stated only for restrictions along the
inclusions `W.ι` and `V.ι`. A converted comparison is a composite
`restrict (f_* N) W.ι ⟶ restrict N a ⟶ restrict M b ⟶ restrict (g_* M) W.ι` whose intermediate
objects are restrictions along the chart liftings `a` and `b` instead, so `restrictLocal` cannot
be applied factor by factor.

`AlgebraicGeometry.restrictChart` is the operation `restrictLocal` performs, stated for
restrictions along *arbitrary* morphisms out of `W.toScheme` and `V.toScheme` compatible with the
inclusion `V.toScheme ⟶ W.toScheme`. It is `restrictLocal` itself when the two morphisms are the
inclusions (`AlgebraicGeometry.restrictLocal_eq_restrictChart`, which is `rfl`), it is functorial
in the morphism, and it carries each factor of a converted comparison to the corresponding factor
of the converted restricted comparison.

## Main definitions

* `AlgebraicGeometry.restrictChart`: **the restriction to a smaller open of a morphism of
  restrictions along arbitrary liftings**, the operation of which
  `AlgebraicGeometry.restrictLocal` is the case of the two inclusions.
* `AlgebraicGeometry.chartOpenLift`: the lifting through an open immersion of the inclusion of an
  open of the base contained in its image.
* `Stacks.SheafOfModules.chartModule`: a chart module restricted to the lifting of an open of the
  base inside the chart image — where two charts are compared.
* `Stacks.SheafOfModules.ModulesGlueData.ofChartIso`: **the glueing datum of a family of sheaves
  of modules on the charts together with isomorphisms of the chart modules over the pairwise
  overlaps whose restrictions to the triple overlaps compose.**

## Main results

* `AlgebraicGeometry.restrictChart_restrictPushforwardIso_hom` and
  `...restrictChart_restrictPushforwardIso_inv`: **the conversion of a chart comparison into a
  comparison of pushforwards commutes with restriction to a smaller open.** This is the
  computation the glueing needs and the only one that is not formal.
* `AlgebraicGeometry.restrictChart_comp` and `AlgebraicGeometry.restrictChart_id`:
  `restrictChart` is functorial, so a composite of comparisons restricts factor by factor even
  when the intermediate objects are not restrictions along the inclusions.
* `AlgebraicGeometry.homOfLE_comp_chartOpenLift`: the chart liftings of two nested opens are
  compatible with the inclusion of the smaller in the larger, the chart being a monomorphism.
* `Stacks.SheafOfModules.ModulesGlueData.ofChartIso_trans_chartSectionsIso`: **the comparisons of
  the module glued by `ofChartIso` with the chart modules are related to one another by the given
  comparisons `β`.** `ofChartIso_mod` records only the chart modules; this is the statement about
  the *glued* module that a construction of a morphism out of it needs, and it is cheap because
  the transition of the datum is by construction the sections map of `β i j` converted to the
  pushforwards, so `...ModulesGlueData.trans_chartSectionsIso` says it already.

## Implementation notes

Every comparison isomorphism of the restriction functors — `restrictFunctorCongr`,
`restrictFunctorComp` and the counit `restrictFunctorAdjCounitIso` — acts on sections as a
restriction map of the module along an equality of opens; for the counit this is
`AlgebraicGeometry.restrictFunctorAdjCounitIso_hom_app_app`, which holds by `rfl` and which
Mathlib states only for the counit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. So
both sides of the conversion lemma are composites of restriction maps of one module with the same
source and target, and the homs of a poset being unique they agree.

Carrying that out needs one detour. After the components have been expanded the goal is no longer
type-correct at the `implicit` transparency level, so no further `simp` step applies to it — the
same obstruction the `mulSheaf` rewrites meet elsewhere in this development. The composite is
therefore collapsed by `exact` against a helper whose restriction maps are *free arrows*, where
no spelling of an open appears and the collapse is a single `Subsingleton.elim`.

`chartOpenLift` is a genuine definition rather than an `abbrev` so that the open and the proof
that it lies in the chart image are recorded in the statement; the proof is irrelevant, so the
liftings of one open obtained from two different proofs are the same term, which is what lets
the three restricted comparisons of a cocycle triangle be composed.

## No tag is claimed

Stacks 00AM is carried by `Stacks.SheafOfModules.ModulesGlueData.glued` and
`...ModulesGlueData.chartIso`; this file only changes the shape in which the comparisons of a
datum are presented.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Restriction of a morphism of restrictions along arbitrary liftings -/

/-- **The comparison of the restriction along a lifting with the restriction of the restriction.**
For `V ≤ W` opens of `X` and morphisms `p` out of `W.toScheme` and `q` out of `V.toScheme` with
`V.toScheme ⟶ W.toScheme ⟶ p` equal to `q`, the restriction of `N` along `q` is the restriction
along `V.toScheme ⟶ W.toScheme` of the restriction along `p`. -/
def restrictChartIsoOfLE {Y : Scheme.{u}} {V W : X.Opens} (hV : V ≤ W) {p : W.toScheme ⟶ Y}
    [IsOpenImmersion p] {q : V.toScheme ⟶ Y} [IsOpenImmersion q] (hpq : X.homOfLE hV ≫ p = q)
    (N : Y.Modules) :
    Scheme.Modules.restrict N q ≅
      Scheme.Modules.restrict (Scheme.Modules.restrict N p) (X.homOfLE hV) :=
  ((Scheme.Modules.restrictFunctorCongr hpq).app N).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hV) p).app N

/-- **The restriction to a smaller open of a morphism of restrictions along liftings.** This is
the operation `AlgebraicGeometry.restrictLocal` performs, with the inclusions `W.ι` and `V.ι`
replaced by arbitrary compatible liftings of them, and with the source and the target allowed to
be restrictions of modules on two different schemes. -/
def restrictChart {Y Z : Scheme.{u}} {V W : X.Opens} (hV : V ≤ W)
    {p : W.toScheme ⟶ Y} [IsOpenImmersion p] {q : V.toScheme ⟶ Y} [IsOpenImmersion q]
    (hpq : X.homOfLE hV ≫ p = q)
    {p' : W.toScheme ⟶ Z} [IsOpenImmersion p'] {q' : V.toScheme ⟶ Z} [IsOpenImmersion q']
    (hpq' : X.homOfLE hV ≫ p' = q')
    {N : Y.Modules} {M : Z.Modules}
    (β : Scheme.Modules.restrict N p ⟶ Scheme.Modules.restrict M p') :
    Scheme.Modules.restrict N q ⟶ Scheme.Modules.restrict M q' :=
  (restrictChartIsoOfLE hV hpq N).hom ≫
    (Scheme.Modules.restrictFunctor (X.homOfLE hV)).map β ≫ (restrictChartIsoOfLE hV hpq' M).inv

/-- **`AlgebraicGeometry.restrictLocal` is `AlgebraicGeometry.restrictChart` at the two
inclusions.** -/
lemma restrictLocal_eq_restrictChart {A B : X.Modules} {V W : X.Opens} (hV : V ≤ W)
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) :
    restrictLocal φ hV =
      restrictChart hV (Scheme.homOfLE_ι X hV) (Scheme.homOfLE_ι X hV) φ :=
  rfl

/-- **`AlgebraicGeometry.restrictChart` is multiplicative**, through an intermediate object that
is a restriction along any lifting. -/
lemma restrictChart_comp {Y Z Z' : Scheme.{u}} {V W : X.Opens} (hV : V ≤ W)
    {p : W.toScheme ⟶ Y} [IsOpenImmersion p] {q : V.toScheme ⟶ Y} [IsOpenImmersion q]
    (hpq : X.homOfLE hV ≫ p = q)
    {p' : W.toScheme ⟶ Z} [IsOpenImmersion p'] {q' : V.toScheme ⟶ Z} [IsOpenImmersion q']
    (hpq' : X.homOfLE hV ≫ p' = q')
    {p'' : W.toScheme ⟶ Z'} [IsOpenImmersion p''] {q'' : V.toScheme ⟶ Z'} [IsOpenImmersion q'']
    (hpq'' : X.homOfLE hV ≫ p'' = q'')
    {N : Y.Modules} {M : Z.Modules} {M' : Z'.Modules}
    (β : Scheme.Modules.restrict N p ⟶ Scheme.Modules.restrict M p')
    (γ : Scheme.Modules.restrict M p' ⟶ Scheme.Modules.restrict M' p'') :
    restrictChart hV hpq hpq'' (β ≫ γ) =
      restrictChart hV hpq hpq' β ≫ restrictChart hV hpq' hpq'' γ := by
  simp [restrictChart, Functor.map_comp]

/-- **`AlgebraicGeometry.restrictChart` is unital.** -/
@[simp]
lemma restrictChart_id {Y : Scheme.{u}} {V W : X.Opens} (hV : V ≤ W) {p : W.toScheme ⟶ Y}
    [IsOpenImmersion p] {q : V.toScheme ⟶ Y} [IsOpenImmersion q] (hpq : X.homOfLE hV ≫ p = q)
    (N : Y.Modules) :
    restrictChart hV hpq hpq (𝟙 (Scheme.Modules.restrict N p)) = 𝟙 _ := by
  simp [restrictChart]

/-! ### The conversion of a chart comparison, and its compatibility with restriction -/

/-- **The counit of the restriction–pushforward adjunction acts on sections as a restriction map
of the module.** Mathlib records this for the counit of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`; the isomorphism
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` is that counit, so the formula
holds for it by `rfl`. -/
private lemma restrictFunctorAdjCounitIso_hom_app_app {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (M : Y.Modules) (U : Y.Opens) :
    ((Scheme.Modules.restrictFunctorAdjCounitIso g).hom.app M).app U =
      M.presheaf.map (eqToHom (g.preimage_image_eq U).symm).op :=
  rfl

/-- A composite of seven restriction maps of a module is a composite of three with the same
source and target, the homs of a poset being unique.

The restriction maps are free arrows, so that the statement contains no spelling of an open: the
goal it closes is not type-correct at the `implicit` transparency level, and matching it needs
`exact` rather than a rewrite. -/
private lemma presheaf_map_collapse {Y : Scheme.{u}} (N : Y.Modules)
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : (Y.Opens)ᵒᵖ}
    (a₁ : P₀ ⟶ P₁) (a₂ : P₁ ⟶ P₂) (a₃ : P₂ ⟶ P₃) (a₄ : P₃ ⟶ P₄) (a₅ : P₄ ⟶ P₅)
    (a₆ : P₅ ⟶ P₆) (a₇ : P₆ ⟶ P₇) {Q₁ Q₂ : (Y.Opens)ᵒᵖ}
    (b₁ : P₀ ⟶ Q₁) (b₂ : Q₁ ⟶ Q₂) (b₃ : Q₂ ⟶ P₇) :
    (N.presheaf.map a₁ ≫ N.presheaf.map a₂) ≫
        (N.presheaf.map a₃ ≫ N.presheaf.map a₄ ≫ N.presheaf.map a₅) ≫
          N.presheaf.map a₆ ≫ N.presheaf.map a₇ =
      N.presheaf.map b₁ ≫ N.presheaf.map b₂ ≫ N.presheaf.map b₃ := by
  simp only [← Functor.map_comp, ← Category.assoc]
  exact presheaf_map_eq N _ _

/-- **Converting a chart comparison into a comparison of pushforwards commutes with restriction
to a smaller open.** For an open immersion `f : Y ⟶ X` and liftings `a`, `a'` of the inclusions
of two nested opens `V ≤ W` of `X` through `f`, the restriction to `V` of
`Stacks.SheafOfModules.restrictPushforwardIso` at `W` is the one at `V`.

This is what lets the cocycle condition of
`Stacks.SheafOfModules.ModulesGlueData.ofOverlapIsoOfCocycle`, which lives over the triple
overlap, be read off a cocycle for the chart comparisons: the three converted comparisons are
restrictions to three different pairwise overlaps, and this identifies each of them, restricted
to the triple overlap, with the conversion of the restricted comparison. -/
lemma restrictChart_restrictPushforwardIso_hom {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {V W : X.Opens} (hV : V ≤ W) {a : W.toScheme ⟶ Y} [IsOpenImmersion a]
    {a' : V.toScheme ⟶ Y} [IsOpenImmersion a'] (haa' : X.homOfLE hV ≫ a = a')
    (ha : a ≫ f = W.ι) (ha' : a' ≫ f = V.ι) (N : Y.Modules) :
    restrictChart hV (Scheme.homOfLE_ι X hV) haa'
        (Stacks.SheafOfModules.restrictPushforwardIso f a ha N).hom =
      (Stacks.SheafOfModules.restrictPushforwardIso f a' ha' N).hom := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  simp only [restrictChart, restrictChartIsoOfLE, Stacks.SheafOfModules.restrictPushforwardIso,
    restrictFunctor_map_app, restrictFunctorAdjCounitIso_hom_app_app, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.pushforward_obj_presheaf_map]
  exact presheaf_map_collapse N _ _ _ _ _ _ _ _ _ _

/-- **The inverse of the conversion also commutes with restriction to a smaller open.** This is
`AlgebraicGeometry.restrictChart_restrictPushforwardIso_hom` read backwards, through the
functoriality of `AlgebraicGeometry.restrictChart`. -/
lemma restrictChart_restrictPushforwardIso_inv {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {V W : X.Opens} (hV : V ≤ W) {a : W.toScheme ⟶ Y} [IsOpenImmersion a]
    {a' : V.toScheme ⟶ Y} [IsOpenImmersion a'] (haa' : X.homOfLE hV ≫ a = a')
    (ha : a ≫ f = W.ι) (ha' : a' ≫ f = V.ι) (N : Y.Modules) :
    restrictChart hV haa' (Scheme.homOfLE_ι X hV)
        (Stacks.SheafOfModules.restrictPushforwardIso f a ha N).inv =
      (Stacks.SheafOfModules.restrictPushforwardIso f a' ha' N).inv := by
  rw [← Category.comp_id (restrictChart hV haa' (Scheme.homOfLE_ι X hV) _),
    ← Iso.hom_inv_id (Stacks.SheafOfModules.restrictPushforwardIso f a' ha' N),
    ← restrictChart_restrictPushforwardIso_hom f hV haa' ha ha' N, ← Category.assoc,
    ← restrictChart_comp, Iso.inv_hom_id, restrictChart_id, Category.id_comp]

/-! ### The lifting of an open of the base through a chart -/

section ChartLift

variable {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- An open of the base contained in the image of an open immersion is contained in its range as
a set. -/
lemma range_ι_subset_range {V : X.Opens} (hV : V ≤ f.opensRange) :
    Set.range (V.ι).base ⊆ Set.range f.base := by
  rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
  exact hV

/-- **The lifting of an open of the base through a chart containing it.** For an open immersion
`f : Y ⟶ X` and an open `V` of `X` inside its image, the inclusion of `V` factors through `f`,
uniquely, and this is the factor. -/
def chartOpenLift {V : X.Opens} (hV : V ≤ f.opensRange) : V.toScheme ⟶ Y :=
  IsOpenImmersion.lift f V.ι (range_ι_subset_range f hV)

/-- The lifting of `V` through `f`, followed by `f`, is the inclusion of `V`. -/
@[simp]
lemma chartOpenLift_fac {V : X.Opens} (hV : V ≤ f.opensRange) : chartOpenLift f hV ≫ f = V.ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- The lifting of an open of the base through an open immersion is an open immersion. -/
instance {V : X.Opens} (hV : V ≤ f.opensRange) : IsOpenImmersion (chartOpenLift f hV) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift f V.ι (range_ι_subset_range f hV)))

/-- **The liftings of two nested opens through one chart are compatible with the inclusion of the
smaller in the larger**, an open immersion being a monomorphism. -/
lemma homOfLE_comp_chartOpenLift {V V' : X.Opens} (hV : V ≤ f.opensRange) (hV' : V' ≤ V) :
    X.homOfLE hV' ≫ chartOpenLift f hV = chartOpenLift f (hV'.trans hV) := by
  rw [← cancel_mono f, Category.assoc, chartOpenLift_fac, chartOpenLift_fac, Scheme.homOfLE_ι]

end ChartLift

end AlgebraicGeometry

namespace Stacks.SheafOfModules

open AlgebraicGeometry

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
  [∀ i, IsOpenImmersion (f i)] (mod : ∀ i, (Y i).Modules)

/-- **A chart module read over an open of the base inside the chart image.** This is where two
charts are compared: the chart modules live on different schemes, and an open of the base inside
both chart images, lifted through either chart, is the only common ground. -/
abbrev chartModule (i : ι) {V : S.Opens} (hV : V ≤ (f i).opensRange) : V.toScheme.Modules :=
  Scheme.Modules.restrict (mod i) (chartOpenLift (f i) hV)

/-- **The restriction of a comparison of two chart modules to a smaller open of the base.** -/
def chartModuleRestrict {i j : ι} {V V' : S.Opens} {hi : V ≤ (f i).opensRange}
    {hj : V ≤ (f j).opensRange} (hV' : V' ≤ V)
    (β : chartModule f mod i hi ⟶ chartModule f mod j hj) :
    chartModule f mod i (hV'.trans hi) ⟶ chartModule f mod j (hV'.trans hj) :=
  restrictChart hV' (homOfLE_comp_chartOpenLift (f i) hi hV')
    (homOfLE_comp_chartOpenLift (f j) hj hV') β

/-- **The conversion of a comparison of chart modules into a comparison of the pushforwards**, as
`Stacks.SheafOfModules.ModulesGlueData.ofOverlapIsoOfCocycle` reads it: over the overlap of two
chart images, with both chart modules pushed forward to the base. -/
def ofChartIsoHom (i j : ι)
    (β : chartModule f mod i (inf_le_left : chartOverlap f i j ≤ (f i).opensRange) ≅
      chartModule f mod j (inf_le_right : chartOverlap f i j ≤ (f j).opensRange)) :
    Scheme.Modules.restrict (pushforwardChart f mod i) (chartOverlap f i j).ι ≅
      Scheme.Modules.restrict (pushforwardChart f mod j) (chartOverlap f i j).ι :=
  restrictPushforwardIso (f i) (chartOpenLift (f i) inf_le_left) (chartOpenLift_fac _ _) (mod i) ≪≫
    β ≪≫ (restrictPushforwardIso (f j) (chartOpenLift (f j) inf_le_right)
      (chartOpenLift_fac _ _) (mod j)).symm

/-- **The restriction to the triple overlap of a converted comparison is the conversion of the
restricted comparison.** -/
lemma restrictLocal_ofChartIsoHom (i j : ι)
    (β : chartModule f mod i (inf_le_left : chartOverlap f i j ≤ (f i).opensRange) ≅
      chartModule f mod j (inf_le_right : chartOverlap f i j ≤ (f j).opensRange))
    {V' : S.Opens} (hT : V' ≤ chartOverlap f i j) :
    restrictLocal (ofChartIsoHom f mod i j β).hom hT =
      (restrictPushforwardIso (f i) (chartOpenLift (f i) (hT.trans inf_le_left))
          (chartOpenLift_fac _ _) (mod i)).hom ≫
        chartModuleRestrict f mod hT β.hom ≫
          (restrictPushforwardIso (f j) (chartOpenLift (f j) (hT.trans inf_le_right))
            (chartOpenLift_fac _ _) (mod j)).inv := by
  rw [restrictLocal_eq_restrictChart, ofChartIsoHom]
  rw [show (restrictPushforwardIso (f i) (chartOpenLift (f i) inf_le_left)
        (chartOpenLift_fac _ _) (mod i) ≪≫ β ≪≫
        (restrictPushforwardIso (f j) (chartOpenLift (f j) inf_le_right)
          (chartOpenLift_fac _ _) (mod j)).symm).hom =
      (restrictPushforwardIso (f i) (chartOpenLift (f i) inf_le_left)
          (chartOpenLift_fac _ _) (mod i)).hom ≫ β.hom ≫
        (restrictPushforwardIso (f j) (chartOpenLift (f j) inf_le_right)
          (chartOpenLift_fac _ _) (mod j)).inv from rfl]
  rw [restrictChart_comp (hpq' := homOfLE_comp_chartOpenLift (f i) inf_le_left hT),
    restrictChart_comp (hpq' := homOfLE_comp_chartOpenLift (f j) inf_le_right hT),
    restrictChart_restrictPushforwardIso_hom, restrictChart_restrictPushforwardIso_inv]
  rfl

namespace ModulesGlueData

/-- **A glueing datum of sheaves of modules from comparisons of the chart modules themselves.**
Let `f i : Y i ⟶ S` be a family of open immersions and `mod i` a sheaf of modules on each `Y i`.
An isomorphism, for each pair of charts, of the two chart modules read over the overlap of the
chart images, such that for each triple the restrictions of the three isomorphisms to the triple
overlap compose, is a glueing datum.

This is `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIsoOfCocycle` with its comparisons taken
between the chart modules rather than between their pushforwards to the base; the translation is
`AlgebraicGeometry.restrictChart_restrictPushforwardIso_hom`. Neither the images of the charts
nor the base is assumed to be anything in particular, and no cocycle on sections appears. -/
def ofChartIso
    (β : ∀ i j : ι,
      chartModule f mod i (inf_le_left : chartOverlap f i j ≤ (f i).opensRange) ≅
        chartModule f mod j (inf_le_right : chartOverlap f i j ≤ (f j).opensRange))
    (hcoc : ∀ i j k : ι,
      chartModuleRestrict f mod (chartTripleOverlap_le_fst f i j k) (β i j).hom ≫
          chartModuleRestrict f mod (chartTripleOverlap_le_snd f i j k) (β j k).hom =
        chartModuleRestrict f mod (chartTripleOverlap_le_out f i j k) (β i k).hom) :
    ModulesGlueData S f :=
  ofOverlapIsoOfCocycle f mod (fun i j ↦ ofChartIsoHom f mod i j (β i j)) (fun i j k ↦ by
    rw [restrictLocal_ofChartIsoHom f mod i j (β i j) (chartTripleOverlap_le_fst f i j k),
      restrictLocal_ofChartIsoHom f mod j k (β j k) (chartTripleOverlap_le_snd f i j k),
      restrictLocal_ofChartIsoHom f mod i k (β i k) (chartTripleOverlap_le_out f i j k),
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc _ _
        (restrictPushforwardIso (f k) (chartOpenLift (f k) _) (chartOpenLift_fac _ _) (mod k)).inv,
      hcoc i j k])

/-- The chart modules of `Stacks.SheafOfModules.ModulesGlueData.ofChartIso` are the given
ones. -/
@[simp]
lemma ofChartIso_mod
    (β : ∀ i j : ι,
      chartModule f mod i (inf_le_left : chartOverlap f i j ≤ (f i).opensRange) ≅
        chartModule f mod j (inf_le_right : chartOverlap f i j ≤ (f j).opensRange))
    (hcoc : ∀ i j k : ι,
      chartModuleRestrict f mod (chartTripleOverlap_le_fst f i j k) (β i j).hom ≫
          chartModuleRestrict f mod (chartTripleOverlap_le_snd f i j k) (β j k).hom =
        chartModuleRestrict f mod (chartTripleOverlap_le_out f i j k) (β i k).hom) :
    (ofChartIso f mod β hcoc).mod = mod :=
  rfl

/-- **The cocycle hypothesis of `Stacks.SheafOfModules.ModulesGlueData.ofChartIso` is
satisfiable**, so the construction is not vacuous: the identity comparisons of one chart module
satisfy it. -/
lemma ofChartIso_cocycle_of_id {i : ι} {V V' : S.Opens} (hV' : V' ≤ V)
    (hi : V ≤ (f i).opensRange) :
    chartModuleRestrict f mod (hi := hi) (hj := hi) hV'
        (𝟙 (chartModule f mod i hi)) = 𝟙 _ :=
  restrictChart_id _ _ _

/-- **The comparisons of the module glued by `Stacks.SheafOfModules.ModulesGlueData.ofChartIso`
with the chart modules are related to one another by the given comparisons `β`.**

`ofChartIso` records only its chart modules (`ofChartIso_mod`); this is the statement about the
glued module that a construction of a morphism *out of* it needs, and the reason it is cheap is
that the transition of the datum is by construction the sections map of `β i j` converted to the
pushforwards (`ofChartIsoHom`), so the general
`Stacks.SheafOfModules.ModulesGlueData.trans_chartSectionsIso` says it already. -/
theorem ofChartIso_trans_chartSectionsIso
    (β : ∀ i j : ι,
      chartModule f mod i (inf_le_left : chartOverlap f i j ≤ (f i).opensRange) ≅
        chartModule f mod j (inf_le_right : chartOverlap f i j ≤ (f j).opensRange))
    (hcoc : ∀ i j k : ι,
      chartModuleRestrict f mod (chartTripleOverlap_le_fst f i j k) (β i j).hom ≫
          chartModuleRestrict f mod (chartTripleOverlap_le_snd f i j k) (β j k).hom =
        chartModuleRestrict f mod (chartTripleOverlap_le_out f i j k) (β i k).hom)
    (i j : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange)
    (s : ToType ((ofChartIso f mod β hcoc).glued.val.obj (op V))) :
    localAppFun (ofChartIsoHom f mod i j (β i j)).hom V (le_inf hi hj)
        (((ofChartIso f mod β hcoc).chartSectionsIso i hi).hom s) =
      ((ofChartIso f mod β hcoc).chartSectionsIso j hj).hom s :=
  (ofChartIso f mod β hcoc).trans_chartSectionsIso i j hi hj s

end ModulesGlueData

end Stacks.SheafOfModules

end
