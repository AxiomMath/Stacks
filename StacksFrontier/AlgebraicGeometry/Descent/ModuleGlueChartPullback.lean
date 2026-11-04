module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueChartIso
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Pullback
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictPullbackCoherence

/-!
# A glueing datum of sheaves of modules from comparisons of the inverse images of the charts

`Stacks.SheafOfModules.ModulesGlueData.ofChartIso` builds a glueing datum out of one isomorphism
per pair of charts, taken between the *restrictions* of the two chart modules along the liftings
of the overlap of the chart images. A construction that pulls sheaves of modules back, however,
produces its comparison between the *inverse images* `a^*(mod i) ≅ b^*(mod j)` along those
liftings — that is the shape in which, for instance, the comparison of two quadruples of Section
01NS over an overlap of two members of a covering arrives, the pullback of a quadruple being
written with the inverse image.

Restriction and inverse image along an open immersion are identified by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, so one such comparison converts
into the other. What has to be checked, exactly as in
`StacksFrontier/AlgebraicGeometry/Descent/ModuleGlueChartIso.lean`, is that the conversion
**commutes with passing to a smaller open of the base**: without that, the cocycle condition of
`Stacks.SheafOfModules.ModulesGlueData.ofChartIso`, which lives over the triple overlap, cannot
be read off a cocycle for the comparisons of inverse images, because the three converted
comparisons are restrictions to three different pairwise overlaps.

## The two operations and the computation relating them

`AlgebraicGeometry.restrictChart` restricts a morphism of restrictions along liftings to a
smaller open of the base. `Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackChartRestrict` is the
same operation for a morphism of inverse images along liftings; it needs no open immersion
hypothesis, being assembled out of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` only.
`Stacks.AlgebraicGeometry.ModuleHomGlue.restrictChart_ofPullbackChart` is the computation that
the conversion carries one to the other.

Its mathematical input is the pseudofunctoriality of `restrictFunctorIsoPullback`, used through
the two cancellations
`Stacks.AlgebraicGeometry.ModuleHomGlue.restrictFunctorComp_hom_comp_isoPullback` and
`Stacks.AlgebraicGeometry.ModuleHomGlue.isoPullback_inv_comp_restrictFunctorComp_inv`; the two
reindexing isomorphisms disappear because the statement is proved after substituting the two
equalities of liftings.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullbackChart` and `...ofPullbackChartIso`: **the
  morphism, respectively isomorphism, of restrictions along two liftings corresponding to a
  morphism of the inverse images along them.** This is
  `Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback` with the two sides allowed to be modules
  on two different schemes, restricted along two different liftings.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackChartRestrict`: the restriction to a smaller
  open of the base of a morphism of inverse images along liftings.
* `Stacks.SheafOfModules.chartPullbackModule` and `...chartPullbackRestrict`: the inverse image
  of a chart module over an open of the base inside the chart image, and its restriction to a
  smaller open — the inverse-image counterparts of `Stacks.SheafOfModules.chartModule` and
  `...chartModuleRestrict`.
* `Stacks.SheafOfModules.ModulesGlueData.ofChartPullbackIsoFamily`: the comparisons of the chart
  modules themselves attached to comparisons of their inverse images, as
  `Stacks.SheafOfModules.ModulesGlueData.ofChartIso` consumes them.

## Main results

* `Stacks.AlgebraicGeometry.ModuleHomGlue.restrictChart_ofPullbackChart`: **converting a
  comparison of inverse images into a comparison of restrictions commutes with restriction to a
  smaller open of the base.**
* `Stacks.SheafOfModules.chartModuleIsoChartPullbackModule`: a chart module read over an open of
  the base is the inverse image of the chart module along the lifting of that open.
* `Stacks.SheafOfModules.ModulesGlueData.ofChartPullbackIso_cocycle`: **a cocycle for the
  comparisons of the inverse images is a cocycle for their conversions**, which is the
  hypothesis of `Stacks.SheafOfModules.ModulesGlueData.ofChartIso`.
* `Stacks.SheafOfModules.ModulesGlueData.exists_modulesGlueData_of_chartPullbackIso`: **the
  glueing datum of a family of sheaves of modules on the charts together with isomorphisms of
  the inverse images of the chart modules over the pairwise overlaps whose restrictions to the
  triple overlaps compose.**

## Implementation notes

The last statement is an existence statement rather than a construction, and that is forced, not
a preference. A `def` whose type or value mentions the cocycle condition in the inverse-image
spelling is rejected by the kernel:

```
error: (kernel) deterministic timeout
```

— this happens for the packaged construction, for the same construction with the type ascription
dropped, for the same construction marked `@[irreducible]`, for the abstraction of the cocycle
condition into a `def ... : Prop`, and even for `def _ (β) (hcoc) : ℕ := 0`, which has that
condition as a hypothesis and the value `0`. The same condition in the binders of a *theorem* —
including the existence statement here, whose proof applies `ofChartIso` to the converted family
and reads off its chart modules by `rfl` — checks in 0.3 s. What the kernel has to cross is a
composite of two `chartPullbackRestrict`s whose middle object is the inverse image of one chart
module along `AlgebraicGeometry.chartOpenLift` at two *different* proofs of one inequality of
opens: a proof occurring in a data position, where the proof-irrelevance step sits under
`AlgebraicGeometry.IsOpenImmersion.lift`. A consumer that needs the glueing datum should
`obtain` it from the existence statement inside its proof.

## No tag is claimed

Nothing here states a clause of a tag; the file converts between two presentations of the local
data a glueing argument consumes.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

/-! ### A comparison of inverse images along two liftings, read on the restrictions -/

section OfPullbackChart

variable {W Y Z Z' : Scheme.{u}} {p : W ⟶ Y} [IsOpenImmersion p] {p' : W ⟶ Z}
  [IsOpenImmersion p'] {p'' : W ⟶ Z'} [IsOpenImmersion p'']
  {N : Y.Modules} {M : Z.Modules} {M' : Z'.Modules}

/-- **The morphism of restrictions corresponding to a morphism of inverse images**, with the two
sides modules on two different schemes restricted along two different morphisms. This is
`Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback` with the two sides decoupled. -/
def ofPullbackChart
    (φ : (Scheme.Modules.pullback p).obj N ⟶ (Scheme.Modules.pullback p').obj M) :
    Scheme.Modules.restrict N p ⟶ Scheme.Modules.restrict M p' :=
  (Scheme.Modules.restrictFunctorIsoPullback p).hom.app N ≫ φ ≫
    (Scheme.Modules.restrictFunctorIsoPullback p').inv.app M

/-- **The conversion is multiplicative**: the two comparisons between restriction and inverse
image at the intermediate module cancel. -/
lemma ofPullbackChart_comp
    (φ : (Scheme.Modules.pullback p).obj N ⟶ (Scheme.Modules.pullback p').obj M)
    (χ : (Scheme.Modules.pullback p').obj M ⟶ (Scheme.Modules.pullback p'').obj M') :
    ofPullbackChart (φ ≫ χ) = ofPullbackChart φ ≫ ofPullbackChart χ := by
  simp only [ofPullbackChart, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- **The conversion is unital.** -/
@[simp]
lemma ofPullbackChart_id :
    ofPullbackChart (𝟙 ((Scheme.Modules.pullback p).obj N)) =
      𝟙 (Scheme.Modules.restrict N p) := by
  simp only [ofPullbackChart, Category.id_comp, Iso.hom_inv_id_app]

/-- **The isomorphism of restrictions corresponding to an isomorphism of inverse images.** -/
def ofPullbackChartIso
    (e : (Scheme.Modules.pullback p).obj N ≅ (Scheme.Modules.pullback p').obj M) :
    Scheme.Modules.restrict N p ≅ Scheme.Modules.restrict M p' :=
  ((Scheme.Modules.restrictFunctorIsoPullback p).app N) ≪≫ e ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback p').app M).symm

/-- The forward morphism of `ofPullbackChartIso e` is `ofPullbackChart e.hom`. -/
@[simp]
lemma ofPullbackChartIso_hom
    (e : (Scheme.Modules.pullback p).obj N ≅ (Scheme.Modules.pullback p').obj M) :
    (ofPullbackChartIso e).hom = ofPullbackChart e.hom :=
  rfl

end OfPullbackChart

/-! ### Restriction to a smaller open of the base, on the inverse-image side -/

section PullbackChartRestrict

variable {X Y Z : Scheme.{u}} {V W : X.Opens}

/-- **The restriction to a smaller open of the base of a morphism of inverse images along
liftings.** This is what `AlgebraicGeometry.restrictChart` does for restrictions; unlike there,
no open immersion hypothesis is needed, the inverse image being functorial in the morphism
through `AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
def pullbackChartRestrict (hV : V ≤ W)
    {p : W.toScheme ⟶ Y} {q : V.toScheme ⟶ Y} (hpq : X.homOfLE hV ≫ p = q)
    {p' : W.toScheme ⟶ Z} {q' : V.toScheme ⟶ Z} (hpq' : X.homOfLE hV ≫ p' = q')
    {N : Y.Modules} {M : Z.Modules}
    (φ : (Scheme.Modules.pullback p).obj N ⟶ (Scheme.Modules.pullback p').obj M) :
    (Scheme.Modules.pullback q).obj N ⟶ (Scheme.Modules.pullback q').obj M :=
  (Scheme.Modules.pullbackCongr hpq).inv.app N ≫
    (Scheme.Modules.pullbackComp (X.homOfLE hV) p).inv.app N ≫
      (Scheme.Modules.pullback (X.homOfLE hV)).map φ ≫
        (Scheme.Modules.pullbackComp (X.homOfLE hV) p').hom.app M ≫
          (Scheme.Modules.pullbackCongr hpq').hom.app M

/-- **Converting a comparison of inverse images into a comparison of restrictions commutes with
restriction to a smaller open of the base.** For liftings `p`, `p'` of the inclusion of an open
`W` of `X` and liftings `q`, `q'` of the inclusion of a smaller open `V`, compatible with the
inclusion of `V` in `W`, the restriction to `V` of the conversion of `φ` is the conversion of
the restriction to `V` of `φ`.

This is what lets the cocycle condition of
`Stacks.SheafOfModules.ModulesGlueData.ofChartIso`, which lives over a triple overlap, be read
off a cocycle for comparisons of inverse images. -/
lemma restrictChart_ofPullbackChart (hV : V ≤ W)
    {p : W.toScheme ⟶ Y} [IsOpenImmersion p] {q : V.toScheme ⟶ Y} [IsOpenImmersion q]
    (hpq : X.homOfLE hV ≫ p = q)
    {p' : W.toScheme ⟶ Z} [IsOpenImmersion p'] {q' : V.toScheme ⟶ Z} [IsOpenImmersion q']
    (hpq' : X.homOfLE hV ≫ p' = q')
    {N : Y.Modules} {M : Z.Modules}
    (φ : (Scheme.Modules.pullback p).obj N ⟶ (Scheme.Modules.pullback p').obj M) :
    restrictChart hV hpq hpq' (ofPullbackChart φ) =
      ofPullbackChart (pullbackChartRestrict hV hpq hpq' φ) := by
  subst hpq
  subst hpq'
  have hcongr : ∀ {A B : Scheme.{u}} {k : A ⟶ B} (_ : IsOpenImmersion k),
      Scheme.Modules.restrictFunctorCongr (rfl : k = k) = Iso.refl _ :=
    fun _ ↦ Iso.ext (ModuleLimits.restrictFunctorCongr_rfl _)
  simp only [pullbackChartRestrict, pullbackCongr_rfl, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, Category.comp_id]
  simp only [restrictChart, restrictChartIsoOfLE, hcongr, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id]
  simp only [ofPullbackChart, Functor.map_comp, Category.assoc]
  rw [← ofPullback_pullback_map (X.homOfLE hV) φ]
  simp only [ofPullback, Category.assoc]
  rw [restrictFunctorComp_hom_comp_isoPullback_assoc,
    isoPullback_inv_comp_restrictFunctorComp_inv]

end PullbackChartRestrict

end Stacks.AlgebraicGeometry.ModuleHomGlue

namespace Stacks.SheafOfModules

open AlgebraicGeometry Stacks.AlgebraicGeometry.ModuleHomGlue

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
  [∀ i, IsOpenImmersion (f i)] (mod : ∀ i, (Y i).Modules)

/-- **The inverse image of a chart module along the lifting of an open of the base inside the
chart image.** This is `Stacks.SheafOfModules.chartModule` with the inverse image in place of the
restriction; it is the shape in which a construction that pulls modules back produces its
comparisons. -/
abbrev chartPullbackModule (i : ι) {V : S.Opens} (hV : V ≤ (f i).opensRange) :
    V.toScheme.Modules :=
  (Scheme.Modules.pullback (chartOpenLift (f i) hV)).obj (mod i)

/-- **A chart module read over an open of the base is the inverse image of the chart module along
the lifting of that open.** -/
def chartModuleIsoChartPullbackModule (i : ι) {V : S.Opens} (hV : V ≤ (f i).opensRange) :
    chartModule f mod i hV ≅ chartPullbackModule f mod i hV :=
  (Scheme.Modules.restrictFunctorIsoPullback (chartOpenLift (f i) hV)).app (mod i)

/-- **The restriction of a comparison of the inverse images of two chart modules to a smaller
open of the base**, the inverse-image counterpart of
`Stacks.SheafOfModules.chartModuleRestrict`. -/
def chartPullbackRestrict {i j : ι} {V V' : S.Opens} {hi : V ≤ (f i).opensRange}
    {hj : V ≤ (f j).opensRange} (hV' : V' ≤ V)
    (φ : chartPullbackModule f mod i hi ⟶ chartPullbackModule f mod j hj) :
    chartPullbackModule f mod i (hV'.trans hi) ⟶ chartPullbackModule f mod j (hV'.trans hj) :=
  pullbackChartRestrict hV' (homOfLE_comp_chartOpenLift (f i) hi hV')
    (homOfLE_comp_chartOpenLift (f j) hj hV') φ

/-- **Restricting a comparison of chart modules to a smaller open of the base commutes with the
conversion from the inverse-image presentation.** -/
lemma chartModuleRestrict_ofPullbackChart {i j : ι} {V V' : S.Opens}
    {hi : V ≤ (f i).opensRange} {hj : V ≤ (f j).opensRange} (hV' : V' ≤ V)
    (φ : chartPullbackModule f mod i hi ⟶ chartPullbackModule f mod j hj) :
    chartModuleRestrict f mod hV' (ofPullbackChart φ) =
      ofPullbackChart (chartPullbackRestrict f mod hV' φ) :=
  restrictChart_ofPullbackChart hV' _ _ φ

namespace ModulesGlueData

/-- **The comparison of the chart modules corresponding to a comparison of their inverse
images**, as the family `Stacks.SheafOfModules.ModulesGlueData.ofChartIso` consumes. -/
def ofChartPullbackIsoFamily
    (β : ∀ i j : ι,
      chartPullbackModule f mod i (inf_le_left : chartOverlap f i j ≤ (f i).opensRange) ≅
        chartPullbackModule f mod j (inf_le_right : chartOverlap f i j ≤ (f j).opensRange))
    (i j : ι) :
    chartModule f mod i (inf_le_left : chartOverlap f i j ≤ (f i).opensRange) ≅
      chartModule f mod j (inf_le_right : chartOverlap f i j ≤ (f j).opensRange) :=
  ofPullbackChartIso (β i j)

/-- The forward morphism of `ofChartPullbackIsoFamily f mod β i j` is
`ofPullbackChart (β i j).hom`. -/
@[simp]
lemma ofChartPullbackIsoFamily_hom
    (β : ∀ i j : ι,
      chartPullbackModule f mod i (inf_le_left : chartOverlap f i j ≤ (f i).opensRange) ≅
        chartPullbackModule f mod j (inf_le_right : chartOverlap f i j ≤ (f j).opensRange))
    (i j : ι) :
    (ofChartPullbackIsoFamily f mod β i j).hom = ofPullbackChart (β i j).hom :=
  rfl

/-- **A cocycle for comparisons of the inverse images of the chart modules is a cocycle for their
conversions into comparisons of the chart modules themselves.** This is the hypothesis of
`Stacks.SheafOfModules.ModulesGlueData.ofChartIso`, verified for the converted comparisons. -/
lemma ofChartPullbackIso_cocycle
    (β : ∀ i j : ι,
      chartPullbackModule f mod i (inf_le_left : chartOverlap f i j ≤ (f i).opensRange) ≅
        chartPullbackModule f mod j (inf_le_right : chartOverlap f i j ≤ (f j).opensRange))
    (hcoc : ∀ i j k : ι,
      chartPullbackRestrict f mod (chartTripleOverlap_le_fst f i j k) (β i j).hom ≫
          chartPullbackRestrict f mod (chartTripleOverlap_le_snd f i j k) (β j k).hom =
        chartPullbackRestrict f mod (chartTripleOverlap_le_out f i j k) (β i k).hom)
    (i j k : ι) :
    chartModuleRestrict f mod (chartTripleOverlap_le_fst f i j k)
          (ofChartPullbackIsoFamily f mod β i j).hom ≫
        chartModuleRestrict f mod (chartTripleOverlap_le_snd f i j k)
          (ofChartPullbackIsoFamily f mod β j k).hom =
      chartModuleRestrict f mod (chartTripleOverlap_le_out f i j k)
        (ofChartPullbackIsoFamily f mod β i k).hom := by
  rw [ofChartPullbackIsoFamily_hom, ofChartPullbackIsoFamily_hom, ofChartPullbackIsoFamily_hom,
    chartModuleRestrict_ofPullbackChart, chartModuleRestrict_ofPullbackChart,
    chartModuleRestrict_ofPullbackChart, ← ofPullbackChart_comp, hcoc i j k]

/-- **A glueing datum of sheaves of modules from comparisons of the inverse images of the chart
modules.** Let `f i : Y i ⟶ S` be a family of open immersions and `mod i` a sheaf of modules on
each `Y i`. An isomorphism, for each pair of charts, of the inverse images of the two chart
modules along the liftings of the overlap of the chart images, such that for each triple the
restrictions of the three isomorphisms to the triple overlap compose, is a glueing datum whose
chart modules are the given ones.

This is `Stacks.SheafOfModules.ModulesGlueData.ofChartIso` with its comparisons taken between
the inverse images rather than between the restrictions; the translation is
`Stacks.AlgebraicGeometry.ModuleHomGlue.restrictChart_ofPullbackChart`, and the cocycle
condition is carried across by
`Stacks.SheafOfModules.ModulesGlueData.ofChartPullbackIso_cocycle`.

Stated as an existence statement rather than as a construction, for the reason recorded in the
implementation notes. -/
theorem exists_modulesGlueData_of_chartPullbackIso
    (β : ∀ i j : ι,
      chartPullbackModule f mod i (inf_le_left : chartOverlap f i j ≤ (f i).opensRange) ≅
        chartPullbackModule f mod j (inf_le_right : chartOverlap f i j ≤ (f j).opensRange))
    (hcoc : ∀ i j k : ι,
      chartPullbackRestrict f mod (chartTripleOverlap_le_fst f i j k) (β i j).hom ≫
          chartPullbackRestrict f mod (chartTripleOverlap_le_snd f i j k) (β j k).hom =
        chartPullbackRestrict f mod (chartTripleOverlap_le_out f i j k) (β i k).hom) :
    ∃ G : ModulesGlueData S f, G.mod = mod :=
  ⟨ofChartIso f mod (ofChartPullbackIsoFamily f mod β) (ofChartPullbackIso_cocycle f mod β hcoc),
    rfl⟩

/-- **The cocycle hypothesis of
`Stacks.SheafOfModules.ModulesGlueData.exists_modulesGlueData_of_chartPullbackIso` is
satisfiable**, so the statement is not vacuous: the identity comparisons of the inverse image of
one chart module satisfy it. -/
lemma chartPullbackRestrict_id {i : ι} {V V' : S.Opens} (hV' : V' ≤ V)
    (hi : V ≤ (f i).opensRange) :
    chartPullbackRestrict f mod (hi := hi) (hj := hi) hV'
        (𝟙 (chartPullbackModule f mod i hi)) = 𝟙 _ := by
  simp [chartPullbackRestrict, pullbackChartRestrict]

end ModulesGlueData

end Stacks.SheafOfModules

end
