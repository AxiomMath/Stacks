module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartLocalRefinement

/-!
# The chart comparisons of a glued module as comparisons of inverse images

A `Stacks.SheafOfModules.ModulesGlueData` compares its glued module with the `i`-th chart module
by `...ModulesGlueData.chartIso`, an isomorphism of the **restriction** of the glued module along
the `i`-th chart with that chart module, and the relation between two such comparisons is
`...ModulesGlueData.ofChartIso_restrictFunctor_map_chartAdjunct`, an equation of morphisms of
restrictions over an open of the base. A construction whose local data are morphisms of **inverse
images** — the glueing of the map `ψ` of a quadruple in step (1) of the proof of Tag 01NV — needs
both in the inverse-image vocabulary. This file makes the two crossings.

## The two crossings

`...ModulesGlueData.gluedPullbackIso` is the first: `chartIso` read across
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, which is the comparison of the
restriction along an open immersion with the inverse image.

The second is `...RelativeProjQcohSheaf.refineChartIso_trans_chartWitness`: over a common
refinement of two charts the two identifications differ by
`...RelativeProjQcohSheaf.Quadruple.chartWitness`. The conversion in both directions is
`...ModuleHomGlue.ofPullbackChart`, which is injective; what has to be proved is that it carries
`...RelativeProjQcohSheaf.refineChartIso` of `gluedPullbackIso` to the restriction of the
transposed comparison `...ModulesGlueData.chartAdjunct`, and that is
`...ModulesGlueData.ofPullbackChart_refineChartIso_gluedPullbackIso`. Its two halves are
`...ModuleHomGlue.ofPullbackChart_refineChartIso`, whose content is the pseudofunctoriality of
`restrictFunctorIsoPullback` in the form `...ModuleHomGlue.isoPullback_congr_comp`, and
`...ModulesGlueData.restrictFunctor_map_chartAdjunct_comp_restrictPushforwardIso`, which is the
adjunction triangle of `chartAdjunct` read over a smaller open through two naturality squares.

## Main definitions

* `Stacks.SheafOfModules.ModulesGlueData.gluedPullbackIso`: **the comparison of the glued module
  with a chart module, as a comparison of inverse images.**

## Main results

* `Stacks.AlgebraicGeometry.ModuleHomGlue.isoPullback_congr_comp`: the contraction of an iterated
  inverse image, read on restrictions, is the comparison of the iterated restriction.
* `...ModuleHomGlue.ofPullbackChart_refineChartIso` and
  `...ModuleHomGlue.ofPullbackChart_injective`.
* `...ModulesGlueData.restrictFunctor_map_chartAdjunct_comp_restrictPushforwardIso` and
  `...ModulesGlueData.ofPullbackChart_refineChartIso_gluedPullbackIso`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.refineChartIso_trans_chartWitness`: **the two
  identifications of the glued module of a family of quadruples with the chart modules over a
  common refinement of two charts differ by `...Quadruple.chartWitness`**, as an equation of
  isomorphisms of inverse images. This is the second of the two vocabulary crossings that stood
  between the glueing tools and the local data of the glueing of `ψ`.

## Implementation notes

Every collapse is an `exact` against a helper stated in a bare category with every object and
morphism free, and every application of `ofPullbackChart` names its two liftings: left to
unification the elaborator unfolds `AlgebraicGeometry.chartOpenLift` to
`AlgebraicGeometry.IsOpenImmersion.lift` and then fails to find `IsOpenImmersion` for the
unfolded term.

## No tag is claimed

Nothing here states a clause of a tag; the file translates two comparisons this repository
already has between two spellings of the inverse image.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition

/-- Cancelling an inverse on the right of a composite, stated in a bare category with every
object and morphism free. -/
private theorem rightCancelInv {C : Type*} [Category C] {X Y Z : C}
    (x : X ⟶ Y) (i : Y ⟶ Z) (j : Z ⟶ Y) (y : X ⟶ Z)
    (hij : i ≫ j = CategoryStruct.id Y) (h : x ≫ i = y) : x = y ≫ j := by
  rw [← h, Category.assoc, hij, Category.comp_id]

/-- Collapsing two naturality squares and a triangle, stated in a bare category with every object
and morphism free. -/
private theorem naturalityCollapse {C : Type*} [Category C] {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ : C}
    (fb : X₁ ⟶ X₂) (cg : X₂ ⟶ X₃) (cp : X₃ ⟶ X₄) (fkc : X₄ ⟶ Y₃)
    (cg' : X₁ ⟶ Y₁) (fkg : Y₁ ⟶ X₃) (cp' : Y₁ ⟶ Y₂) (fkfi : Y₂ ⟶ X₄) (fkchart : Y₂ ⟶ Y₃)
    (h1 : fb ≫ cg = cg' ≫ fkg) (h2 : fkg ≫ cp = cp' ≫ fkfi) (h3 : fkfi ≫ fkc = fkchart) :
    fb ≫ cg ≫ cp ≫ fkc = cg' ≫ cp' ≫ fkchart := by
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc fkg, h2, Category.assoc, h3]

/-- Moving a naturality square out of a four-fold composite, stated in a bare category with every
object and morphism free. -/
private theorem reassocNat {C : Type*} [Category C] {X A B D E F G : C}
    (ib : X ⟶ A) (cg : A ⟶ B) (cc : B ⟶ D) (fke : D ⟶ E) (ikn : E ⟶ F)
    (ikm : D ⟶ G) (fkre : G ⟶ F) (h : fke ≫ ikn = ikm ≫ fkre) :
    ib ≫ (cg ≫ cc ≫ fke) ≫ ikn = (ib ≫ cg ≫ cc ≫ ikm) ≫ fkre := by
  simp only [Category.assoc]
  rw [h]

/-- Inserting a cancelling pair into a four-fold composite and collapsing it against a given
identity, stated in a bare category with every object and morphism free. -/
private theorem insertUnitCollapse {C : Type*} [Category C] {X A B B' D E F G : C}
    (ib : X ⟶ A) (cg : A ⟶ B) (cc : B ⟶ D) (ikm : D ⟶ E)
    (u : E ⟶ F) (v : F ⟶ E) (w : E ⟶ G) (p : X ⟶ B') (q : B' ⟶ F) (t : F ⟶ G)
    (huv : u ≫ v = CategoryStruct.id E)
    (hA : ib ≫ cg ≫ cc ≫ ikm ≫ u = p ≫ q) (ht : v ≫ w = t) :
    (ib ≫ cg ≫ cc ≫ ikm) ≫ w = p ≫ q ≫ t := by
  rw [rightCancelInv (ib ≫ cg ≫ cc ≫ ikm) u v _ huv (by simpa only [Category.assoc] using hA)]
  simp only [Category.assoc, ht]

/-! ### The comparison between restriction and inverse image over a refinement -/

section Refine

variable {T Z₁ Z : Scheme.{u}} (g : Z₁ ⟶ T) [IsOpenImmersion g] (k : Z ⟶ Z₁)
  [IsOpenImmersion k] {b : Z ⟶ T} [IsOpenImmersion b] (hk : k ≫ g = b)

/-- **The contraction of an iterated inverse image, read on restrictions, is the comparison
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` of the iterated restriction.** Both ends
of the five-fold composite are the comparison
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and the identity is the
pseudofunctoriality of that comparison in the form
`...ModuleHomGlue.isoPullback_inv_comp_restrictFunctorComp_inv`. -/
public theorem isoPullback_congr_comp (M : T.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback b).hom.app M ≫
          (Scheme.Modules.pullbackCongr hk).inv.app M ≫
          (Scheme.Modules.pullbackComp k g).inv.app M ≫
          (Scheme.Modules.restrictFunctorIsoPullback k).inv.app
            ((Scheme.Modules.pullback g).obj M) ≫
          (Scheme.Modules.restrictFunctor k).map
            ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M) =
      (Scheme.Modules.restrictFunctorCongr hk).inv.app M ≫
        (Scheme.Modules.restrictFunctorComp k g).hom.app M := by
  subst hk
  have hpc : (Scheme.Modules.pullbackCongr (rfl : k ≫ g = k ≫ g)).inv.app M =
      CategoryStruct.id ((Scheme.Modules.pullback (k ≫ g)).obj M) := by
    rw [pullbackCongr_rfl]
    rfl
  have hrc : (Scheme.Modules.restrictFunctorCongr (rfl : k ≫ g = k ≫ g)).inv.app M =
      CategoryStruct.id (Scheme.Modules.restrict M (k ≫ g)) := by
    rw [show Scheme.Modules.restrictFunctorCongr (rfl : k ≫ g = k ≫ g) = Iso.refl _ from
      Iso.ext (ModuleLimits.restrictFunctorCongr_rfl _)]
    rfl
  rw [hpc, hrc, Category.id_comp, Category.id_comp]
  have key' : (Scheme.Modules.restrictFunctorIsoPullback k).inv.app
          ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.restrictFunctor k).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M) =
      ((Scheme.Modules.pullbackComp k g).hom.app M ≫
          (Scheme.Modules.restrictFunctorIsoPullback (k ≫ g)).inv.app M) ≫
        (Scheme.Modules.restrictFunctorComp k g).hom.app M :=
    rightCancelInv _ _ _ _ ((Scheme.Modules.restrictFunctorComp k g).inv_hom_id_app M)
      ((Category.assoc _ _ _).trans (isoPullback_inv_comp_restrictFunctorComp_inv g k M))
  rw [key']
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]

end Refine

/-- **The identification of the inverse image of the chart module over a refinement, read on
restrictions.** `...RelativeProjQcohSheaf.refineChartIso` is the comparison
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` of the iterated restriction followed by
the restriction of the given identification. -/
public theorem ofPullbackChart_refineChartIso {T Z₁ Z : Scheme.{u}} (g : Z₁ ⟶ T)
    [IsOpenImmersion g] (k : Z ⟶ Z₁) [IsOpenImmersion k] {b : Z ⟶ T} [IsOpenImmersion b]
    (hk : k ≫ g = b) (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M]
    {N : SheafOfModules.{u} (structureRingSheaf Z₁.toRingedSpace)}
    (e : (pullbackFunctor (ringedSpaceHom g)).obj M ≅ N) :
    ofPullbackChart
        ((RelativeProjQcohSheaf.refineChartIso g k hk M e).hom) =
      (Scheme.Modules.restrictFunctorCongr hk).inv.app M ≫
        (Scheme.Modules.restrictFunctorComp k g).hom.app M ≫
        (Scheme.Modules.restrictFunctor k).map
          (((Scheme.Modules.restrictFunctorIsoPullback g).app M ≪≫ e).hom) := by
  have hcc : (compCmp k g M).inv =
      (Scheme.Modules.pullbackComp k g).inv.app M :=
    (RelativeProjQcohSheaf.compComparison_eq_compCmp_inv k g M).symm.trans
      (RelativeProjQcohSheaf.compComparison_eq_pullbackComp_inv k g M)
  have hstep1 : ofPullbackChart ((RelativeProjQcohSheaf.refineChartIso g k hk M e).hom) =
      (Scheme.Modules.restrictFunctorIsoPullback b).hom.app M ≫
        ((Scheme.Modules.pullbackCongr hk).inv.app M ≫
          (Scheme.Modules.pullbackComp k g).inv.app M ≫
          (Scheme.Modules.pullback k).map e.hom) ≫
        (Scheme.Modules.restrictFunctorIsoPullback k).inv.app N :=
    congrArg (fun z => (Scheme.Modules.restrictFunctorIsoPullback b).hom.app M ≫
      ((Scheme.Modules.pullbackCongr hk).inv.app M ≫ z ≫
        (Scheme.Modules.pullback k).map e.hom) ≫
      (Scheme.Modules.restrictFunctorIsoPullback k).inv.app N) hcc
  refine hstep1.trans ?_
  refine (reassocNat _ _ _ _ _ _ _
    ((Scheme.Modules.restrictFunctorIsoPullback k).inv.naturality e.hom)).trans ?_
  exact insertUnitCollapse _ _ _ _
    ((Scheme.Modules.restrictFunctor k).map
      ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M))
    ((Scheme.Modules.restrictFunctor k).map
      ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M))
    _ _ _ _
    (((Scheme.Modules.restrictFunctor k).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.restrictFunctor k).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).inv_hom_id_app M)).trans
        ((Scheme.Modules.restrictFunctor k).map_id _)))
    (isoPullback_congr_comp g k hk M)
    ((Scheme.Modules.restrictFunctor k).map_comp _ _).symm

/-- The conversion of a comparison of inverse images into one of restrictions is injective, being
conjugation by isomorphisms. -/
public theorem ofPullbackChart_injective {W Y Z : Scheme.{u}} {p : W ⟶ Y} [IsOpenImmersion p]
    {p' : W ⟶ Z} [IsOpenImmersion p'] {N : Y.Modules} {M : Z.Modules}
    {φ₁ φ₂ : (Scheme.Modules.pullback p).obj N ⟶ (Scheme.Modules.pullback p').obj M}
    (h : ofPullbackChart φ₁ = ofPullbackChart φ₂) : φ₁ = φ₂ := by
  rw [ofPullbackChart, ofPullbackChart] at h
  exact (cancel_mono _).mp ((cancel_epi _).mp h)


end Stacks.AlgebraicGeometry.ModuleHomGlue

namespace Stacks.SheafOfModules.ModulesGlueData

open AlgebraicGeometry Stacks.AlgebraicGeometry.ModuleHomGlue

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ S}
  [∀ i, IsOpenImmersion (f i)]

/-- **The comparison of the glued module with a chart module, as a comparison of inverse
images.** This is `Stacks.SheafOfModules.ModulesGlueData.chartIso`, which is stated for
`AlgebraicGeometry.Scheme.Modules.restrict`, carried across
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. It is the identification a
construction whose local data are morphisms of inverse images consumes. -/
def gluedPullbackIso (D : ModulesGlueData S f) (i : ι) :
    (Scheme.Modules.pullback (f i)).obj D.glued ≅ D.mod i :=
  ((Scheme.Modules.restrictFunctorIsoPullback (f i)).app D.glued).symm ≪≫ D.chartIso i

/-- **The restriction to a smaller open of the base of the transposed comparison
`Stacks.SheafOfModules.ModulesGlueData.chartAdjunct`, followed by the comparison of the
pushforward with the chart module there, is the comparison
`Stacks.SheafOfModules.ModulesGlueData.chartIso` restricted along the lifting.**

This is the adjunction triangle `...ModulesGlueData.restrictFunctor_map_chartAdjunct` read over
a smaller open: the two naturality squares of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` move the transposed comparison past the
two comparisons of restrictions, and the triangle closes what is left. -/
theorem restrictFunctor_map_chartAdjunct_comp_restrictPushforwardIso (D : ModulesGlueData S f)
    (i : ι) {Z : Scheme.{u}} (k : Z ⟶ Y i) [IsOpenImmersion k] {b : Z ⟶ S} [IsOpenImmersion b]
    (hk : k ≫ f i = b) :
    (Scheme.Modules.restrictFunctor b).map (D.chartAdjunct i) ≫
        (restrictPushforwardIso (f i) k hk (D.mod i)).hom =
      (Scheme.Modules.restrictFunctorCongr hk).inv.app D.glued ≫
        (Scheme.Modules.restrictFunctorComp k (f i)).hom.app D.glued ≫
        (Scheme.Modules.restrictFunctor k).map (D.chartIso i).hom := by
  have hnat1 := (Scheme.Modules.restrictFunctorCongr hk).inv.naturality (D.chartAdjunct i)
  have hnat2 := (Scheme.Modules.restrictFunctorComp k (f i)).hom.naturality (D.chartAdjunct i)
  have htri : (Scheme.Modules.restrictFunctor k).map
        ((Scheme.Modules.restrictFunctor (f i)).map (D.chartAdjunct i)) ≫
      (Scheme.Modules.restrictFunctor k).map
        ((Scheme.Modules.restrictFunctorAdjCounitIso (f i)).hom.app (D.mod i)) =
      (Scheme.Modules.restrictFunctor k).map (D.chartIso i).hom :=
    ((Scheme.Modules.restrictFunctor k).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.restrictFunctor k).map
        (D.restrictFunctor_map_chartAdjunct i))
  rw [restrictPushforwardIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
  exact Stacks.AlgebraicGeometry.ModuleHomGlue.naturalityCollapse _ _ _ _ _ _ _ _ _
    hnat1 hnat2 htri


/-- **The identification of the inverse image of the glued module with a chart module, read over
a refinement of the chart, is the restriction of the transposed comparison.** This is
`...ModuleHomGlue.ofPullbackChart_refineChartIso` at
`...ModulesGlueData.gluedPullbackIso` together with
`...ModulesGlueData.restrictFunctor_map_chartAdjunct_comp_restrictPushforwardIso`. -/
theorem ofPullbackChart_refineChartIso_gluedPullbackIso (D : ModulesGlueData S f)
    [Stacks.SheafOfModules.IsInvertible S.toRingedSpace.presheaf
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isSheafStruct S) D.glued]
    (i : ι) {Z : Scheme.{u}} (k : Z ⟶ Y i) [IsOpenImmersion k] {b : Z ⟶ S}
    [IsOpenImmersion b] (hk : k ≫ f i = b) :
    ofPullbackChart
        ((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.refineChartIso (f i) k hk D.glued
          (D.gluedPullbackIso i)).hom) =
      (Scheme.Modules.restrictFunctor b).map (D.chartAdjunct i) ≫
        (restrictPushforwardIso (f i) k hk (D.mod i)).hom := by
  have hself : (Scheme.Modules.restrictFunctorIsoPullback (f i)).app D.glued ≪≫
      D.gluedPullbackIso i = D.chartIso i := by
    rw [gluedPullbackIso, ← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  refine (ofPullbackChart_refineChartIso (f i) k hk D.glued (D.gluedPullbackIso i)).trans ?_
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.restrictFunctorCongr hk).inv.app D.glued ≫
      (Scheme.Modules.restrictFunctorComp k (f i)).hom.app D.glued ≫
      (Scheme.Modules.restrictFunctor k).map (Iso.hom z)) hself) ?_
  exact (D.restrictFunctor_map_chartAdjunct_comp_restrictPushforwardIso i k hk).symm

end Stacks.SheafOfModules.ModulesGlueData

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.SheafOfModules Stacks.AlgebraicGeometry.ModuleHomGlue

variable {T S : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-- **The second vocabulary crossing: the two identifications of the glued module with the chart
modules over a common refinement of two charts differ by `...Quadruple.chartWitness`.**

`...RelativeProjQcohSheaf.quadrupleGlueData_restrictFunctor_map_chartAdjunct` says this for the
transposed comparisons `...ModulesGlueData.chartAdjunct`, as an equation of morphisms of
restrictions over an open of `T`; here it is read for the identifications of *inverse images*
along the two morphisms out of the refinement, which is the form
`...RelativeProjQcohSheaf.localApp_chartLocalApp_eq` consumes. The conversion is
`...ModuleHomGlue.ofPullbackChart`, which is injective, together with
`...ModulesGlueData.ofPullbackChart_refineChartIso_gluedPullbackIso` on each side and
`...RelativeProjQcohSheaf.chartPullbackRestrict_chartWitness` on the comparison. -/
theorem refineChartIso_trans_chartWitness (f : T ⟶ S) {ι : Type u} (W : ι → T.Opens)
    (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
      (quadrupleGlueData f W P hP).glued]
    (i j : ι) {V : T.Opens} (hV : V ≤ chartOverlap (fun a => (W a).ι) i j) :
    refineChartIso ((W i).ι) (chartOpenLift ((W i).ι) (hV.trans inf_le_left))
          (chartOpenLift_fac _ _) (quadrupleGlueData f W P hP).glued
          ((quadrupleGlueData f W P hP).gluedPullbackIso i) ≪≫
        Quadruple.chartWitness f W P hP i j
          (chartOpenLift ((W i).ι) (hV.trans inf_le_left))
          (chartOpenLift ((W j).ι) (hV.trans inf_le_right))
          (by rw [chartOpenLift_fac, chartOpenLift_fac]) =
      refineChartIso ((W j).ι) (chartOpenLift ((W j).ι) (hV.trans inf_le_right))
        (chartOpenLift_fac _ _) (quadrupleGlueData f W P hP).glued
        ((quadrupleGlueData f W P hP).gluedPullbackIso j) := by
  refine Iso.ext (ofPullbackChart_injective (p := V.ι)
    (p' := chartOpenLift ((W j).ι) (hV.trans inf_le_right)) ?_)
  have h1 := (quadrupleGlueData f W P hP).ofPullbackChart_refineChartIso_gluedPullbackIso i
    (chartOpenLift ((W i).ι) (hV.trans inf_le_left)) (chartOpenLift_fac _ _)
  have h2 := (quadrupleGlueData f W P hP).ofPullbackChart_refineChartIso_gluedPullbackIso j
    (chartOpenLift ((W j).ι) (hV.trans inf_le_right)) (chartOpenLift_fac _ _)
  have hb : ofPullbackChart (p := chartOpenLift ((W i).ι) (hV.trans inf_le_left))
        (p' := chartOpenLift ((W j).ι) (hV.trans inf_le_right))
        ((Quadruple.chartWitness f W P hP i j
        (chartOpenLift ((W i).ι) (hV.trans inf_le_left))
        (chartOpenLift ((W j).ι) (hV.trans inf_le_right))
        (by rw [chartOpenLift_fac, chartOpenLift_fac])).hom) =
      chartModuleRestrict (fun a => (W a).ι) (fun a => (P a).L) hV
        (ModulesGlueData.ofChartPullbackIsoFamily _ _ (chartGlueIso f W P hP) i j).hom :=
    (congrArg (ofPullbackChart (p := chartOpenLift ((W i).ι) (hV.trans inf_le_left))
          (p' := chartOpenLift ((W j).ι) (hV.trans inf_le_right)) (N := (P i).L) (M := (P j).L))
        (chartPullbackRestrict_chartWitness f W P hP hV i j inf_le_left inf_le_right).symm).trans
      ((chartModuleRestrict_ofPullbackChart (fun a => (W a).ι) (fun a => (P a).L) hV
            ((chartGlueIso f W P hP i j).hom)).symm.trans
        (congrArg (chartModuleRestrict (fun a => (W a).ι) (fun a => (P a).L) hV)
          (ModulesGlueData.ofChartPullbackIsoFamily_hom (fun a => (W a).ι) (fun a => (P a).L)
            (chartGlueIso f W P hP) i j).symm))
  have hglue : (Scheme.Modules.restrictFunctor V.ι).map
          ((quadrupleGlueData f W P hP).chartAdjunct i) ≫
        (restrictPushforwardIso ((W i).ι) (chartOpenLift ((W i).ι) (hV.trans inf_le_left))
          (chartOpenLift_fac _ _) ((P i).L)).hom ≫
        chartModuleRestrict (fun a => (W a).ι) (fun a => (P a).L) hV
          (ModulesGlueData.ofChartPullbackIsoFamily _ _ (chartGlueIso f W P hP) i j).hom ≫
        (restrictPushforwardIso ((W j).ι) (chartOpenLift ((W j).ι) (hV.trans inf_le_right))
          (chartOpenLift_fac _ _) ((P j).L)).inv =
      (Scheme.Modules.restrictFunctor V.ι).map
        ((quadrupleGlueData f W P hP).chartAdjunct j) :=
    Eq.trans (congrArg (fun z => (Scheme.Modules.restrictFunctor V.ι).map
        ((quadrupleGlueData f W P hP).chartAdjunct i) ≫ z)
      (restrictLocal_ofChartIsoHom (fun a => (W a).ι) (fun a => (P a).L) i j
        (ModulesGlueData.ofChartPullbackIsoFamily _ _ (chartGlueIso f W P hP) i j) hV).symm)
      (quadrupleGlueData_restrictFunctor_map_chartAdjunct f W P hP i j hV)
  refine (ofPullbackChart_comp (p := V.ι)
    (p' := chartOpenLift ((W i).ι) (hV.trans inf_le_left))
    (p'' := chartOpenLift ((W j).ι) (hV.trans inf_le_right)) _ _).trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ ofPullbackChart
    (p := chartOpenLift ((W i).ι) (hV.trans inf_le_left))
    (p' := chartOpenLift ((W j).ι) (hV.trans inf_le_right))
    ((Quadruple.chartWitness f W P hP i j
      (chartOpenLift ((W i).ι) (hV.trans inf_le_left))
      (chartOpenLift ((W j).ι) (hV.trans inf_le_right))
      (by rw [chartOpenLift_fac, chartOpenLift_fac])).hom)) h1) ?_
  refine Eq.trans (congrArg (fun z =>
    ((Scheme.Modules.restrictFunctor V.ι).map ((quadrupleGlueData f W P hP).chartAdjunct i) ≫
      (restrictPushforwardIso ((W i).ι) (chartOpenLift ((W i).ι) (hV.trans inf_le_left))
        (chartOpenLift_fac _ _) ((P i).L)).hom) ≫ z) hb) ?_
  exact (rightCancelInv _ _ _ _
    ((restrictPushforwardIso ((W j).ι) (chartOpenLift ((W j).ι) (hV.trans inf_le_right))
      (chartOpenLift_fac _ _) ((P j).L)).inv_hom_id)
    (((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans hglue)).trans h2.symm

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf


end
