module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.Basic

/-!
# Reducing the non-nested chart comparison to nested comparisons with a local model

A `Stacks.AlgebraicGeometry.ChartTransNonNested.RefinementData` consists of comparison
isomorphisms `loc k i j` between the `i`-th and the `j`-th chart module over a member `L k` of a
refinement lying below both chart opens; these are indexed by a pair of charts.

This file takes, over each member of the refinement, a **local model** — a single presheaf of
`𝒪_X`-modules — together with an isomorphism of each chart module with it, and a transition
between the models of a nested pair of refinement members compatible with those isomorphisms.
The pairwise comparison `i → j` is then the `i`-th identification followed by the inverse of the
`j`-th, so the cocycle condition over a single member holds by cancellation, and the only cocycle
condition among the inputs is `cmp_modelTrans`, for a nested chain.

Every input is a statement about one chart at a time over a nested pair of opens, which is the
shape of Tag 01NO: for the twists on a relative projective spectrum the model over an affine open
`W` of the base is the pushforward of the twists on `Proj Γ(W, A)`, the isomorphism with the
`i`-th chart module is the comparison of Tag 01NO for the nested pair `W ⊆ U i`, and the model
transition is the same comparison for a nested pair of refinement members.

## Main definitions

* `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData`: charts, a local model over each member
  of a refinement, the comparison of each chart module with the model, and the model transitions.
* `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.toRefinementData`: the pairwise
  comparisons, obtained by cancelling the model in the middle.
* `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.toChartGlueData`: the glueing datum.
* `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.glued`: the glued sheaf of modules.
* `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.chartIso`: the restriction of the glued
  sheaf of modules along a chart is isomorphic to the module carried by that chart.

## Main results

* `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.trans_app_of_le`: over an open contained
  in a member of the refinement, the non-nested comparison is the composite of that member's two
  comparisons with the model.
* `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.trans_trans`: the cocycle condition for
  the non-nested comparisons.

## Implementation notes

"Nested" refers to the refinement family, not to the base. For the relative projective spectrum
with `L = U = fun W : S.affineOpens => toBase ⁻¹ᵁ W.1`, the hypothesis `L k ≤ U i` of `cmp` reads
`toBase ⁻¹ᵁ W ≤ toBase ⁻¹ᵁ U`, which is weaker than `W ≤ U` since the structure morphism need
not be surjective.

The open-immersion hypothesis of `Stacks.AlgebraicGeometry.ChartTransNonNested.ModelData.chartIso`
is passed to `Stacks.AlgebraicGeometry.SchemeModuleGlue.chartIso` by name, since instance search
does not find an instance on `D.hom i` at `D.toChartGlueData.hom i`.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ChartTransNonNested

/-- **Chart data presented by local models over a refinement.**

Over each member `L k` of the refinement there is one presheaf of `𝒪_X`-modules `model k`, and
each chart module whose open contains `L k` is identified with it. The identifications for two
*nested* members of the refinement are related by a transition between the models which does not
depend on the chart. -/
public structure ModelData (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) where
  /-- The `i`-th chart. -/
  chart (i : ι) : Scheme.{u}
  /-- The morphism from the `i`-th chart to `X`. -/
  hom (i : ι) : chart i ⟶ X
  /-- The sheaf of modules carried by the `i`-th chart. -/
  sheaf (i : ι) : (chart i).Modules
  /-- The index type of the refinement. -/
  κ : Type u
  /-- The refinement: a family of opens of `X`. -/
  L : κ → X.Opens
  /-- Each chart open is covered by the members of the refinement contained in it. -/
  isRefinedBy_chartOpen (i : ι) : IsRefinedBy L (U i)
  /-- So is the meet of any two members of the refinement. -/
  isRefinedBy_inf (k k' : κ) : IsRefinedBy L (L k ⊓ L k')
  /-- The local model over a member of the refinement. -/
  model (k : κ) : PresheafOfModules.{u} X.ringCatSheaf.obj
  /-- The identification of the `i`-th chart module with the model over a member of the refinement
  lying below `U i`. For the twists on a relative Proj this is Tag 01NO's comparison for the
  nested pair of affine opens. -/
  cmp (k : κ) (i : ι) (hi : L k ≤ U i) :
    TopCat.Sheaf.LocalModuleEquiv (pushforwardVal (hom i) (sheaf i)) (model k) (L k)
  /-- The transition between the models of a nested pair of members of the refinement. -/
  modelTrans (k k' : κ) (hkk' : L k ≤ L k') :
    TopCat.Sheaf.LocalModuleEquiv (model k') (model k) (L k)
  /-- **The cocycle for a nested chain:** the identification of a chart module with the model over
  the smaller member is its identification with the model over the larger one followed by the
  model transition. -/
  cmp_modelTrans (k k' : κ) (hkk' : L k ≤ L k') (i : ι) (hi : L k' ≤ U i)
    (V : X.Opens) (hV : V ≤ L k) (s : (pushforwardVal (hom i) (sheaf i)).obj (op V)) :
    (modelTrans k k' hkk').app V hV ((cmp k' i hi).app V (hV.trans hkk') s)
      = (cmp k i (hkk'.trans hi)).app V hV s

namespace ModelData

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : ModelData X U)

/-- The comparison between two chart modules over a member of the refinement: identify the first
with the model, then the model with the second. -/
public noncomputable def loc (k : D.κ) (i j : ι) (hi : D.L k ≤ U i) (hj : D.L k ≤ U j) :
    TopCat.Sheaf.LocalModuleEquiv (pushforwardVal (D.hom i) (D.sheaf i))
      (pushforwardVal (D.hom j) (D.sheaf j)) (D.L k) :=
  (D.cmp k i hi).trans (D.cmp k j hj).symm

/-- On sections over `V ≤ L k`, the comparison `loc k i j` is the identification of the `i`-th
chart module with the model followed by the inverse of the identification for the `j`-th. -/
@[simp]
public theorem loc_app (k : D.κ) (i j : ι) (hi : D.L k ≤ U i) (hj : D.L k ≤ U j) (V : X.Opens)
    (hV : V ≤ D.L k) (s : (pushforwardVal (D.hom i) (D.sheaf i)).obj (op V)) :
    (D.loc k i j hi hj).app V hV s = ((D.cmp k j hj).app V hV).symm ((D.cmp k i hi).app V hV s) :=
  rfl

/-- **The cocycle condition over a single member of the refinement is free.** The `j`-th
identification with the model cancels against its own inverse. -/
public theorem loc_comp (k : D.κ) (i j l : ι) (hi : D.L k ≤ U i) (hj : D.L k ≤ U j)
    (hl : D.L k ≤ U l) (V : X.Opens) (hV : V ≤ D.L k)
    (s : (pushforwardVal (D.hom i) (D.sheaf i)).obj (op V)) :
    (D.loc k j l hj hl).app V hV ((D.loc k i j hi hj).app V hV s)
      = (D.loc k i l hi hl).app V hV s :=
  by simp

/-- **Shrinking a member of the refinement does not change the comparison.** Both identifications
with the model over the smaller member factor through the model transition, which is independent
of the chart, so it cancels. -/
public theorem loc_mono (k k' : D.κ) (i j : ι) (hkk' : D.L k ≤ D.L k') (hi : D.L k' ≤ U i)
    (hj : D.L k' ≤ U j) (V : X.Opens) (hV : V ≤ D.L k)
    (s : (pushforwardVal (D.hom i) (D.sheaf i)).obj (op V)) :
    (D.loc k i j (hkk'.trans hi) (hkk'.trans hj)).app V hV s
      = (D.loc k' i j hi hj).app V (hV.trans hkk') s := by
  simp only [loc_app]
  rw [LinearEquiv.symm_apply_eq, ← D.cmp_modelTrans k k' hkk' i hi V hV s,
    ← D.cmp_modelTrans k k' hkk' j hj V hV, LinearEquiv.apply_symm_apply]

/-- **The pairwise comparison data over the refinement** given by the comparisons `loc`. -/
public noncomputable def toRefinementData : RefinementData X U where
  chart := D.chart
  hom := D.hom
  sheaf := D.sheaf
  κ := D.κ
  L := D.L
  isRefinedBy_chartOpen := D.isRefinedBy_chartOpen
  isRefinedBy_inf := D.isRefinedBy_inf
  loc := D.loc
  loc_comp := D.loc_comp
  loc_mono := D.loc_mono

/-- **The non-nested chart comparison for a chart family presented by local models.** -/
public noncomputable def trans (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) :
    (pushforwardVal (D.hom i) (D.sheaf i)).obj (op V) ≃ₗ[X.ringCatSheaf.obj.obj (op V)]
      (pushforwardVal (D.hom j) (D.sheaf j)).obj (op V) :=
  D.toRefinementData.trans i j hi hj

/-- Over an open contained in a member of the refinement, the non-nested comparison is the
composite of that member's two identifications with the model. -/
public theorem trans_app_of_le (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j)
    (k : D.κ) (hk : D.L k ≤ U i ⊓ U j) (hV : V ≤ D.L k)
    (s : (pushforwardVal (D.hom i) (D.sheaf i)).obj (op V)) :
    D.trans i j hi hj s
      = ((D.cmp k j (hk.trans inf_le_right)).app V hV).symm
          ((D.cmp k i (hk.trans inf_le_left)).app V hV s) :=
  D.toRefinementData.trans_app_of_le i j hi hj k hk hV s

/-- The non-nested comparison commutes with the restriction maps. -/
public theorem trans_map (i j : ι) {V W : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
    (s : (pushforwardVal (D.hom i) (D.sheaf i)).obj (op V)) :
    D.trans i j (hWV.trans hi) (hWV.trans hj)
        ((pushforwardVal (D.hom i) (D.sheaf i)).resLE hWV s)
      = (pushforwardVal (D.hom j) (D.sheaf j)).resLE hWV (D.trans i j hi hj s) :=
  D.toRefinementData.trans_map i j hi hj hWV s

/-- The cocycle condition, for an arbitrary triple of charts over an arbitrary open. -/
public theorem trans_trans (i j l : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hl : V ≤ U l)
    (s : (pushforwardVal (D.hom i) (D.sheaf i)).obj (op V)) :
    D.trans j l hj hl (D.trans i j hi hj s) = D.trans i l hi hl s :=
  D.toRefinementData.trans_trans i j l hi hj hl s

/-- **The glueing datum for a chart family presented by local models over a refinement.** -/
public noncomputable def toChartGlueData : SchemeModuleGlue.ChartGlueData X U :=
  D.toRefinementData.toChartGlueData

/-- The chart comparison of the glueing datum is the non-nested comparison `trans`. -/
@[simp]
public theorem toChartGlueData_trans (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j)
    (s : (pushforwardVal (D.hom i) (D.sheaf i)).obj (op V)) :
    D.toChartGlueData.trans i j hi hj s = D.trans i j hi hj s := rfl

/-- **The glued sheaf of `𝒪_X`-modules.** -/
public noncomputable def glued : X.Modules :=
  D.toChartGlueData.glued

/-- **The chart identification.** The restriction of the glued sheaf of modules along the `i`-th
chart is isomorphic, as a sheaf of modules on that chart, to the module the chart carries. -/
public noncomputable def chartIso (i : ι) [hom_isOpenImmersion : IsOpenImmersion (D.hom i)]
    (hi : D.hom i ''ᵁ (⊤ : (D.chart i).Opens) ≤ U i) :
    Scheme.Modules.restrict D.glued (D.hom i) ≅ D.sheaf i :=
  SchemeModuleGlue.chartIso D.toChartGlueData i
    (hom_isOpenImmersion := hom_isOpenImmersion) hi

end ModelData

end Stacks.AlgebraicGeometry.ChartTransNonNested

end
