module

public import StacksFrontier.AlgebraicGeometry.SchemeModuleGlue.Basic

/-!
# Glueing sheaves of modules on a scheme along a family of open immersions

Given a family of charts over opens `U i` of a scheme `X`, a sheaf of modules on each chart and
comparison isomorphisms over the overlaps satisfying the cocycle condition, this file glues them
to a sheaf of `𝒪_X`-modules, and identifies the restriction of the glued object along a chart
that is an open immersion with the module that chart carried.

## Main definitions

* `Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData`: a family of charts over a family of
  opens of `X`, a sheaf of modules on each chart, and comparison isomorphisms on the overlaps.
* `Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData.glued`: the glued object, as an
  `AlgebraicGeometry.Scheme.Modules`.
* `Stacks.AlgebraicGeometry.SchemeModuleGlue.chartSectionEquiv`: the chart identification on
  sections over an open of the chart, as a linear equivalence over the chart's own ring of
  sections.
* `Stacks.AlgebraicGeometry.SchemeModuleGlue.chartIso`: **the chart identification.** The
  restriction of the glued object along a chart is isomorphic to the module that chart carried.

## Main results

* `Stacks.AlgebraicGeometry.SchemeModuleGlue.chartSectionEquiv_naturality`: the identification
  on sections commutes with the restriction maps.
* `Stacks.AlgebraicGeometry.SchemeModuleGlue.chartIso_hom_app` and `chartIso_inv_app`: the two
  directions of the chart identification on sections.

## Implementation notes

The open-immersion hypothesis on a chart is a named instance binder, `hom_isOpenImmersion`, so
that a caller whose instance is not found at the spelling `G.hom i` can pass it as
`(hom_isOpenImmersion := …)`.

`AlgebraicGeometry.Scheme.Modules` and `AlgebraicGeometry.Scheme.Modules.restrict` are `def`s and
`rw` fails on goals in which they occur, so the proofs about them are term-mode
`Eq.trans`/`congrArg`. The scalar rings are written `X.ringCatSheaf.obj.obj (op V)`, the spelling
at which the `Module` instances on sections are registered.

## References

* [Stacks Project, Tag 00AL](https://stacks.math.columbia.edu/tag/00AL)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace PresheafOfModules

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}

/-- Restricting a section along any `f : op A ⟶ op B` and then along any `g : op B ⟶ op A` is
the identity. -/
public theorem map_map_eq_self (N : PresheafOfModules.{u} 𝒪) {A B : Opens X}
    (f : op A ⟶ op B) (g : op B ⟶ op A) (x : N.obj (op A)) : N.map g (N.map f x) = x := by
  rw [← N.map_comp_apply, show f ≫ g = 𝟙 _ from Subsingleton.elim _ _]
  exact congr($(N.presheaf.map_id (op A)) x)

end PresheafOfModules

namespace Stacks.AlgebraicGeometry.SchemeModuleGlue

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}

/-! ### Glueing data presented by modules on charts -/

/-- **Glueing data for a sheaf of modules on a scheme, with the local pieces given as sheaves of
modules on charts.**

A chart is an arbitrary morphism `hom i : chart i ⟶ X` together with an open `U i` of `X` that it
is thought of as covering; the comparison isomorphism over an open `V` contained in both `U i` and
`U j` identifies the sections of the `i`-th module over `hom i ⁻¹ᵁ V` with those of the `j`-th over
`hom j ⁻¹ᵁ V`, `𝒪_X(V)`-linearly, those being the sections over `V` of the two pushforwards. -/
public structure ChartGlueData (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) where
  /-- The `i`-th chart. -/
  chart (i : ι) : Scheme.{u}
  /-- The morphism from the `i`-th chart to `X`. -/
  hom (i : ι) : chart i ⟶ X
  /-- The sheaf of modules carried by the `i`-th chart. -/
  sheaf (i : ι) : (chart i).Modules
  /-- The comparison isomorphism over an open `V` contained in both `U i` and `U j`, as an
  isomorphism of `𝒪_X(V)`-modules between the sections of the two pushforwards over `V`. -/
  trans : ∀ (i j : ι) {V : X.Opens} (_hi : V ≤ U i) (_hj : V ≤ U j),
    ((Scheme.Modules.pushforward (hom i)).obj (sheaf i)).val.obj (op V) ≃ₗ[
        X.ringCatSheaf.obj.obj (op V)]
      ((Scheme.Modules.pushforward (hom j)).obj (sheaf j)).val.obj (op V)
  /-- The comparison isomorphisms commute with the restriction maps. -/
  trans_map : ∀ (i j : ι) {V W : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
      (s : ((Scheme.Modules.pushforward (hom i)).obj (sheaf i)).val.obj (op V)),
    trans i j (hWV.trans hi) (hWV.trans hj)
        (((Scheme.Modules.pushforward (hom i)).obj (sheaf i)).val.resLE hWV s)
      = ((Scheme.Modules.pushforward (hom j)).obj (sheaf j)).val.resLE hWV
          (trans i j hi hj s)
  /-- The cocycle condition. -/
  trans_trans : ∀ (i j k : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k)
      (s : ((Scheme.Modules.pushforward (hom i)).obj (sheaf i)).val.obj (op V)),
    trans j k hj hk (trans i j hi hj s) = trans i k hi hk s

/-- Chart-presented glueing data, read as glueing data of sheaves of `𝒪_X`-modules on the
underlying space of `X`, with the same comparison data. -/
public def ChartGlueData.toOModuleGlueData (G : ChartGlueData X U) :
    TopCat.Sheaf.OModuleGlueData (X := X.toTopCat) X.ringCatSheaf.obj U where
  sheaf i := chartLocalPresheaf (G.hom i) (G.sheaf i) (U i)
  isSheaf i := isSheaf_chartLocalPresheaf (G.hom i) (G.sheaf i) (U i)
  trans := G.trans
  trans_map := G.trans_map
  trans_trans := G.trans_trans

/-- **The sheaf of `𝒪_X`-modules glued from modules on charts.** -/
public def ChartGlueData.glued (G : ChartGlueData X U) : X.Modules :=
  gluedModules G.toOModuleGlueData

/-! ### The chart identification -/

section ChartIso

/-- If a chart lands in its own open then so does the image of every open of the chart. -/
public theorem image_le (G : ChartGlueData X U) (i : ι)
    [hom_isOpenImmersion : IsOpenImmersion (G.hom i)]
    (hi : G.hom i ''ᵁ (⊤ : (G.chart i).Opens) ≤ U i) (W : (G.chart i).Opens) :
    G.hom i ''ᵁ W ≤ U i :=
  ((G.hom i).image_mono le_top).trans hi

/-- **The scalar comparison.** For an open immersion `f` and an open `W` of its source, the
composite of `(f.appIso W).inv` with `f.app (f ''ᵁ W)` is the restriction map along the equality
`f ⁻¹ᵁ (f ''ᵁ W) = W`, so restricting it back along that equality returns the scalar unchanged. -/
public theorem map_eqToHom_app_appIso_inv {Z : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f]
    (W : Z.Opens) (r : Z.presheaf.obj (op W)) :
    Z.presheaf.map (eqToHom (f.preimage_image_eq W).symm).op
        (f.app (f ''ᵁ W) ((f.appIso W).inv r)) = r := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    f.appIso_inv_app_presheafMap W]
  rfl

/-- **The chart identification on sections.** Over an open `W` of the `i`-th chart, the sections of
the restriction of the glued object along that chart are the sections of the module the chart
carried, as modules over the chart's own ring of sections over `W`: the comparison map of the
glueing at `hom i ''ᵁ W`, followed by the restriction map along
`hom i ⁻¹ᵁ (hom i ''ᵁ W) = W`. -/
public def chartSectionEquiv (G : ChartGlueData X U) (i : ι)
    [hom_isOpenImmersion : IsOpenImmersion (G.hom i)]
    (hi : G.hom i ''ᵁ (⊤ : (G.chart i).Opens) ≤ U i) (W : (G.chart i).Opens) :
    (Scheme.Modules.restrict G.glued (G.hom i)).val.obj (op W) ≃ₗ[
        (G.chart i).ringCatSheaf.obj.obj (op W)] (G.sheaf i).val.obj (op W) where
  toFun x := (G.sheaf i).val.restrictₛₗ (eqToHom ((G.hom i).preimage_image_eq W).symm).op
    (G.toOModuleGlueData.sectionsLinearEquiv i (image_le G i hi W) x)
  invFun y := (G.toOModuleGlueData.sectionsLinearEquiv i (image_le G i hi W)).symm
    ((G.sheaf i).val.restrictₛₗ (eqToHom ((G.hom i).preimage_image_eq W)).op y)
  map_add' x y :=
    Eq.trans
      (congrArg ((G.sheaf i).val.restrictₛₗ (eqToHom ((G.hom i).preimage_image_eq W).symm).op)
        (map_add (G.toOModuleGlueData.sectionsLinearEquiv i (image_le G i hi W)) x y))
      (map_add ((G.sheaf i).val.restrictₛₗ
        (eqToHom ((G.hom i).preimage_image_eq W).symm).op) _ _)
  map_smul' r x := by
    have h1 : ∀ (r' : X.ringCatSheaf.obj.obj (op (G.hom i ''ᵁ W)))
        (y : G.toOModuleGlueData.gluedPresheafOfModules.obj (op (G.hom i ''ᵁ W))),
        G.toOModuleGlueData.sectionsLinearEquiv i (image_le G i hi W) (r' • y)
          = r' • G.toOModuleGlueData.sectionsLinearEquiv i (image_le G i hi W) y :=
      fun r' y => map_smul _ r' y
    have h2 : ∀ (t : (G.chart i).ringCatSheaf.obj.obj (op (G.hom i ⁻¹ᵁ (G.hom i ''ᵁ W))))
        (z : (G.sheaf i).val.obj (op (G.hom i ⁻¹ᵁ (G.hom i ''ᵁ W)))),
        (G.sheaf i).val.restrictₛₗ (eqToHom ((G.hom i).preimage_image_eq W).symm).op (t • z)
          = (G.chart i).ringCatSheaf.obj.map
                (eqToHom ((G.hom i).preimage_image_eq W).symm).op t •
              (G.sheaf i).val.restrictₛₗ
                (eqToHom ((G.hom i).preimage_image_eq W).symm).op z :=
      fun t z => map_smulₛₗ _ t z
    refine Eq.trans (congrArg ((G.sheaf i).val.restrictₛₗ
        (eqToHom ((G.hom i).preimage_image_eq W).symm).op)
      (h1 (((G.hom i).appIso W).inv r : X.ringCatSheaf.obj.obj (op (G.hom i ''ᵁ W)))
        (x : G.toOModuleGlueData.gluedPresheafOfModules.obj (op (G.hom i ''ᵁ W))))) ?_
    refine Eq.trans (h2 ((G.hom i).app (G.hom i ''ᵁ W) (((G.hom i).appIso W).inv r) :
        (G.chart i).ringCatSheaf.obj.obj (op (G.hom i ⁻¹ᵁ (G.hom i ''ᵁ W))))
      (G.toOModuleGlueData.sectionsLinearEquiv i (image_le G i hi W) x)) ?_
    exact congrArg (fun t => t • (G.sheaf i).val.restrictₛₗ
        (eqToHom ((G.hom i).preimage_image_eq W).symm).op
        (G.toOModuleGlueData.sectionsLinearEquiv i (image_le G i hi W) x))
      (map_eqToHom_app_appIso_inv (G.hom i) W r)
  left_inv x :=
    Eq.trans
      (congrArg (G.toOModuleGlueData.sectionsLinearEquiv i (image_le G i hi W)).symm
        (PresheafOfModules.map_map_eq_self (G.sheaf i).val _ _
          (G.toOModuleGlueData.sectionsLinearEquiv i (image_le G i hi W) x)))
      (LinearEquiv.symm_apply_apply _ x)
  right_inv y :=
    Eq.trans
      (congrArg ((G.sheaf i).val.restrictₛₗ (eqToHom ((G.hom i).preimage_image_eq W).symm).op)
        (LinearEquiv.apply_symm_apply
          (G.toOModuleGlueData.sectionsLinearEquiv i (image_le G i hi W)) _))
      (PresheafOfModules.map_map_eq_self (G.sheaf i).val _ _ y)

/-- **The chart identification commutes with the restriction maps.** -/
public theorem chartSectionEquiv_naturality (G : ChartGlueData X U) (i : ι)
    [hom_isOpenImmersion : IsOpenImmersion (G.hom i)]
    (hi : G.hom i ''ᵁ (⊤ : (G.chart i).Opens) ≤ U i)
    {W₁ W₂ : (G.chart i).Opens} (g : (op W₁ : (Opens ↥(G.chart i))ᵒᵖ) ⟶ op W₂)
    (x : (Scheme.Modules.restrict G.glued (G.hom i)).val.obj (op W₁)) :
    chartSectionEquiv G i hi W₂ ((Scheme.Modules.restrict G.glued (G.hom i)).val.map g x)
      = (G.sheaf i).val.map g (chartSectionEquiv G i hi W₁ x) := by
  have hle : G.hom i ''ᵁ W₂ ≤ G.hom i ''ᵁ W₁ := (G.hom i).image_mono (leOfHom g.unop)
  have hres : ∀ (p : (op (G.hom i ⁻¹ᵁ (G.hom i ''ᵁ W₁)) : (Opens ↥(G.chart i))ᵒᵖ) ⟶
        op (G.hom i ⁻¹ᵁ (G.hom i ''ᵁ W₂)))
      (y : (G.sheaf i).val.obj (op (G.hom i ⁻¹ᵁ (G.hom i ''ᵁ W₁)))),
      (G.sheaf i).val.map (eqToHom ((G.hom i).preimage_image_eq W₂).symm).op
          ((G.sheaf i).val.map p y)
        = (G.sheaf i).val.map g ((G.sheaf i).val.map
            (eqToHom ((G.hom i).preimage_image_eq W₁).symm).op y) := by
    intro p y
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply,
      show p ≫ (eqToHom ((G.hom i).preimage_image_eq W₂).symm).op
        = (eqToHom ((G.hom i).preimage_image_eq W₁).symm).op ≫ g from Subsingleton.elim _ _]
  have hcomp := TopCat.Sheaf.GlueData.sectionsEquiv_map
    G.toOModuleGlueData.toAddGlueData.toGlueData i (image_le G i hi W₁) hle x
  exact Eq.trans
    (congrArg ((G.sheaf i).val.restrictₛₗ
      (eqToHom ((G.hom i).preimage_image_eq W₂).symm).op) hcomp) (hres _ _)

/-- **The chart identification.** The restriction of the glued object along a chart is isomorphic,
as a sheaf of modules on that chart, to the module the chart carried. -/
public def chartIso (G : ChartGlueData X U) (i : ι)
    [hom_isOpenImmersion : IsOpenImmersion (G.hom i)]
    (hi : G.hom i ''ᵁ (⊤ : (G.chart i).Opens) ≤ U i) :
    Scheme.Modules.restrict G.glued (G.hom i) ≅ G.sheaf i :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W => (chartSectionEquiv G i hi W.unop).toModuleIso)
      (fun {_W₁ _W₂} g => by
        ext x
        exact chartSectionEquiv_naturality G i hi g x))

/-- The chart identification acts on sections by
`Stacks.AlgebraicGeometry.SchemeModuleGlue.chartSectionEquiv`. -/
public theorem chartIso_hom_app (G : ChartGlueData X U) (i : ι)
    [hom_isOpenImmersion : IsOpenImmersion (G.hom i)]
    (hi : G.hom i ''ᵁ (⊤ : (G.chart i).Opens) ≤ U i) (W : (G.chart i).Opens)
    (x : (Scheme.Modules.restrict G.glued (G.hom i)).val.obj (op W)) :
    (chartIso G i hi).hom.val.app (op W) x = chartSectionEquiv G i hi W x :=
  rfl

/-- Its inverse acts on sections by the inverse of
`Stacks.AlgebraicGeometry.SchemeModuleGlue.chartSectionEquiv`. -/
public theorem chartIso_inv_app (G : ChartGlueData X U) (i : ι)
    [hom_isOpenImmersion : IsOpenImmersion (G.hom i)]
    (hi : G.hom i ''ᵁ (⊤ : (G.chart i).Opens) ≤ U i) (W : (G.chart i).Opens)
    (y : (G.sheaf i).val.obj (op W)) :
    (chartIso G i hi).inv.val.app (op W) y = (chartSectionEquiv G i hi W).symm y :=
  rfl

end ChartIso

end Stacks.AlgebraicGeometry.SchemeModuleGlue

end
