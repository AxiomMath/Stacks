module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitSections

/-!
# The value over a chart of the inverse image of a global section

`AlgebraicGeometry.Space.modulePullbackSections` is the inverse image of a global section of an
`𝒪_Y`-module `M` along a morphism `g : X ⟶ Y` of algebraic spaces: a global section is a
morphism `𝒪_Y ⟶ M`, and its inverse image is `𝒪_X ≅ g^*𝒪_Y ⟶ g^*M` read back as a global
section of `g^*M`.  It had no description of its values: the first of the two morphisms is
`AlgebraicGeometry.Space.modulePullbackUnitIso`, which is built by corepresentability.

This file computes those values.  Over a commutative diagram `d` of étale scheme charts — a
chart `d.U` of `X` above a chart `d.V` of `Y` — the value of the inverse image of `σ` at `d.U`
is a canonical function of the value of `σ` at `d.V`, namely the chart projection of the unit
of the Stacks 03D7 adjunction:

`(g^*σ)(d.U) = chartSection d (σ(d.V))`.

So the inverse image of a global section is computed chartwise, which is what a consumer that
evaluates global sections at a chart needs.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackChartSection`: the canonical section of `g^*M` over the
  chart `d.U` attached to a section of `M` over the chart `d.V` — the unit of the Stacks 03D7
  adjunction for the morphism of small étale ringed topoi, followed by the chart projection of
  the direct image of Stacks 03LU.
* `AlgebraicGeometry.Space.chartPullbackSectionMap`: that section followed by a morphism out of
  the inverse image.

## Main results

* `AlgebraicGeometry.Space.modulePullbackChartSection_map`: the chart section is natural in the
  module.
* `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_val_app_one`: **the identification
  `𝒪_X ≅ g^*𝒪_Y` of Stacks 03LU carries the unit function to the chart section of the unit
  function.**  This is the one value of that identification which corepresentability yields.
* `AlgebraicGeometry.Space.modulePullbackSections_val`: **the inverse image of a global section,
  evaluated over a chart.**
* `AlgebraicGeometry.Space.sectionsMap_modulePullbackSections_val`: the same with a morphism out
  of the inverse image composed on, which is the shape the maps of Stacks 07SI between the
  groups of global sections have.

## Implementation notes

The chart section is built from the unit of
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` — the Stacks 03D7 adjunction
for the morphism of ringed topoi — and not from
`AlgebraicGeometry.Space.modulePullbackAdjunction`, which is that adjunction transported along
`AlgebraicGeometry.Space.modulePushforwardIso`.  The two differ by a comparison which is the
identity on underlying sheaves of sets, so the chart sections agree; the untransported form is
used because it is the form the corepresentability computation of
`StacksFrontier/AlgebraicGeometry/Spaces/StructureSheafPullbackUnitSections.lean` produces, and
inserting the comparison here would re-introduce a transport with no value lemma.
`AlgebraicGeometry.Space.modulePullbackUnitSection` is the same section built from the
transported adjunction; it is not used here for that reason.

Both naturality steps are the naturality of the chart projection
`AlgebraicGeometry.Space.moduleChartProjection`, which is a natural transformation of functors
of sheaves of *sets*; the second is applied to a morphism out of the terminal sheaf, which no
module-level naturality lemma would cover. The underlying sheaf of sets of the direct image of
the modules development and of the ringed-topos one agree definitionally, which is what lets
one chart projection serve both.

The identification `𝒪_X ≅ g^*𝒪_Y` is proved on the unit function by applying the inverse
isomorphism, which is injective on sections, rather than by computing both sides: only the
composite with that inverse has a description.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- Evaluating a composite of morphisms of modules on a section is evaluating the two factors in
turn.  Stated for arbitrary factors so that nothing has to be unfolded. -/
public theorem comp_val_app_apply {Z : AlgebraicSpaces B S hS}
    {M₁ M₂ M₃ : Modules.{u, u} B S hS Z.1 Z.2} (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃)
    (W : (SmallEtale B S hS Z.1)ᵒᵖ) (w : M₁.val.obj W) :
    (a ≫ b).val.app W w = b.val.app W (a.val.app W w) :=
  rfl

/-- A component of an isomorphism of modules is injective on sections. -/
private theorem iso_val_app_injective {Z : AlgebraicSpaces B S hS}
    {M₁ M₂ : Modules.{u, u} B S hS Z.1 Z.2} (e : M₁ ≅ M₂)
    (W : (SmallEtale B S hS Z.1)ᵒᵖ) {x y : M₁.val.obj W}
    (h : e.hom.val.app W x = e.hom.val.app W y) : x = y := by
  have hx : ∀ z : M₁.val.obj W, e.inv.val.app W (e.hom.val.app W z) = z := fun z ↦
    (comp_val_app_apply B S hS e.hom e.inv W z).symm.trans
      (congrArg (fun m : M₁ ⟶ M₁ ↦ m.val.app W z) e.hom_inv_id)
  exact ((hx x).symm.trans (congrArg (fun z ↦ e.inv.val.app W z) h)).trans (hx y)

/-! ### The chart section of an inverse image -/

/-- The chart projection commutes with a morphism of modules on `X`, pushed forward to `Y`. -/
private theorem chartProjection_pushforward_map_apply {A₁ A₂ : Modules.{u, u} B S hS X.1 X.2}
    (ψ : A₁ ⟶ A₂) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (t : ((pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).obj A₁).val.obj
      (op d.V)) :
    (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
        (moduleSetSheaf B S hS X A₂)
      (((pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).map ψ).val.app
        (op d.V) t)
      = ψ.val.app (op d.U)
        ((moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
          (moduleSetSheaf B S hS X A₁) t) :=
  (Functor.natTrans_app_map_apply
    (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d))
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map ψ) t)

/-- **The canonical section of `g^*M` over the chart of `X` of a commutative diagram `d` of
étale scheme charts attached to a section `s` of `M` over the chart of `Y`**: the unit of the
Stacks 03D7 adjunction evaluated at `s`, followed by the chart projection
`AlgebraicGeometry.Space.moduleChartProjection` of the direct image of Stacks 03LU. -/
noncomputable def modulePullbackChartSection (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : M.val.obj (op d.V)) : ((modulePullback B S hS f).obj M).val.obj (op d.U) :=
  (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
      (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M))
    (((pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS f)).unit.app M).val.app (op d.V) s)

variable {M' : Modules.{u, u} B S hS Y.1 Y.2}

/-- **The chart section is natural in the module.**  This is the naturality of the unit of the
Stacks 03D7 adjunction followed by the naturality of the chart projection. -/
theorem modulePullbackChartSection_map (a : M ⟶ M')
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : M.val.obj (op d.V)) :
    ((modulePullback B S hS f).map a).val.app (op d.U)
        (modulePullbackChartSection B S hS f M d s)
      = modulePullbackChartSection B S hS f M' d (a.val.app (op d.V) s) := by
  have hnat : a ≫ (pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS f)).unit.app M'
      = (pullbackAdjPushforwardModules
            (smallEtaleRingedToposModulesHom B S hS f)).unit.app M ≫
        (pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).map
          ((modulePullback B S hS f).map a) :=
    (pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).unit.naturality a
  have hx := congrArg
    (fun m : M ⟶ (pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).obj
        ((modulePullback B S hS f).obj M') ↦ m.val.app (op d.V) s) hnat
  refine (chartProjection_pushforward_map_apply B S hS f _ d _).symm.trans ?_
  exact congrArg
    ((moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
      (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M'))) hx.symm

/-! ### The inverse image of the structure sheaf, on the unit function -/

/-- The chart section of the unit function is carried by the identification
`𝒪_X ≅ g^*𝒪_Y` of Stacks 03LU to the unit function.

This is `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_inv_adjunct_val_app_one` —
the transpose of that identification, on the unit section — read through the chart projection,
twice: once to move the identification out of the chart projection, and once to evaluate the
chart projection on a direct image of a morphism out of the terminal sheaf. -/
theorem modulePullbackUnitIso_hom_val_app_modulePullbackChartSection
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (modulePullbackUnitIso B S hS f).hom.val.app (op d.U)
        (modulePullbackChartSection B S hS f
          (SheafOfModules.unit (structureRingSheaf B S hS Y)) d
          (1 : (structureRingSheaf B S hS Y).obj.obj (op d.V)))
      = (1 : (structureRingSheaf B S hS X).obj.obj (op d.U)) := by
  have hA' :
      ((pullbackAdjPushforwardModules
              (smallEtaleRingedToposModulesHom B S hS f)).unit.app
            (SheafOfModules.unit (structureRingSheaf B S hS Y)) ≫
          (pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).map
            (modulePullbackUnitIso B S hS f).hom).val.app (op d.V)
          (1 : (structureRingSheaf B S hS Y).obj.obj (op d.V))
        = ((smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforward.map
              (unitTerminalHomEquiv (structureRingSheaf B S hS X)
                (SheafOfModules.unit (structureRingSheaf B S hS X)) (𝟙 _))).hom.app (op d.V)
            ((MorphismOfTopoi.pushforwardTerminalSection
                (smallEtaleRingedToposModulesHom B S hS f).toToposHom).hom.app (op d.V)
              (terminalSheafSection (SmallEtale.topology B S hS Y.1) (op d.V))) :=
    (congrArg
      (fun mm : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶
          (pushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).obj
            (SheafOfModules.unit (structureRingSheaf B S hS X)) ↦
        mm.val.app (op d.V) (1 : (structureRingSheaf B S hS Y).obj.obj (op d.V)))
      (Adjunction.homEquiv_unit
        (pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS f))
        (SheafOfModules.unit (structureRingSheaf B S hS Y))
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (modulePullbackUnitIso B S hS f).hom)).symm.trans
      (pullbackModulesObjUnitIso_inv_adjunct_val_app_one
        (smallEtaleRingedToposModulesHom B S hS f) (op d.V))
  refine (chartProjection_pushforward_map_apply B S hS f _ d _).symm.trans ?_
  refine Eq.trans (congrArg
    ((moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
      (moduleSetSheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)))) hA') ?_
  exact (Functor.natTrans_app_map_apply
      (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d))
      (unitTerminalHomEquiv (structureRingSheaf B S hS X)
        (SheafOfModules.unit (structureRingSheaf B S hS X)) (𝟙 _)) _).trans
    (unitTerminalHomEquiv_id_app_apply (structureRingSheaf B S hS X) _ _)

/-- **The identification `𝒪_X ≅ g^*𝒪_Y` of Stacks 03LU carries the unit function to the chart
section of the unit function.**

This is the identity that a computation with the inverse image of a global section needs, and
the only value of that identification available: it is built by corepresentability
(`AlgebraicGeometry.Space.modulePullbackUnitIso_inv_comp`), so only its composites are
described, and the composite with the inverse isomorphism is the one whose value on the unit
function can be read off. That inverse is injective on sections, which is what turns the
statement about the composite into this one. -/
theorem modulePullbackUnitIso_inv_val_app_one (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (modulePullbackUnitIso B S hS f).inv.val.app (op d.U)
        (1 : (structureRingSheaf B S hS X).obj.obj (op d.U))
      = modulePullbackChartSection B S hS f
          (SheafOfModules.unit (structureRingSheaf B S hS Y)) d
          (1 : (structureRingSheaf B S hS Y).obj.obj (op d.V)) := by
  refine iso_val_app_injective B S hS (modulePullbackUnitIso B S hS f) (op d.U)
    (Eq.trans ?_ (modulePullbackUnitIso_hom_val_app_modulePullbackChartSection
      B S hS f d).symm)
  exact (comp_val_app_apply B S hS (modulePullbackUnitIso B S hS f).inv
      (modulePullbackUnitIso B S hS f).hom (op d.U) _).symm.trans
    (congrArg
      (fun m : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
          SheafOfModules.unit (structureRingSheaf B S hS X) ↦
        m.val.app (op d.U) (1 : (structureRingSheaf B S hS X).obj.obj (op d.U)))
      (modulePullbackUnitIso B S hS f).inv_hom_id)

/-! ### The inverse image of a global section, over a chart -/

/-- **The inverse image of a global section of a module, evaluated over a chart.**  Over a
commutative diagram `d` of étale scheme charts, the value at the chart of `X` of the inverse
image of a global section `σ` of `M` is the chart section of the value of `σ` at the chart of
`Y`.

So `AlgebraicGeometry.Space.modulePullbackSections` is computed chartwise: it is the identity
`𝒪_X ≅ g^*𝒪_Y` on the unit function, which is
`AlgebraicGeometry.Space.modulePullbackUnitIso_inv_val_app_one`, followed by the naturality of
the chart section in the module. -/
theorem modulePullbackSections_val (σ : M.sections)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (modulePullbackSections B S hS f M σ).val (op d.U)
      = modulePullbackChartSection B S hS f M d (σ.val (op d.V)) := by
  refine Eq.trans (comp_val_app_apply B S hS (modulePullbackUnitIso B S hS f).inv
    ((modulePullback B S hS f).map ((SheafOfModules.unitHomEquiv M).symm σ)) (op d.U)
    (1 : (structureRingSheaf B S hS X).obj.obj (op d.U))) ?_
  refine Eq.trans (congrArg
    (fun z ↦ ((modulePullback B S hS f).map
        ((SheafOfModules.unitHomEquiv M).symm σ)).val.app (op d.U) z)
    (modulePullbackUnitIso_inv_val_app_one B S hS f d)) ?_
  refine (modulePullbackChartSection_map B S hS f
    (SheafOfModules.unit (structureRingSheaf B S hS Y))
    ((SheafOfModules.unitHomEquiv M).symm σ) d _).trans ?_
  exact congrArg (modulePullbackChartSection B S hS f M d)
    (unitHomEquiv_symm_val_app_one M σ (op d.V))

/-! ### A morphism out of an inverse image, on an inverse image of a global section -/

variable (N : Modules.{u, u} B S hS X.1 X.2)

/-- **The chart value of a morphism out of an inverse image of modules, on an inverse image of a
global section**: the chart section of the value of the global section over the chart of `Y`,
followed by the morphism.

This is the shape in which the maps `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` of Stacks 07SI are built — an
inverse image of a global section followed by a comparison of iterated inverse images — so it is
the shape in which their chart values are computed. -/
noncomputable def chartPullbackSectionMap (ψ : (modulePullback B S hS f).obj M ⟶ N)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (y : M.val.obj (op d.V)) : N.val.obj (op d.U) :=
  ψ.val.app (op d.U) (modulePullbackChartSection B S hS f M d y)

/-- **The inverse image of a global section, pushed through a morphism out of the inverse image
and evaluated over a chart.**  This is
`AlgebraicGeometry.Space.modulePullbackSections_val` with a morphism out of the inverse image
composed on, which is how the maps of Stacks 07SI between the groups of global sections are
built. -/
theorem sectionsMap_modulePullbackSections_val (ψ : (modulePullback B S hS f).obj M ⟶ N)
    (σ : M.sections) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (SheafOfModules.sectionsMap ψ (modulePullbackSections B S hS f M σ)).val (op d.U)
      = chartPullbackSectionMap B S hS f M N ψ d (σ.val (op d.V)) :=
  (PresheafOfModules.sectionsMap_coe ψ.val
      (modulePullbackSections B S hS f M σ) (op d.U)).trans
    (congrArg (fun z ↦ ψ.val.app (op d.U) z)
      (modulePullbackSections_val B S hS f M σ d))

end AlgebraicGeometry.Space

end
