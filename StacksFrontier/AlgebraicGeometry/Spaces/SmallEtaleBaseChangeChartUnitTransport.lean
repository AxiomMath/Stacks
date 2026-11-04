module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnit
public import StacksFrontier.CategoryTheory.Adjunction.UnitSectionProjection

/-!
# The chart projection of the unit of étale restriction, and the comparison of direct images

Let `f : X ⟶ Y` be an étale *representable* morphism of algebraic spaces over a scheme `S` in a
big fppf site `B`.  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeChartUnit.lean`
reduces **(†)** — the statement that the adjoint-canonical comparison
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso` of the two direct images of modules
agrees with the hand-built `AlgebraicGeometry.Space.modulePushforwardChartIso` — to a single
equation of units, and proves every ingredient of that equation.  This file carries out the
assembly and proves (†).

## Main results

* `AlgebraicGeometry.Space.chartSetProj_etaleModulePullbackAdjunction_unit`: **the chart
  projection of the unit of Stacks 03LU is restriction of sections along the cartesian
  projection.**  This is the sectionwise identity that
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeChartUnit.lean` lists as the one
  missing input.
* `AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction_unit_comp_chartIso_inv`:
  the resulting equation of units, in the shape
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso_eq_chartIso_symm_of_unit` asks
  for.
* `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso_eq_chartIso_symm`: **(†)**.

## Implementation notes

**Where the sections are read.**  Every step is taken with the *set-level* chart projection
`AlgebraicGeometry.Space.chartSetProj`, applied to the sheaf of sets underlying the module in
question, and never with the module-level `AlgebraicGeometry.Space.chartModProj`.  That is
forced.  The module-level projection has the sections of
`AlgebraicGeometry.Space.modulePushforward` as its domain, so feeding it a section of the
*other* spelling of the direct image — the one
`Stacks.Sheaves.RingedToposModules.pushforwardModules` of the morphism of ringed topoi, which is
where the unit of Stacks 03D7 lives — makes the elaborator compare two presheaves *of modules*
whose sections at the pullback of a module are a sheafified tensor product, and the heartbeat
budget is gone at `whnf`.  The set-level projection has a sheaf of sets as its domain, and both
module spellings reduce to one and the same sheaf of sets; each of the two conversions is then
affordable.  With `chartModProj` the transport below does not elaborate, with
`chartSetProj` it does.

**The imported sectionwise identity is used directly, not restated.**
`AlgebraicGeometry.Space.modulePullbackAdjunction_unit_val_app` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSpellingBridge.lean` is applied as it stands
at the one place that uses it, `.chartSetProj_modulePullbackAdjunction_unit`.  The two spellings of
the sheaf of rings over which the sections are taken (`AlgebraicGeometry.Space.Modules`' own, and
`Stacks.Sheaves.RingedToposModules.structureRingSheaf` of the small étale ringed topos) are
reconciled at elaboration, but the imported statement matches on the nose here, so a local
restatement would only be a second declaration of one statement.  The set-level projection above
is a different matter: without it the transport does not elaborate.

**One declaration per step.**  As in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeChartUnit.lean`, the heartbeat budget
is per declaration and several of these steps cost a large fraction of one, so each is its own
declaration and the chain is assembled from them.

No `@[stacks]` attribute is carried by the sectionwise steps: they are readings on sections of
comparisons that already carry their tags.  (†) itself is an identification of two comparisons,
not an assertion of a numbered result.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace Stacks.ChartUnitTransport

universe w v uu

variable {CC : Type uu} [Category.{v} CC] {J : GrothendieckTopology CC}
    {R : Sheaf J RingCat.{w}}

/-- **A morphism of sheaves of modules is determined by its values on sections**, with the
object of the site unopped.  Quantifying over the object rather than over an object of the
opposite category means a consumer supplying a statement at `Opposite.op V` does not pay for the
conversion at the chart; the conversion happens here, at a variable. -/
theorem hom_ext_val_app_apply_unop {M N : SheafOfModules.{w} R} {a b : M ⟶ N}
    (h : ∀ (W : CC) (x : M.val.obj (op W)), a.val.app (op W) x = b.val.app (op W) x) : a = b :=
  SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun Z ↦ ModuleCat.hom_ext (LinearMap.ext (h Z.unop)))

end Stacks.ChartUnitTransport

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom)

/-! ### The imported sectionwise identity of the direct images, restated -/

/-- **The hand-built comparison of the two direct images of modules is the chart projection on
sections**, restated with the projection written as
`AlgebraicGeometry.Space.chartSetProj`.  This is
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_val_app`. -/
theorem modulePushforwardChartIso_hom_app_chartSetProj
    (N : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1)
    (n : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    ((modulePushforwardChartIso B S hS f hrep).hom.app N).val.app (op V) n =
      chartSetProj B S hS f hrep (moduleSetSheaf B S hS X N) V n :=
  modulePushforwardChartIso_hom_app_val_app B S hS f hrep N V n

/-! ### The transport of the unit under the chart projection -/

/-- **The transport.**  The chart projection of the unit of Stacks 03D7 does not see which of
the two spellings of the direct image of modules the unit is taken in: the comparison of the two
is the identity on underlying sheaves of sets, and the chart projection factors through them.

This is the step the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeChartUnit.lean` record as the one that
does not elaborate.  It is `Stacks.CategoryTheory.proj_congr` — an arbitrary projection applied
to an equality of sections, with the equality first — at the chart projection; the set-level
projection is what makes it elaborate, see the implementation notes. -/
theorem chartSetProj_modulePullbackAdjunction_unit (M : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS Y.1) (x : M.val.obj (op V)) :
    chartSetProj B S hS f hrep
        (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M)) V
        (((modulePullbackAdjunction B S hS f).unit.app M).val.app (op V) x) =
      chartSetProj B S hS f hrep
        (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M)) V
        (((pullbackAdjPushforwardModules
          (smallEtaleRingedToposModulesHom B S hS f)).unit.app M).val.app (op V) x) := by
  have h := Stacks.CategoryTheory.proj_congr
    (modulePullbackAdjunction_unit_val_app B S hS f M (op V) x)
    (chartSetProj B S hS f hrep
      (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M)) V)
  exact h

/-- The unit of Stacks 03D7 is the topos-level unit followed by the extension-of-scalars unit,
on sections: the composite adjunction's unit, read at a chart. -/
theorem chartSetProj_pullbackAdjPushforwardModules_unit
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (x : M.val.obj (op V)) :
    chartSetProj B S hS f hrep
        (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M)) V
        (((pullbackAdjPushforwardModules
          (smallEtaleRingedToposModulesHom B S hS f)).unit.app M).val.app (op V) x) =
      chartSetProj B S hS f hrep
        (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M)) V
        (((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y)).map
            ((extendScalarsFSharpAdjunction B S hS f).unit.app
              ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
                (structureRingSheaf B S hS Y)).obj M))).val.app (op V)
          (((inverseImageAdjDirectImageModules
              (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y)).unit.app M).val.app (op V) x)) := rfl

/-- The extension-of-scalars unit moves out of the chart projection. -/
theorem chartSetProj_extendScalarsFSharpAdjunction_unit
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (x : M.val.obj (op V)) :
    chartSetProj B S hS f hrep
        (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M)) V
        (((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y)).map
            ((extendScalarsFSharpAdjunction B S hS f).unit.app
              ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
                (structureRingSheaf B S hS Y)).obj M))).val.app (op V)
          (((inverseImageAdjDirectImageModules
              (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y)).unit.app M).val.app (op V) x)) =
      ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y)).obj M)).val.app
          (op ((smallBaseChange B S hS f hrep).obj V))
        (chartSetProj B S hS f hrep
          ((smallToposMorphismTypeU B S hS f).inverseImage.obj
            (moduleSetSheaf B S hS Y M)) V
          (((inverseImageAdjDirectImageModules
              (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y)).unit.app M).val.app (op V) x)) :=
  chartSetProj_directImageModules_map B S hS f hrep
    ((extendScalarsFSharpAdjunction B S hS f).unit.app
      ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)).obj M)) V
    (((inverseImageAdjDirectImageModules
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)).unit.app M).val.app (op V) x)

/-- The topos-level unit of modules is, on sections, the topos-level unit of sheaves of sets. -/
theorem chartSetProj_inverseImageAdjDirectImageModules_unit
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (x : M.val.obj (op V)) :
    chartSetProj B S hS f hrep
        ((smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y M)) V
        (((inverseImageAdjDirectImageModules
            (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)).unit.app M).val.app (op V) x) =
      chartSetProj B S hS f hrep
        ((smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y M)) V
        (((smallToposMorphismTypeU B S hS f).adj.unit.app
          (moduleSetSheaf B S hS Y M)).hom.app (op V) x) :=
  congrArg (chartSetProj B S hS f hrep
      ((smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y M)) V)
    (Sheaf.hom_congr_app_apply
      (moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y) M) (op V) x)

/-- **The chart projection of the unit of Stacks 03D7 is the extension-of-scalars unit applied to
the chart projection of the topos-level unit of sheaves of sets.** -/
theorem chartSetProj_modulePullbackAdjunction_unit_eq (M : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS Y.1) (x : M.val.obj (op V)) :
    chartSetProj B S hS f hrep
        (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M)) V
        (((modulePullbackAdjunction B S hS f).unit.app M).val.app (op V) x) =
      ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y)).obj M)).val.app
          (op ((smallBaseChange B S hS f hrep).obj V))
        (chartSetProj B S hS f hrep
          ((smallToposMorphismTypeU B S hS f).inverseImage.obj
            (moduleSetSheaf B S hS Y M)) V
          (((smallToposMorphismTypeU B S hS f).adj.unit.app
            (moduleSetSheaf B S hS Y M)).hom.app (op V) x)) :=
  ((chartSetProj_modulePullbackAdjunction_unit B S hS f hrep M V x).trans
      ((chartSetProj_pullbackAdjPushforwardModules_unit B S hS f hrep M V x).trans
        (chartSetProj_extendScalarsFSharpAdjunction_unit B S hS f hrep M V x))).trans
    (Stacks.CategoryTheory.proj_congr
      (chartSetProj_inverseImageAdjDirectImageModules_unit B S hS f hrep M V x)
      (fun m ↦ ((extendScalarsFSharpAdjunction B S hS f).unit.app
          ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)).obj M)).val.app
        (op ((smallBaseChange B S hS f hrep).obj V)) m))

/-! ### The set-level end of the chain -/

/-- **The comparison of Stacks 03LQ applied to the chart projection of the topos-level unit is
restriction of sections along the cartesian projection.**  The comparison moves back inside the
chart projection by naturality, where it turns the topos-level unit into the unit of étale
restriction of sheaves of sets, whose chart projection is that restriction. -/
theorem inverseImageIso_chartSetProj_adj_unit (M : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS Y.1) (x : M.val.obj (op V)) :
    ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
          (moduleSetSheaf B S hS Y M)).hom.app
        (op ((smallBaseChange B S hS f hrep).obj V))
        (chartSetProj B S hS f hrep
          ((smallToposMorphismTypeU B S hS f).inverseImage.obj
            (moduleSetSheaf B S hS Y M)) V
          (((smallToposMorphismTypeU B S hS f).adj.unit.app
            (moduleSetSheaf B S hS Y M)).hom.app (op V) x)) =
      M.val.map ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).counit.app V).op x :=
  ((chartSetProj_smallEtaleDirectImage_map_inverseImageIso B S hS f hf hrep
        (moduleSetSheaf B S hS Y M) V
        (((smallToposMorphismTypeU B S hS f).adj.unit.app
          (moduleSetSheaf B S hS Y M)).hom.app (op V) x)).symm.trans
      (Stacks.CategoryTheory.proj_congr
        (smallEtaleDirectImage_map_inverseImageIso_adj_unit B S hS f hf
          (moduleSetSheaf B S hS Y M) V x)
        (chartSetProj B S hS f hrep
          ((smallEtaleSetRestriction B S hS f hf).obj (moduleSetSheaf B S hS Y M)) V))).trans
    (chartSetProj_setRestrictionAdjunction_unit B S hS f hf hrep
      (moduleSetSheaf B S hS Y M) V x)

/-! ### The chart projection of the unit of Stacks 03LU -/

/-- The unit of Stacks 03LU is the unit of Stacks 03D7 followed by the direct image of the
identification of Stacks 03LW: this is how
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is defined, read on a section. -/
theorem etaleModulePullbackAdjunction_unit_val_app (M : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS Y.1) (x : M.val.obj (op V)) :
    ((etaleModulePullbackAdjunction B S hS f hf).unit.app M).val.app (op V) x =
      ((modulePushforward B S hS f).map
        ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M)).val.app (op V)
        (((modulePullbackAdjunction B S hS f).unit.app M).val.app (op V) x) := rfl

/-- The identification of Stacks 03LW moves out of the chart projection. -/
theorem chartSetProj_etaleModulePullbackAdjunction_unit_eq
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (x : M.val.obj (op V)) :
    chartSetProj B S hS f hrep
        (moduleSetSheaf B S hS X ((etaleModulePullback.{u, u} B S hS f hf).obj M)) V
        (((etaleModulePullbackAdjunction B S hS f hf).unit.app M).val.app (op V) x) =
      ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M).val.app
          (op ((smallBaseChange B S hS f hrep).obj V))
        (chartSetProj B S hS f hrep
          (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M)) V
          (((modulePullbackAdjunction B S hS f).unit.app M).val.app (op V) x)) :=
  (Stacks.CategoryTheory.proj_congr
      (etaleModulePullbackAdjunction_unit_val_app B S hS f hf M V x)
      (chartSetProj B S hS f hrep
        (moduleSetSheaf B S hS X ((etaleModulePullback.{u, u} B S hS f hf).obj M)) V)).trans
    (chartSetProj_modulePushforward_map B S hS f hrep
      ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M) V
      (((modulePullbackAdjunction B S hS f).unit.app M).val.app (op V) x))

/-- The identification of Stacks 03LW applied to the chart projection of the unit of
Stacks 03D7, which the previous step computes. -/
theorem modulePullbackIso_chartSetProj_modulePullbackAdjunction_unit
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (x : M.val.obj (op V)) :
    ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M).val.app
          (op ((smallBaseChange B S hS f hrep).obj V))
        (chartSetProj B S hS f hrep
          (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj M)) V
          (((modulePullbackAdjunction B S hS f).unit.app M).val.app (op V) x)) =
      ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M).val.app
          (op ((smallBaseChange B S hS f hrep).obj V))
        (((extendScalarsFSharpAdjunction B S hS f).unit.app
              ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
                (structureRingSheaf B S hS Y)).obj M)).val.app
            (op ((smallBaseChange B S hS f hrep).obj V))
          (chartSetProj B S hS f hrep
            ((smallToposMorphismTypeU B S hS f).inverseImage.obj
              (moduleSetSheaf B S hS Y M)) V
            (((smallToposMorphismTypeU B S hS f).adj.unit.app
              (moduleSetSheaf B S hS Y M)).hom.app (op V) x))) :=
  Stacks.CategoryTheory.proj_congr
    (chartSetProj_modulePullbackAdjunction_unit_eq B S hS f hrep M V x)
    (fun m ↦ ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M).val.app
      (op ((smallBaseChange B S hS f hrep).obj V)) m)

/-- **The chart projection of the unit of Stacks 03LU is restriction of sections along the
cartesian projection `V ×_Y X ⟶ V`.**  This is the sectionwise identity that
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeChartUnit.lean` records as the one
missing input to (†).

The identification of Stacks 03LW moves out of the projection; what is left is the unit of
Stacks 03D7, whose projection is the extension-of-scalars unit applied to the projection of the
topos-level unit of sheaves of sets; the identification of Stacks 03LW absorbs the
extension-of-scalars unit into the comparison of Stacks 03LQ
(`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_extendScalars_unit`); and
that comparison turns the topos-level unit into the unit of étale restriction of sheaves of
sets, whose chart projection is the restriction. -/
theorem chartSetProj_etaleModulePullbackAdjunction_unit
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (x : M.val.obj (op V)) :
    chartSetProj B S hS f hrep
        (moduleSetSheaf B S hS X ((etaleModulePullback.{u, u} B S hS f hf).obj M)) V
        (((etaleModulePullbackAdjunction B S hS f hf).unit.app M).val.app (op V) x) =
      M.val.map ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).counit.app V).op x :=
  ((chartSetProj_etaleModulePullbackAdjunction_unit_eq B S hS f hf hrep M V x).trans
      (modulePullbackIso_chartSetProj_modulePullbackAdjunction_unit
        B S hS f hf hrep M V x)).trans
    ((modulePullbackIsoEtaleModulePullback_hom_app_extendScalars_unit B S hS f hf M
        (op ((smallBaseChange B S hS f hrep).obj V))
        (chartSetProj B S hS f hrep
          ((smallToposMorphismTypeU B S hS f).inverseImage.obj
            (moduleSetSheaf B S hS Y M)) V
          (((smallToposMorphismTypeU B S hS f).adj.unit.app
            (moduleSetSheaf B S hS Y M)).hom.app (op V) x))).trans
      (inverseImageIso_chartSetProj_adj_unit B S hS f hf hrep M V x))

/-! ### (†) -/

/-- The unit of Stacks 03LU followed by the hand-built comparison of the two direct images is
the unit of the base-change adjunction, at a module.  Both sides are computed on sections: the
left by `AlgebraicGeometry.Space.chartSetProj_etaleModulePullbackAdjunction_unit`, the right by
`AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction_unit_app_val_app`. -/
theorem etaleModulePullbackAdjunction_unit_comp_chartIso
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (etaleModulePullbackAdjunction B S hS f hf).unit.app M ≫
        (modulePushforwardChartIso B S hS f hrep).hom.app
          ((etaleModulePullback.{u, u} B S hS f hf).obj M) =
      (etaleModulePullbackSmallBaseChangeAdjunction B S hS f hf hrep).unit.app M := by
  refine Stacks.ChartUnitTransport.hom_ext_val_app_apply_unop (fun V x ↦ ?_)
  refine Eq.trans (Stacks.Sheaves.RingedToposModules.comp_val_app_apply
    ((etaleModulePullbackAdjunction B S hS f hf).unit.app M)
    ((modulePushforwardChartIso B S hS f hrep).hom.app
      ((etaleModulePullback.{u, u} B S hS f hf).obj M)) (op V) x) ?_
  refine Eq.trans (modulePushforwardChartIso_hom_app_chartSetProj B S hS f hrep
    ((etaleModulePullback.{u, u} B S hS f hf).obj M) V
    (((etaleModulePullbackAdjunction B S hS f hf).unit.app M).val.app (op V) x)) ?_
  exact chartSetProj_etaleModulePullbackAdjunction_unit B S hS f hf hrep M V x

/-- The unit equation in the shape
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso_eq_chartIso_symm_of_unit` asks
for. -/
theorem etaleModulePullbackSmallBaseChangeAdjunction_unit_comp_chartIso_inv :
    (etaleModulePullbackSmallBaseChangeAdjunction B S hS f hf hrep).unit ≫
        Functor.whiskerLeft (etaleModulePullback.{u, u} B S hS f hf)
          (modulePushforwardChartIso B S hS f hrep).inv =
      (etaleModulePullbackAdjunction B S hS f hf).unit := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  refine Eq.trans (congrArg
    (fun m ↦ m ≫ (modulePushforwardChartIso B S hS f hrep).inv.app
      ((etaleModulePullback.{u, u} B S hS f hf).obj M))
    (etaleModulePullbackAdjunction_unit_comp_chartIso B S hS f hf hrep M).symm) ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m ↦ (etaleModulePullbackAdjunction B S hS f hf).unit.app M ≫ m)
        ((modulePushforwardChartIso B S hS f hrep).hom_inv_id_app
          ((etaleModulePullback.{u, u} B S hS f hf).obj M))).trans (Category.comp_id _))

/-- **(†): the adjoint-canonical comparison of the two direct images of modules is the
hand-built one.**  The comparison
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso` given by uniqueness of a right
adjoint is the inverse of the hand-built
`AlgebraicGeometry.Space.modulePushforwardChartIso`. -/
theorem smallBaseChangeModulePushforwardIso_eq_chartIso_symm :
    smallBaseChangeModulePushforwardIso B S hS f hf hrep =
      (modulePushforwardChartIso B S hS f hrep).symm :=
  smallBaseChangeModulePushforwardIso_eq_chartIso_symm_of_unit B S hS f hf hrep
    (etaleModulePullbackSmallBaseChangeAdjunction_unit_comp_chartIso_inv B S hS f hf hrep)

end AlgebraicGeometry.Space

end
