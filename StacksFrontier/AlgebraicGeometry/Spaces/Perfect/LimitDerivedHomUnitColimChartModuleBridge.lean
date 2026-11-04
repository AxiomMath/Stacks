module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushTransitionNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleSetSheafCommutation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimChartCocycle

/-!
# The chart comparison of the direct images of `𝒪`-modules, on underlying sheaves of sets

`AlgebraicGeometry.Space.spacesEtaleModelChartModulesPushforwardIso` compares the direct image
of `𝒪`-modules along a morphism of the spaces-étale models of Stacks 03G1 with the direct image
on the small étale sites.  On underlying sheaves of sets that comparison is the square
`AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso`, whose composition law is
`AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso_cocycle_moduleSheaf` — but
stated with the five factors spelled the way the *sheaves of sets* side spells them.  **This file
carries that equation to the spelling of the module side**, factor by factor, which is the step
the composition law for the comparison itself is waiting on: it is the hypothesis `hchart` of
`AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso_cocycle_of_chart` and of
`AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom_comp_of_chart`, read through the
sheaf-of-sets functor.

## Main results

* `AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle`: **the
  cocycle for the chart comparison of the direct images of `𝒪`-modules, on underlying sheaves of
  sets**, with every factor written as the module side writes it — the image under the
  sheaf-of-sets functor of each of the five morphisms of modules the cocycle is built from.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_comp`: the
  same with each side a single image of a composite, which is the form
  `Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor` consumes.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_sections`:
  the same read on a section.
* `AlgebraicGeometry.Space.comp_eq_of_moduleSheafFunctor_sections`: a two-factor composite of
  morphisms of `𝒪`-modules equals a three-factor one as soon as the composites of the underlying
  morphisms of sheaves of sets agree on sections.

## What is still open, and exactly where

`hchart` itself is **not** proved here.  What is missing is the single step from
`moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle` to the same equation *in the category
of modules*; the two results above are its two halves, and feeding the second to the first is
what does not fit.  Supplying
`moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_sections` to
`comp_eq_of_moduleSheafFunctor_sections` costs more than 200,000 heartbeats, with the five
morphisms inferred and with all five given explicitly alike; so does
`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor` applied to
`moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_comp`, directly, through a wrapper of
it specialised to the structure sheaf of an algebraic space at variable morphisms, through `ext`
and a `congrArg` on a section, through
`Stacks.SheafOfModules.comp_eq_of_forall_val_app_apply` with the section passages taken by
`simp only`, and through those passages split off into declarations of their own.  Once that step
is available, the rest is cheap: `CategoryTheory.Iso.ext`,
`CategoryTheory.NatTrans.ext` and `funext` expand the whiskers for about 15,000 heartbeats, and
the two composition laws then follow from the `…_of_chart` results for about 10,000 and
14,000.

## Implementation notes

**Why the passage from the set spelling to the module spelling is split into seven steps.**  The
underlying sheaf of sets of a module on the chart has a module-side and a set-side spelling, and
the two agree only definitionally.  Each single identification is affordable and five of them in
one `isDefEq` are not: the chart identification
`msf.obj ((chartModules W).obj N) = (chartRestr W).obj (msf'.obj N)` costs about 18,000
heartbeats, the direct-image one
`msf.obj ((modulePush h).obj N) = (smallEtaleDirectImage h).obj (msf.obj N)` about 16,000 and two
nested about 48,500, while the cocycle has five objects to identify.  Rewriting the five descent
lemmas and then appealing to the set cocycle costs 220,934, and so does every other arrangement
that does the five at once; even the *statement* of one single factor written with both its
objects fully descended — the direct image along `g` of the chart comparison at `f` — costs
200,018 on its own and does not elaborate.

So the factors are brought over to the module spelling **one at a time**, each step its own
declaration with its own heartbeat budget (statement and proof are budgeted separately, which is
why `moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle` reports more than the limit and
still checks).  Three things make the steps cheap:

* The order matters, because a factor is cheap to bring over exactly when the objects it meets are
  already one unfolding away.  Taking the composition comparison of Stacks 03LU first, while the
  direct image beside it is still read on sheaves of sets, costs 211,583; bringing the direct
  image over before the chart comparison at `g` costs 953,028, a *kernel* timeout.  In the order
  below no step exceeds 191,940.
* Two steps change the spelling *inside* a functor's `map` rather than at the objects of a
  composite (`_step₂` and `_step₃`); those are the cheapest, and the two generic descent lemmas
  (this file's `moduleSheafFunctor_map_spacesEtaleModelChartModules_map` and
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map_geometric`) cost 37,109
  and 19,888 where the same identification inside a specific five-factor composite does not
  finish.
* The last step, the comparison `AlgebraicGeometry.Space.modulePushforwardCompIso` of
  Stacks 03LU, is taken **on a section** and not on the morphism of sheaves.  That comparison is
  built from `CategoryTheory.eqToIso` of an equality of functors, and every arrangement that asks
  the kernel to compare it with the geometric comparison on sheaves runs out of the kernel's
  budget: `rw` of the descent lemma, a `congrArg` over the third factor, and the same `congrArg`
  with the descent lemma reversed all fail there.  Performing that `congrArg` inside
  `CategoryTheory.Sheaf.sectionsFunctor` with the section written out runs out of heartbeats in
  the elaborator instead.  What works is
  `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app`, the equality of
  *sections*, with the section it is applied to left for unification to find.

`rw` is not usable for the two steps that change the outer functor: `M` is bound at the spelling
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS
X))` while the direct images on the models are indexed by
`(spacesEtaleModelRingedTopos B S hS X).Modules`, so the abstracted goal is not type-correct at
`implicit` transparency and `rw` reports the pattern as absent.  Those two steps use `congrArg`
over the factor instead.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The chart functor of Stacks 03G1 is, on a morphism, restriction of sheaves of sets along
the chart.**  This is the morphism half of
`AlgebraicGeometry.Space.spacesEtaleModelChartModules_comp_moduleSheafFunctor`; section by
section both sides reindex along the same arrow of the model. -/
theorem moduleSheafFunctor_map_spacesEtaleModelChartModules_map (W : AlgebraicSpaces B S hS)
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS W))} (ψ : M ⟶ N) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map
        ((spacesEtaleModelChartModules B S hS W).map ψ) =
      (spacesEtaleModelChartRestriction B S hS W).map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelStructureSheaf B S hS W))).map ψ) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-! ### From the set spelling of the cocycle to the module spelling, one factor at a time -/

/-- `AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso_cocycle_moduleSheaf` with the
second factor of the left-hand side — the chart comparison at `f ≫ g` — written in the module
spelling. -/
theorem moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₁ (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (spacesEtaleModelChartRestriction B S hS Z).map
          ((smallModelBaseChangeRestrictionComp B S hS f g).hom.app
            ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelStructureSheaf B S hS X))).obj M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g)).hom.app M) =
      (spacesEtaleModelChartDirectImageIso B S hS g).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelStructureSheaf B S hS Y))).obj
            ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M)) ≫
        (smallToposMorphismTypeU B S hS g).pushforward.map
            ((spacesEtaleModelChartDirectImageIso B S hS f).hom.app
              ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
                (spacesEtaleModelStructureSheaf B S hS X))).obj M)) ≫
          (smallToposMorphismTypeU_comp B S hS f g).hom.app
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
              ((spacesEtaleModelChartModules B S hS X).obj M)) := by
  rw [moduleSheafFunctor_map_spacesEtaleModelChartModulesPushforwardIso_hom_app B S hS (f ≫ g)
    M]
  exact spacesEtaleModelChartDirectImageIso_cocycle_moduleSheaf B S hS f g M

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₁`
with the chart comparison at `f` written in the module spelling *inside* the direct image along
`g`.  The direct image is still the one of sheaves of sets, so no object of the composite
changes. -/
theorem moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₂ (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (spacesEtaleModelChartRestriction B S hS Z).map
          ((smallModelBaseChangeRestrictionComp B S hS f g).hom.app
            ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelStructureSheaf B S hS X))).obj M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g)).hom.app M) =
      (spacesEtaleModelChartDirectImageIso B S hS g).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelStructureSheaf B S hS Y))).obj
            ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M)) ≫
        (smallToposMorphismTypeU B S hS g).pushforward.map
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
              ((spacesEtaleModelChartModulesPushforwardIso B S hS f).hom.app M)) ≫
          (smallToposMorphismTypeU_comp B S hS f g).hom.app
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
              ((spacesEtaleModelChartModules B S hS X).obj M)) := by
  rw [moduleSheafFunctor_map_spacesEtaleModelChartModulesPushforwardIso_hom_app B S hS f M]
  exact moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₁ B S hS f g M

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₂`
with the composition isomorphism of the direct images on the models written in the module
spelling *inside* restriction along the chart. -/
theorem moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₃ (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (spacesEtaleModelChartRestriction B S hS Z).map
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelStructureSheaf B S hS Z))).map
            ((spacesEtaleModelPushforwardComp B S hS f g).hom.app M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g)).hom.app M) =
      (spacesEtaleModelChartDirectImageIso B S hS g).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelStructureSheaf B S hS Y))).obj
            ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M)) ≫
        (smallToposMorphismTypeU B S hS g).pushforward.map
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
              ((spacesEtaleModelChartModulesPushforwardIso B S hS f).hom.app M)) ≫
          (smallToposMorphismTypeU_comp B S hS f g).hom.app
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
              ((spacesEtaleModelChartModules B S hS X).obj M)) := by
  rw [moduleSheafFunctor_map_spacesEtaleModelPushforwardComp_hom_app]
  exact moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₂ B S hS f g M

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₃`
with the chart comparison at `g` written in the module spelling. -/
theorem moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₄ (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (spacesEtaleModelChartRestriction B S hS Z).map
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelStructureSheaf B S hS Z))).map
            ((spacesEtaleModelPushforwardComp B S hS f g).hom.app M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g)).hom.app M) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS g).hom.app
            ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M)) ≫
        (smallToposMorphismTypeU B S hS g).pushforward.map
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
              ((spacesEtaleModelChartModulesPushforwardIso B S hS f).hom.app M)) ≫
          (smallToposMorphismTypeU_comp B S hS f g).hom.app
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
              ((spacesEtaleModelChartModules B S hS X).obj M)) := by
  rw [moduleSheafFunctor_map_spacesEtaleModelChartModulesPushforwardIso_hom_app B S hS g
    ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M)]
  exact moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₃ B S hS f g M

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₄`
with the direct image along `g` of the chart comparison at `f` written in the module spelling,
by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map_geometric`. -/
theorem moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₅ (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (spacesEtaleModelChartRestriction B S hS Z).map
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelStructureSheaf B S hS Z))).map
            ((spacesEtaleModelPushforwardComp B S hS f g).hom.app M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g)).hom.app M) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS g).hom.app
            ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
            ((modulePushforward B S hS g).map
              ((spacesEtaleModelChartModulesPushforwardIso B S hS f).hom.app M)) ≫
          (smallToposMorphismTypeU_comp B S hS f g).hom.app
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
              ((spacesEtaleModelChartModules B S hS X).obj M)) := by
  rw [moduleSheafFunctor_map_modulePushforward_map_geometric]
  exact moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₄ B S hS f g M

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₅`
with the first factor of the left-hand side written in the module spelling.  Only the
composition comparison of Stacks 03LU is still read on sheaves of sets. -/
theorem moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₆ (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModules B S hS Z).map
            ((spacesEtaleModelPushforwardComp B S hS f g).hom.app M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g)).hom.app M) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS g).hom.app
            ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
            ((modulePushforward B S hS g).map
              ((spacesEtaleModelChartModulesPushforwardIso B S hS f).hom.app M)) ≫
          (smallToposMorphismTypeU_comp B S hS f g).hom.app
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
              ((spacesEtaleModelChartModules B S hS X).obj M)) := by
  refine (congrArg (fun t ↦ t ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g)).hom.app M))
    (moduleSheafFunctor_map_spacesEtaleModelChartModules_map B S hS Z
      ((spacesEtaleModelPushforwardComp B S hS f g).hom.app M))).trans
    (moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₅ B S hS f g M)

/-- **The cocycle for the chart comparison of the direct images of `𝒪`-modules, on underlying
sheaves of sets.**  Every factor is the image under the sheaf-of-sets functor of the morphism of
modules the cocycle is built from, so this is exactly the cocycle of
`AlgebraicGeometry.Space.spacesEtaleModelChartModulesPushforwardIso` read on underlying sheaves
of sets.

The last spelling change, the comparison of Stacks 03LU, is taken on a section: see this file's
implementation notes. -/
theorem moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModules B S hS Z).map
            ((spacesEtaleModelPushforwardComp B S hS f g).hom.app M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g)).hom.app M) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS g).hom.app
            ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
            ((modulePushforward B S hS g).map
              ((spacesEtaleModelChartModulesPushforwardIso B S hS f).hom.app M)) ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
            ((modulePushforwardCompIso B S hS f g).hom.app
              ((spacesEtaleModelChartModules B S hS X).obj M)) := by
  refine Sheaf.hom_ext_sections fun W s ↦ ?_
  refine (congrArg (fun n ↦ (Sheaf.sectionsFunctor _ W).map n s)
    (moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_step₆ B S hS f g M)).trans ?_
  exact (modulePushforwardCompIso_hom_app_val_app B S hS f g
    ((spacesEtaleModelChartModules B S hS X).obj M) W _).symm

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle` with each
side a single image of a composite of morphisms of modules, which is the form
`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor` consumes. -/
theorem moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((spacesEtaleModelChartModules B S hS Z).map
            ((spacesEtaleModelPushforwardComp B S hS f g).hom.app M) ≫
          (spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g)).hom.app M) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((spacesEtaleModelChartModulesPushforwardIso B S hS g).hom.app
            ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M) ≫
          (modulePushforward B S hS g).map
              ((spacesEtaleModelChartModulesPushforwardIso B S hS f).hom.app M) ≫
            (modulePushforwardCompIso B S hS f g).hom.app
              ((spacesEtaleModelChartModules B S hS X).obj M)) := by
  refine (CategoryTheory.Functor.map_comp _ _ _).trans
    ((moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle B S hS f g M).trans
      ((congrArg (fun t ↦ (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
            ((spacesEtaleModelChartModulesPushforwardIso B S hS g).hom.app
              ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M)) ≫ t)
          (CategoryTheory.Functor.map_comp _ _ _).symm).trans
        (CategoryTheory.Functor.map_comp _ _ _).symm))

/-- **Two composites of morphisms of `𝒪`-modules, one of two factors and one of three, agree as
soon as the composites of their underlying morphisms of sheaves of sets agree on sections.**

Every passage this needs — a composite of morphisms of sheaves of sets on a section, the
underlying morphism of sheaves of sets of a morphism of modules on a section, and the sections of
the sheaf of sets underlying a module against the sections of the module — is taken here, with
the five morphisms variables.  That is the whole content of the statement: asked of the composites
of the cocycle below instead, in any arrangement, each of those passages costs the whole heartbeat
budget. -/
theorem comp_eq_of_moduleSheafFunctor_sections (W : AlgebraicSpaces B S hS)
    {M N P Q R : Modules.{u, u} B S hS W.1 W.2} (a : M ⟶ N) (b : N ⟶ P) (c : M ⟶ Q)
    (d : Q ⟶ R) (e : R ⟶ P)
    (h : ∀ (V : (SmallEtale B S hS W.1)ᵒᵖ)
      (x : ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).obj M).obj.obj V),
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map a ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map b).hom.app V x =
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map c ≫
            (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map d ≫
              (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map e).hom.app V x) :
    a ≫ b = c ≫ d ≫ e :=
  Stacks.SheafOfModules.comp_eq_of_forall_val_app_apply a b c (d ≫ e) fun V x ↦ h V x

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle` read on a
section.  The section is given on the sheaf of sets, which is the side
`CategoryTheory.Sheaf.hom_congr_app_apply` and
`AlgebraicGeometry.Space.comp_eq_of_moduleSheafFunctor_sections` both speak, so nothing is
reconciled here. -/
theorem moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle_sections (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X)))
    (V : (SmallEtale B S hS Z.1)ᵒᵖ)
    (x : ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
      ((spacesEtaleModelChartModules B S hS Z).obj
        (((spacesEtaleModelHom B S hS f).pushforwardTopos ⋙
        (spacesEtaleModelHom B S hS g).pushforwardTopos).obj M))).obj.obj V) :
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModules B S hS Z).map
            ((spacesEtaleModelPushforwardComp B S hS f g).hom.app M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g)).hom.app M)).hom.app V x =
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
          ((spacesEtaleModelChartModulesPushforwardIso B S hS g).hom.app
            ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
            ((modulePushforward B S hS g).map
              ((spacesEtaleModelChartModulesPushforwardIso B S hS f).hom.app M)) ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
            ((modulePushforwardCompIso B S hS f g).hom.app
              ((spacesEtaleModelChartModules B S hS X).obj M))).hom.app V x :=
  Sheaf.hom_congr_app_apply
    (moduleSheafFunctor_map_chartModulesPushforwardIso_cocycle B S hS f g M) V x

end AlgebraicGeometry.Space

end
