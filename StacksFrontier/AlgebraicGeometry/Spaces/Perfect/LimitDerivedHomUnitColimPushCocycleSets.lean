module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomCompCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelPushforwardComparison
public import StacksFrontier.CategoryTheory.Adjunction.LimitDerivedHomUnitColimPushCocycleMate

/-!
# The underived pushforward comparison of Stacks 03G1 on underlying sheaves of sets

`AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso` compares the direct image of
`𝒪`-modules along the morphism of models of the ringed spaces-étale sites with the direct image on
the small étale sites, under the equivalences of Stacks 03G1.  It is built in two steps: the
comparison `AlgebraicGeometry.Space.spacesEtaleModelChartModulesPushforwardIso` for the *chart*
functor `AlgebraicGeometry.Space.spacesEtaleModelChartModules`, conjugated by the identification
`AlgebraicGeometry.Space.spacesEtaleModelChartModulesIso` of that functor with the functor of the
equivalence.

This file shows that the first step is **determined on underlying sheaves of sets**, by the square
`AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso` of direct images of sheaves of sets,
and that the second step is pure formalism.  Together they reduce the composition law for
`spacesEtaleModelModulesPushforwardIso` to a statement about sheaves of sets.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleModelChartModules_comp_moduleSheafFunctor` and
  `AlgebraicGeometry.Space.pushforwardTopos_comp_moduleSheafFunctor`: two sides of the square of
  module functors have the corresponding sides of the square of functors of sheaves of sets as
  their underlying sheaves of sets, on the nose.  The third,
  `AlgebraicGeometry.Space.modulePushforward_comp_moduleSheafFunctor`, is already in
  `StacksFrontier/AlgebraicGeometry/Spaces/ModuleSetSheafCommutation.lean`.
* `moduleSheafFunctor_map_spacesEtaleModelChartModulesPushforwardIso_hom_app` (in the namespace
  `AlgebraicGeometry.Space`):
  **the chart comparison of direct images of modules is
  `AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso` on underlying sheaves of sets.**
* `AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso_cocycle_of_chart`: the
  composition law for `spacesEtaleModelModulesPushforwardIso` follows from the one for
  `spacesEtaleModelChartModulesPushforwardIso`.

## Implementation notes

The comparison for the *equivalence* functor does **not** descend to
`spacesEtaleModelChartDirectImageIso`: `spacesEtaleModelChartModules B S hS Z` and
`(spacesEtaleModelModulesEquiv B S hS Z).functor` do not have the same underlying sheaf of sets
even up to definitional unfolding, because the latter goes through the model of the small étale
site and the Comparison Lemma for it.  That is why the descent is stated for the chart functor and
the passage to the equivalence is done separately, by
`CategoryTheory.Adjunction.cocycle_iso_conj`.

All the statements below are at the level of objects or of `Iso.app`, never inside
`CategoryTheory.NatTrans.app`, and the descent is proved by `Sheaf.hom_ext_sections`: the same
claim as a single `rfl` on the two morphisms of sheaves exceeds the heartbeat limit, while section
by section each unfolding is small.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The chart functor of Stacks 03G1, on underlying sheaves of sets, is restriction of sheaves of
sets along the chart `AlgebraicGeometry.Space.spacesEtaleModelChart`. -/
theorem spacesEtaleModelChartModules_comp_moduleSheafFunctor (Z : AlgebraicSpaces B S hS) :
    spacesEtaleModelChartModules B S hS Z ⋙
        Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z) =
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelStructureSheaf B S hS Z)) ⋙
        (spacesEtaleModelChart B S hS Z).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS Z.1) (smallModelTopology B S hS Z) :=
  rfl

variable {X Y : AlgebraicSpaces B S hS}

/-- The direct image of modules along the morphism of models, on underlying sheaves of sets, is
restriction along the base change `AlgebraicGeometry.Space.smallModelBaseChange`. -/
theorem pushforwardTopos_comp_moduleSheafFunctor (f : X ⟶ Y) :
    (spacesEtaleModelHom B S hS f).pushforwardTopos ⋙
        Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelStructureSheaf B S hS Y)) =
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelStructureSheaf B S hS X)) ⋙
        smallModelBaseChangeRestriction B S hS f :=
  rfl

/-- **The chart comparison of the direct images of `𝒪`-modules is the comparison
`AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso` of the direct images of sheaves of
sets**, on underlying sheaves of sets.  Both sides are the restriction of a section along the same
morphism of the model of `X`. -/
theorem moduleSheafFunctor_map_spacesEtaleModelChartModulesPushforwardIso_hom_app (f : X ⟶ Y)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((spacesEtaleModelChartModulesPushforwardIso B S hS f).hom.app M) =
      (spacesEtaleModelChartDirectImageIso B S hS f).hom.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelStructureSheaf B S hS X))).obj M) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- **The composition law for the comparison of direct images of Stacks 03G1 follows from the one
for the chart comparison.**  The two differ by conjugation with
`AlgebraicGeometry.Space.spacesEtaleModelChartModulesIso`, which is what
`AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso` is defined to be, and the cocycle
condition is stable under that conjugation. -/
theorem spacesEtaleModelModulesPushforwardIso_cocycle_of_chart {Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hchart : Functor.isoWhiskerRight (spacesEtaleModelPushforwardComp B S hS f g)
          (spacesEtaleModelChartModules B S hS Z) ≪≫
        spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g) =
      Functor.isoWhiskerLeft (spacesEtaleModelHom B S hS f).pushforwardTopos
          (spacesEtaleModelChartModulesPushforwardIso B S hS g) ≪≫
        Functor.isoWhiskerRight (spacesEtaleModelChartModulesPushforwardIso B S hS f)
          (modulePushforward B S hS g) ≪≫
        Functor.isoWhiskerLeft (spacesEtaleModelChartModules B S hS X)
          (modulePushforwardCompIso B S hS f g)) :
    Functor.isoWhiskerRight (spacesEtaleModelPushforwardComp B S hS f g)
          (spacesEtaleModelModulesEquiv B S hS Z).functor ≪≫
        spacesEtaleModelModulesPushforwardIso B S hS (f ≫ g) =
      Functor.isoWhiskerLeft (spacesEtaleModelHom B S hS f).pushforwardTopos
          (spacesEtaleModelModulesPushforwardIso B S hS g) ≪≫
        Functor.isoWhiskerRight (spacesEtaleModelModulesPushforwardIso B S hS f)
          (modulePushforward B S hS g) ≪≫
        Functor.isoWhiskerLeft (spacesEtaleModelModulesEquiv B S hS X).functor
          (modulePushforwardCompIso B S hS f g) :=
  Adjunction.cocycle_iso_conj
    (spacesEtaleModelChartModulesPushforwardIso B S hS g)
    (spacesEtaleModelChartModulesPushforwardIso B S hS f)
    (spacesEtaleModelChartModulesPushforwardIso B S hS (f ≫ g))
    (spacesEtaleModelPushforwardComp B S hS f g)
    (modulePushforwardCompIso B S hS f g)
    (spacesEtaleModelChartModulesIso B S hS Z)
    (spacesEtaleModelChartModulesIso B S hS Y)
    (spacesEtaleModelChartModulesIso B S hS X)
    hchart

end AlgebraicGeometry.Space

end
