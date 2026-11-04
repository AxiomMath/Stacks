module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimCocycleUnderived
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimPushCocycleSets
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomCompCocycle
public import StacksFrontier.CategoryTheory.Adjunction.LimitDerivedHomUnitColimPushCocycleMate

/-!
# The underived pullback cocycle on the spaces-étale models, from the pushforward cocycle

The comparisons `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackIso` of the inverse
images of `𝒪`-modules on the spaces-étale models with those on the small étale sites are
compatible with composition as soon as the comparisons
`AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso` of the direct images are: all four
comparisons in the cocycle are adjoint mates
(`AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom_eq` and
`AlgebraicGeometry.Space.spacesEtaleModelPullbackComp_eq_leftAdjointCompIso`), and mates compose
(`CategoryTheory.Adjunction.leftAdjointCompIso_whiskerLeft_comp_mateOfRightIso_of_iso`).

## Main results

* `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom_comp`: the composition law for the
  comparison of inverse images, from the one for the comparison of direct images.
* `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom_comp_of_chart`: the same, with the
  hypothesis taken for the chart comparison
  `AlgebraicGeometry.Space.spacesEtaleModelChartModulesPushforwardIso`, which is the form that
  `moduleSheafFunctor_map_spacesEtaleModelChartModulesPushforwardIso_hom_app` reduces to a
  statement about sheaves of sets.

## Why the hypothesis and the conclusion avoid `NatTrans.app`

With the hypothesis and the conclusion both in pointwise form the
reduction does not go through at all: `exact` and term mode stop at 200,000 heartbeats in `whnf`,
and `convert … using 1`, `using 2` and `using 3` all elaborate but then time out in the *kernel*.
With the hypothesis an equation of isomorphisms and the conclusion an equation of natural
transformations — neither containing `CategoryTheory.NatTrans.app` — the whole reduction costs
about 53,000 heartbeats.  The hypothesis alone, in the isomorphism form, costs about 10,000; in
pointwise form, bridging it to the generic lemma's own shape is what does not finish.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparisons of the inverse images of `𝒪`-modules on the spaces-étale models and on the
small étale sites are compatible with composition**, given that the comparisons
`AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso` of the direct images are.

The composition comparison of the inverse images on the small étale sites is the one induced by
`AlgebraicGeometry.Space.modulePushforwardCompIso` (Stacks 03LU) on the left adjoints, and the one
on the models is `AlgebraicGeometry.Space.spacesEtaleModelPullbackComp`. -/
theorem spacesEtaleModelModulesPullbackHom_comp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z)
    (hpush : Functor.isoWhiskerRight (spacesEtaleModelPushforwardComp B S hS f g)
          (spacesEtaleModelModulesEquiv B S hS Z).functor ≪≫
        spacesEtaleModelModulesPushforwardIso B S hS (f ≫ g) =
      Functor.isoWhiskerLeft (spacesEtaleModelHom B S hS f).pushforwardTopos
          (spacesEtaleModelModulesPushforwardIso B S hS g) ≪≫
        Functor.isoWhiskerRight (spacesEtaleModelModulesPushforwardIso B S hS f)
          (modulePushforward B S hS g) ≪≫
        Functor.isoWhiskerLeft (spacesEtaleModelModulesEquiv B S hS X).functor
          (modulePushforwardCompIso B S hS f g)) :
    Functor.whiskerLeft (spacesEtaleModelModulesEquiv B S hS Z).functor
          (Adjunction.leftAdjointCompIso (smallEtaleModulePullbackModulesAdjunction B S hS g)
            (smallEtaleModulePullbackModulesAdjunction B S hS f)
            (smallEtaleModulePullbackModulesAdjunction B S hS (f ≫ g))
            (modulePushforwardCompIso B S hS f g)).hom ≫
        spacesEtaleModelModulesPullbackHom B S hS (f ≫ g) =
      Functor.whiskerRight (spacesEtaleModelModulesPullbackHom B S hS g)
          (smallEtaleModulePullbackModules B S hS f) ≫
        Functor.whiskerLeft (spacesEtaleModelHom B S hS g).pullbackTopos
          (spacesEtaleModelModulesPullbackHom B S hS f) ≫
        Functor.whiskerRight (spacesEtaleModelPullbackComp B S hS f g).hom
          (spacesEtaleModelModulesEquiv B S hS X).functor := by
  rw [spacesEtaleModelModulesPullbackHom_eq, spacesEtaleModelModulesPullbackHom_eq,
    spacesEtaleModelModulesPullbackHom_eq]
  exact Adjunction.leftAdjointCompIso_whiskerLeft_comp_mateOfRightIso_of_iso
    (spacesEtaleModelHom B S hS g).pullbackPushforwardAdjunctionTopos
    (spacesEtaleModelHom B S hS f).pullbackPushforwardAdjunctionTopos
    (spacesEtaleModelHom B S hS (f ≫ g)).pullbackPushforwardAdjunctionTopos
    (smallEtaleModulePullbackModulesAdjunction B S hS g)
    (smallEtaleModulePullbackModulesAdjunction B S hS f)
    (smallEtaleModulePullbackModulesAdjunction B S hS (f ≫ g))
    (spacesEtaleModelModulesPushforwardIso B S hS g)
    (spacesEtaleModelModulesPushforwardIso B S hS f)
    (spacesEtaleModelModulesPushforwardIso B S hS (f ≫ g))
    (spacesEtaleModelPushforwardComp B S hS f g)
    (modulePushforwardCompIso B S hS f g) hpush
    (spacesEtaleModelPullbackComp B S hS f g)
    (spacesEtaleModelPullbackComp_eq_leftAdjointCompIso B S hS f g)

/-- `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom_comp` with its hypothesis taken
for the chart comparison `AlgebraicGeometry.Space.spacesEtaleModelChartModulesPushforwardIso`
instead, through
`AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso_cocycle_of_chart`. -/
theorem spacesEtaleModelModulesPullbackHom_comp_of_chart {X Y Z : AlgebraicSpaces B S hS}
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
    Functor.whiskerLeft (spacesEtaleModelModulesEquiv B S hS Z).functor
          (Adjunction.leftAdjointCompIso (smallEtaleModulePullbackModulesAdjunction B S hS g)
            (smallEtaleModulePullbackModulesAdjunction B S hS f)
            (smallEtaleModulePullbackModulesAdjunction B S hS (f ≫ g))
            (modulePushforwardCompIso B S hS f g)).hom ≫
        spacesEtaleModelModulesPullbackHom B S hS (f ≫ g) =
      Functor.whiskerRight (spacesEtaleModelModulesPullbackHom B S hS g)
          (smallEtaleModulePullbackModules B S hS f) ≫
        Functor.whiskerLeft (spacesEtaleModelHom B S hS g).pullbackTopos
          (spacesEtaleModelModulesPullbackHom B S hS f) ≫
        Functor.whiskerRight (spacesEtaleModelPullbackComp B S hS f g).hom
          (spacesEtaleModelModulesEquiv B S hS X).functor :=
  spacesEtaleModelModulesPullbackHom_comp B S hS f g
    (spacesEtaleModelModulesPushforwardIso_cocycle_of_chart B S hS f g hchart)

end AlgebraicGeometry.Space

end
