module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelEtaleDerivedComparison

/-!
# Étale restriction preserves K-injective complexes on the spaces-étale model

Let `j : X ⟶ Y` be an étale morphism of algebraic spaces. Restriction `j^*` of modules on the
spaces-étale models (the pullback of the morphism of ringed topoi
`AlgebraicGeometry.Space.spacesEtaleModelHom j`) is, through the equivalences
`AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` of Stacks 03G1, the étale restriction of
`𝒪`-modules on the small étale sites, which has the exact left adjoint `j_!` (Stacks 03DJ). So it
has an exact left adjoint on the models as well, and by Stacks 08BJ it carries K-injective
complexes to K-injective complexes.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelLowerShriek`: extension by zero on the models, and
  `AlgebraicGeometry.Space.spacesEtaleModelLowerShriekAdjunction`: `j_! ⊣ j^*` there.

## Main results

* `AlgebraicGeometry.Space.isKInjective_spacesEtaleModelHom_pullbackTopos`: `j^*` preserves
  K-injective complexes on the models.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (j : X ⟶ Y) (hj : IsEtale B S hS j.hom)

/-- Restriction along an étale morphism on the spaces-étale models, read through the equivalences
of Stacks 03G1: it is isomorphic to the pullback of `spacesEtaleModelHom j`. -/
def spacesEtaleModelPullbackIsoOfEtale :
    (spacesEtaleModelHom B S hS j).pullbackTopos ≅
      (spacesEtaleModelModulesEquiv B S hS Y).functor ⋙
        etaleModulePullback.{u, u} B S hS j hj ⋙ (spacesEtaleModelModulesEquiv B S hS X).inverse :=
  Functor.isoWhiskerLeft _ (spacesEtaleModelModulesEquiv B S hS X).unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
        (spacesEtaleModelPullbackIsoPushforward B S hS j hj) _ ≪≫
      spacesEtaleModelModulesEquivPostcompIso B S hS j hj) _ ≪≫
    Functor.associator _ _ _

/-- **Extension by zero on the spaces-étale models**: extension by zero `j_!` of Stacks 03DJ on the
small étale sites, read through the equivalences of Stacks 03G1. -/
def spacesEtaleModelLowerShriek :
    (spacesEtaleModelRingedTopos B S hS X).Modules ⥤
      (spacesEtaleModelRingedTopos B S hS Y).Modules :=
  ((spacesEtaleModelModulesEquiv B S hS X).functor ⋙ etaleModuleLowerShriek B S hS j hj) ⋙
    (spacesEtaleModelModulesEquiv B S hS Y).inverse

/-- `j_! ⊣ j^*` on the spaces-étale models. -/
def spacesEtaleModelLowerShriekAdjunction :
    spacesEtaleModelLowerShriek B S hS j hj ⊣ (spacesEtaleModelHom B S hS j).pullbackTopos :=
  (((spacesEtaleModelModulesEquiv B S hS X).toAdjunction.comp
      (etaleModuleLowerShriekAdjunction B S hS j hj)).comp
    (spacesEtaleModelModulesEquiv B S hS Y).symm.toAdjunction).ofNatIsoRight
    (spacesEtaleModelPullbackIsoOfEtale B S hS j hj).symm

/-- Extension by zero on the spaces-étale models preserves finite limits. -/
instance preservesFiniteLimits_spacesEtaleModelLowerShriek :
    PreservesFiniteLimits (spacesEtaleModelLowerShriek B S hS j hj) := by
  unfold spacesEtaleModelLowerShriek
  infer_instance

/-- Extension by zero on the spaces-étale models preserves finite colimits. -/
instance preservesFiniteColimits_spacesEtaleModelLowerShriek :
    PreservesFiniteColimits (spacesEtaleModelLowerShriek B S hS j hj) := by
  unfold spacesEtaleModelLowerShriek
  infer_instance

/-- Extension by zero on the spaces-étale models is additive. -/
instance spacesEtaleModelLowerShriek_additive :
    (spacesEtaleModelLowerShriek B S hS j hj).Additive :=
  Functor.additive_of_preserves_binary_products _

include hj in
/-- **Restriction along an étale morphism preserves K-injective complexes on the spaces-étale
models** (Stacks 08BJ, with the exact left adjoint `j_!`). -/
theorem isKInjective_spacesEtaleModelHom_pullbackTopos
    (I : CochainComplex (spacesEtaleModelRingedTopos B S hS Y).Modules ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((spacesEtaleModelHom B S hS j).pullbackTopos.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
    (spacesEtaleModelLowerShriekAdjunction B S hS j hj) I

end AlgebraicGeometry.Space

end
