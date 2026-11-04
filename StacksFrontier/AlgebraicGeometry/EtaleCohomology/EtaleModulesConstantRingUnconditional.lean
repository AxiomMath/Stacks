module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.CompactGenerationOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Étale modules and the forgetful functor to abelian sheaves

For a ring `Λ` and a scheme `X`, the functor `etaleModuleForgetAb Λ X` sending a sheaf of
`Λ`-modules on the small étale site of `X` to its underlying abelian sheaf agrees, up to natural
isomorphism, with the equivalence `EtaleModules Λ X ≌ SheafOfModules Λ̲` followed by
`SheafOfModules.toSheaf`. Consequently it is additive, exact and conservative.

## Main definitions

* `uliftCoefficientCompForgetGeneral`: The underlying abelian sheaf is unchanged by the change
  of coefficients along `ModuleCat Λ ≌ ModuleCat (ULift Λ)`.
* `etaleModuleSheafEquivalenceFunctorCompToSheafGeneral`: The functor of the equivalence
  `EtaleModules Λ X ≌ SheafOfModules Λ̲` followed by `SheafOfModules.toSheaf` is isomorphic to
  `etaleModuleForgetAb Λ X`.

## Main results

* `etaleModuleForget_additive_general`: `etaleModuleForgetAb Λ X` is additive.
* `etaleModuleForget_preservesFiniteLimits_general`: `etaleModuleForgetAb Λ X` preserves finite
  limits.
* `etaleModuleForget_preservesFiniteColimits_general`: `etaleModuleForgetAb Λ X` preserves
  finite colimits.
* `etaleModuleForget_reflectsIsomorphisms`: `etaleModuleForgetAb Λ X` reflects isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.SheafOfModules.ConstantRing

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] (X : Scheme.{u})

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp

/-- Changing the coefficients along `ModuleCat Λ ≌ ModuleCat (ULift Λ)` does not change the
underlying abelian sheaves. -/
def uliftCoefficientCompForgetGeneral :
    (Sheaf.coefficientEquivalence X.smallEtaleTopology
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max (u + 1) r}
          (ULift.ringEquiv : ULift.{u + 1} Λ ≃+* Λ))).functor ⋙
        sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{max (u + 1) r} (ULift.{u + 1} Λ)) AddCommGrpCat.{max (u + 1) r}) ≅
      _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X :=
  NatIso.ofComponents
    (fun F => (fullyFaithfulSheafToPresheaf X.smallEtaleTopology _).preimageIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (by intro U V g; rfl)))
    (by intro F G φ; rfl)

/-- **The equivalence `EtaleModules Λ X ≌ SheafOfModules Λ̲` is compatible with forgetting the
module structure**: its functor followed by `SheafOfModules.toSheaf` is
`_root_.Stacks.EtaleCohomology.etaleModuleForgetAb`. -/
def etaleModuleSheafEquivalenceFunctorCompToSheafGeneral :
    (etaleModuleSheafEquivalence.{u, r} Λ X).functor ⋙
        SheafOfModules.toSheaf (etaleConstantRingSheaf.{u, r} Λ X) ≅
      _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X :=
  Functor.associator
      (Sheaf.coefficientEquivalence X.smallEtaleTopology
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max (u + 1) r}
          (ULift.ringEquiv : ULift.{u + 1} Λ ≃+* Λ))).functor
      (sheafifiedConstRingModulesEquivalence.{max (u + 1) r, max (u + 1) r, u, u + 1}
      X.smallEtaleTopology (ULift.{u + 1} Λ) :
        Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} (ULift.{u + 1} Λ)) ≌
          SheafOfModules.{max (u + 1) r} (etaleConstantRingSheaf.{u, r} Λ X)).functor
      (SheafOfModules.toSheaf (etaleConstantRingSheaf.{u, r} Λ X)) ≪≫
    Functor.isoWhiskerLeft _
      (sheafifiedConstRingModulesEquivalenceFunctorCompToSheaf.{max (u + 1) r, max (u + 1) r, u,
        u + 1} X.smallEtaleTopology
        (ULift.{u + 1} Λ)) ≪≫
    uliftCoefficientCompForgetGeneral.{u, r} Λ X

/-- The forgetful functor from étale `Λ`-modules to abelian sheaves is additive. -/
instance etaleModuleForget_additive_general :
    (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).Additive where
  map_add := by intros; rfl

/-- The forgetful functor from étale `Λ`-modules to abelian sheaves preserves finite limits. -/
instance etaleModuleForget_preservesFiniteLimits_general :
    PreservesFiniteLimits (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X) :=
  preservesFiniteLimits_of_natIso (etaleModuleSheafEquivalenceFunctorCompToSheafGeneral.{u, r} Λ X)

/-- The forgetful functor from étale `Λ`-modules to abelian sheaves preserves finite colimits. -/
instance etaleModuleForget_preservesFiniteColimits_general :
    PreservesFiniteColimits (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X) :=
  preservesFiniteColimits_of_natIso
    (etaleModuleSheafEquivalenceFunctorCompToSheafGeneral.{u, r} Λ X)

/-- The forgetful functor from étale `Λ`-modules to abelian sheaves reflects isomorphisms. -/
instance etaleModuleForget_reflectsIsomorphisms :
    (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).ReflectsIsomorphisms :=
  reflectsIsomorphisms_of_iso (etaleModuleSheafEquivalenceFunctorCompToSheafGeneral.{u, r} Λ X)

end Stacks.EtaleCohomology

end
