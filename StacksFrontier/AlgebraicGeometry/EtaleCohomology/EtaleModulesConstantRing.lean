module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.CompactGenerationOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Étale sheaves of `Λ`-modules are sheaves of modules over the constant sheaf of rings `Λ̲`

Let `X` be a scheme and `Λ` a ring. Sheaves of `Λ`-modules on the small étale site of `X` are
formalised in this development in two ways: as `Stacks.EtaleCohomology.EtaleModules Λ X`, the
sheaves with values in `ModuleCat Λ`, on which cohomology with compact support is built, and as
sheaves of modules `SheafOfModules O` over a sheaf of rings `O`, on which the results about
forgetting the module structure (Stacks 0D6J, 03FD) are proved. This file identifies the first
with the second for `O = Λ̲`, the constant sheaf of rings, compatibly with the functors to
abelian sheaves.

## Main definitions

* `Stacks.EtaleCohomology.etaleConstantRingSheaf`: the constant sheaf of rings `Λ̲` on the small
  étale site of `X`.
* `Stacks.EtaleCohomology.etaleModuleSheafEquivalence`: the equivalence
  `EtaleModules Λ X ≌ SheafOfModules Λ̲`.
* `Stacks.EtaleCohomology.etaleModuleForgetAb`: the functor from sheaves of `Λ`-modules to abelian
  sheaves forgetting the module structure.

## Main results

* `Stacks.EtaleCohomology.etaleModuleSheafEquivalenceFunctorCompToSheaf`: the functor of the
  equivalence followed by `SheafOfModules.toSheaf` is `etaleModuleForgetAb`.
* `Stacks.EtaleCohomology.etaleModuleForgetAb_preservesFiniteLimits` and its colimit and
  reflection companions: forgetting the module structure is exact and conservative.

## Implementation notes

The coefficients of `EtaleModules Λ X` live in `ModuleCat.{max (u + 1) r} Λ` for `Λ : Type r`,
while the theory of sheaves of modules over a sheaf of rings that is used downstream needs the
ring sheaf and the modules in one universe. The constant sheaf of rings is therefore the
sheafification of the constant presheaf with value `ULift.{u + 1} Λ`, and the equivalence is the
composite of the change of coefficients along `ModuleCat Λ ≌ ModuleCat (ULift Λ)`
(`ModuleCat.restrictScalarsEquivalenceOfRingEquiv ULift.ringEquiv`, which does not change the
underlying abelian groups) with the general equivalence
`Stacks.SheafOfModules.ConstantRing.sheafifiedConstRingModulesEquivalence`.

Sheafification of presheaves of rings, and the identification of the sheafification isos with
the locally bijective morphisms, exist on the small étale site with rings in any universe
containing `u + 1`, by `Stacks.Cohomology.hasSheafify_ringCat` and
`Stacks.Cohomology.wEqualsLocallyBijective_ringCat`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.SheafOfModules.ConstantRing

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] (X : Scheme.{u})

/-- Sheafification of presheaves of rings on the small étale site of a scheme, with the rings
in any universe containing that of the objects of the site. -/
instance hasSheafify_smallEtale_ringCat :
    HasSheafify X.smallEtaleTopology RingCat.{max (u + 1) r} :=
  Stacks.Cohomology.hasSheafify_ringCat X.smallEtaleTopology

/-- On the small étale site, with rings in any universe containing that of the objects of the
site, sheafification inverts exactly the locally bijective morphisms of presheaves of rings. -/
instance wEqualsLocallyBijective_smallEtale_ringCat :
    X.smallEtaleTopology.WEqualsLocallyBijective RingCat.{max (u + 1) r} :=
  Stacks.Cohomology.wEqualsLocallyBijective_ringCat X.smallEtaleTopology

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp

/-- The constant sheaf of rings `Λ̲` on the small étale site of `X`: the sheafification of the
constant presheaf of rings with value `Λ`, lifted to the coefficient universe of
`Stacks.EtaleCohomology.EtaleModules`. -/
abbrev etaleConstantRingSheaf : Sheaf X.smallEtaleTopology RingCat.{max (u + 1) r} :=
  sheafifiedConstRing X.smallEtaleTopology (ULift.{u + 1} Λ)

/-- The functor from sheaves of `Λ`-modules on the small étale site of `X` to abelian sheaves
forgetting the module structure. -/
abbrev etaleModuleForgetAb :
    EtaleModules.{u, r} Λ X ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r} :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})

/-- **Étale sheaves of `Λ`-modules are sheaves of modules over the constant sheaf of rings
`Λ̲`.** -/
def etaleModuleSheafEquivalence :
    EtaleModules.{u, r} Λ X ≌
      SheafOfModules.{max (u + 1) r} (etaleConstantRingSheaf.{u, r} Λ X) :=
  (Sheaf.coefficientEquivalence X.smallEtaleTopology
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max (u + 1) r}
        (ULift.ringEquiv : ULift.{u + 1} Λ ≃+* Λ))).trans
    (sheafifiedConstRingModulesEquivalence.{max (u + 1) r, max (u + 1) r, u, u + 1}
      X.smallEtaleTopology (ULift.{u + 1} Λ) :
      Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} (ULift.{u + 1} Λ)) ≌
        SheafOfModules.{max (u + 1) r} (etaleConstantRingSheaf.{u, r} Λ X))

/-- Changing the coefficients along `ModuleCat Λ ≌ ModuleCat (ULift Λ)` does not change the
underlying abelian sheaves. -/
def uliftCoefficientCompForget :
    (Sheaf.coefficientEquivalence X.smallEtaleTopology
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max (u + 1) r}
        (ULift.ringEquiv : ULift.{u + 1} Λ ≃+* Λ))).functor ⋙
        sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{max (u + 1) r} (ULift.{u + 1} Λ)) AddCommGrpCat.{max (u + 1) r}) ≅
      etaleModuleForgetAb.{u, r} Λ X :=
  NatIso.ofComponents
    (fun F => (fullyFaithfulSheafToPresheaf X.smallEtaleTopology _).preimageIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (by intro U V g; rfl)))
    (by intro F G φ; rfl)

/-- **The equivalence `EtaleModules Λ X ≌ SheafOfModules Λ̲` is compatible with forgetting the
module structure**: its functor followed by `SheafOfModules.toSheaf` is
`Stacks.EtaleCohomology.etaleModuleForgetAb`. -/
def etaleModuleSheafEquivalenceFunctorCompToSheaf :
    (etaleModuleSheafEquivalence.{u, r} Λ X).functor ⋙
        SheafOfModules.toSheaf (etaleConstantRingSheaf.{u, r} Λ X) ≅
      etaleModuleForgetAb.{u, r} Λ X :=
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
    uliftCoefficientCompForget.{u, r} Λ X

/-- The forgetful functor from étale sheaves of `Λ`-modules to abelian sheaves is additive. -/
instance etaleModuleForgetAb_additive : (etaleModuleForgetAb.{u, r} Λ X).Additive where
  map_add := by intros; rfl

/-- The forgetful functor from étale sheaves of `Λ`-modules to abelian sheaves preserves finite
limits. -/
instance etaleModuleForgetAb_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModuleForgetAb.{u, r} Λ X) :=
  preservesFiniteLimits_of_natIso (etaleModuleSheafEquivalenceFunctorCompToSheaf.{u, r} Λ X)

/-- The forgetful functor from étale sheaves of `Λ`-modules to abelian sheaves preserves finite
colimits. -/
instance etaleModuleForgetAb_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleForgetAb.{u, r} Λ X) :=
  preservesFiniteColimits_of_natIso (etaleModuleSheafEquivalenceFunctorCompToSheaf.{u, r} Λ X)

/-- The forgetful functor from étale sheaves of `Λ`-modules to abelian sheaves reflects
isomorphisms. -/
instance etaleModuleForgetAb_reflectsIsomorphisms :
    (etaleModuleForgetAb.{u, r} Λ X).ReflectsIsomorphisms :=
  reflectsIsomorphisms_of_iso (etaleModuleSheafEquivalenceFunctorCompToSheaf.{u, r} Λ X)

end Stacks.EtaleCohomology

end
