module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantCoefficients
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSite
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingedSiteTwoReadings
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# The small étale site ringed by a constant coefficient ring, as a small ringed site

Let `X` be a scheme and `Λ` a commutative ring. Sheaves of `Λ`-modules on the small étale site of
`X` (`Stacks.EtaleCohomology.EtaleModules`, valued in `ModuleCat Λ`) are the same thing as
sheaves of modules over the constant sheaf of rings `Λ̲` on that site. The derived machinery for
sheaves of modules on a ringed site (derived tensor product, derived internal Hom, relative cup
product, ...) is stated for a ringed site whose objects, morphisms, section rings and modules all
live in one universe, while the small étale site of `X : Scheme.{u}` has objects in `Type (u + 1)`
and morphisms in `Type u`, and its module coefficients live in `max (u + 1) r`.

This file therefore attaches to `X` the ringed site `etaleRingedSite Λ X`: the small model
`AsSmall X.Etale` of the small étale site, with the topology induced along the equivalence, ringed
by the constant sheaf of rings with value `Λ` (lifted to the coefficient universe), and identifies
its sheaves of modules with `EtaleModules Λ X`, both on abelian and on derived categories.

## Main definitions

* `Stacks.EtaleCohomology.etaleRingedSite`: the ringed site `(X_étale, Λ̲)`, small model.
* `Stacks.EtaleCohomology.etaleModulesEquivalence`: `EtaleModules Λ X ≌ Mod(X_étale, Λ̲)`.
* `Stacks.EtaleCohomology.etaleDerivedEquivalence`: the induced equivalence of unbounded derived
  categories `D(X_étale, Λ) ≌ D(Mod(X_étale, Λ̲))`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- The topology of the small model `AsSmall X.Etale` of the small étale site of `X`, induced
along the equivalence with `X.Etale`. -/
abbrev etaleSmallModelTopology : GrothendieckTopology (AsSmall.{max (u + 1) r} X.Etale) :=
  Stacks.UniverseLift.liftTopology.{max (u + 1) r} X.smallEtaleTopology

/-- **The small étale site of `X` ringed by the constant coefficient ring `Λ`**, as a ringed site
in the single coefficient universe `max (u + 1) r`: the small model `AsSmall X.Etale` of the
small étale site with its induced topology, and the constant sheaf of commutative rings with value
`Λ` (lifted to that universe). -/
abbrev etaleRingedSite : RingedSite.{max (u + 1) r, max (u + 1) r, max (u + 1) r} :=
  RingedSite.constant (etaleSmallModelTopology.{u, r} X) (ULift.{max (u + 1) r} Λ)

/-- Sheaves of modules over the constant ring sheaf on the small model of the small étale site.
-/
abbrev EtaleRingedModules : Type (max (u + 1) r + 1) :=
  SheafOfModules.{max (u + 1) r}
    (Stacks.SheafOfModules.Tensor.ringSheaf (etaleRingedSite.{u, r} Λ X).O)

/-- **Composing with an equivalence of coefficient categories is an equivalence of sheaf
categories**, with both functors the composition functors `sheafCompose`. -/
def sheafComposeEquivalence {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {A B : Type*} [Category* A] [Category* B] (E : A ≌ B)
    [J.HasSheafCompose E.functor] [J.HasSheafCompose E.inverse] : Sheaf J A ≌ Sheaf J B :=
  CategoryTheory.Equivalence.mk (sheafCompose J E.functor) (sheafCompose J E.inverse)
    (NatIso.ofComponents (fun F => ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U => E.unitIso.app (F.obj.obj U))
        (fun g => E.unitIso.hom.naturality (F.obj.map g))))
      (fun f => by ext U; exact E.unitIso.hom.naturality (f.hom.app U)))
    (NatIso.ofComponents (fun F => ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U => E.counitIso.app (F.obj.obj U))
        (fun g => E.counitIso.hom.naturality (F.obj.map g))))
      (fun f => by ext U; exact E.counitIso.hom.naturality (f.hom.app U)))

/-- Restriction of scalars along `ULift Λ ≃+* Λ`: `Λ`-modules are `ULift Λ`-modules. -/
abbrev uliftScalars : ModuleCat.{max (u + 1) r} Λ ≌ ModuleCat.{max (u + 1) r}
    (ULift.{max (u + 1) r} Λ) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{max (u + 1) r} Λ ≃+* Λ)

/-- The inverse `AsSmall.down` of the equivalence of the small étale site with its small model
is a dense subsite inclusion for the induced topology. -/
instance asSmallDown_isDenseSubsite_etale :
    (AsSmall.equiv : X.Etale ≌ AsSmall.{max (u + 1) r} X.Etale).inverse.IsDenseSubsite
      (etaleSmallModelTopology.{u, r} X) X.smallEtaleTopology :=
  inferInstanceAs
    ((AsSmall.equiv : X.Etale ≌ AsSmall.{max (u + 1) r} X.Etale).inverse.IsDenseSubsite
      ((AsSmall.equiv : X.Etale ≌ AsSmall.{max (u + 1) r} X.Etale).inverse.inducedTopology
        X.smallEtaleTopology) X.smallEtaleTopology)

/-- The small étale site and its small model have equivalent categories of sheaves of
`Λ`-modules. -/
def etaleModulesSmallModelEquivalence :
    EtaleModules.{u, r} Λ X ≌
      Sheaf (etaleSmallModelTopology.{u, r} X) (ModuleCat.{max (u + 1) r} Λ) :=
  (AsSmall.equiv : X.Etale ≌ AsSmall.{max (u + 1) r} X.Etale).sheafCongr
    X.smallEtaleTopology (etaleSmallModelTopology.{u, r} X) (ModuleCat.{max (u + 1) r} Λ)

/-- Sheaves of `Λ`-modules on the small model are sheaves of `ULift Λ`-modules. -/
def etaleModulesSmallModelULiftEquivalence :
    Sheaf (etaleSmallModelTopology.{u, r} X) (ModuleCat.{max (u + 1) r} Λ) ≌
      Sheaf (etaleSmallModelTopology.{u, r} X)
        (ModuleCat.{max (u + 1) r} (ULift.{max (u + 1) r} Λ)) :=
  sheafComposeEquivalence (etaleSmallModelTopology.{u, r} X) (uliftScalars.{u, r} Λ)

/-- Sheaves of `ULift Λ`-modules on the small model are the sheaves of modules over the
constant sheaf of rings. -/
def etaleRingedModulesEquivalence :
    Sheaf (etaleSmallModelTopology.{u, r} X)
        (ModuleCat.{max (u + 1) r} (ULift.{max (u + 1) r} Λ)) ≌
      EtaleRingedModules.{u, r} Λ X :=
  (Stacks.ConstantRingModules.moduleSheafEquivalence.{max (u + 1) r}
    (ULift.{max (u + 1) r} Λ) (etaleSmallModelTopology.{u, r} X)
    (Stacks.ConstantRingModules.constantRingedSiteRingMap (etaleSmallModelTopology.{u, r} X)
      (ULift.{max (u + 1) r} Λ))).symm

/-- **Sheaves of `Λ`-modules on the small étale site are the sheaves of modules over the constant
ringed site** `etaleRingedSite Λ X`. -/
def etaleModulesEquivalence : EtaleModules.{u, r} Λ X ≌ EtaleRingedModules.{u, r} Λ X :=
  (etaleModulesSmallModelEquivalence.{u, r} Λ X).trans
    ((etaleModulesSmallModelULiftEquivalence.{u, r} Λ X).trans
      (etaleRingedModulesEquivalence.{u, r} Λ X))

/-- The functor of `etaleModulesEquivalence` is additive. -/
instance : (etaleModulesEquivalence.{u, r} Λ X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse functor of `etaleModulesEquivalence` is additive. -/
instance : (etaleModulesEquivalence.{u, r} Λ X).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The derived category `D(X_étale, Λ)` is the derived category of modules over the constant
ringed site**: the equivalence induced by `etaleModulesEquivalence`. -/
def etaleDerivedEquivalence :
    DerivedCategory (EtaleModules.{u, r} Λ X) ≌ DerivedCategory (EtaleRingedModules.{u, r} Λ X) :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (etaleModulesEquivalence.{u, r} Λ X)

end Derived

end Stacks.EtaleCohomology

end
