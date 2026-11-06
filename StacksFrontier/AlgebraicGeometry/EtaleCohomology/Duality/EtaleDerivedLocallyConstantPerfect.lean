module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocallyConstantCohomologyPerfect
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsiteFiniteTypeLarge

/-!
# Complexes with locally constant cohomology over a field are perfect on `(X_étale, Λ̲)`

Let `X` be a scheme and `Λ` a field. An object `K` of `D(X_étale, Λ)` with bounded cohomology all
of whose cohomology sheaves are locally constant of finite type is a **perfect** object
(Stacks 08G5) of the derived category of modules over the constant ringed site
`Stacks.EtaleCohomology.etaleRingedSite Λ X`, on which the derived tensor product and the derived
internal Hom `Stacks.EtaleCohomology.etaleDerivedHom` of `D(X_étale, Λ)` are defined
(`Stacks.EtaleCohomology.isPerfect_etaleDerivedEquivalence_functor_obj`).

The local constancy of the cohomology sheaves, stated on Mathlib's small étale site, is carried to
the small model `AsSmall X.Etale` of the ringed site
(`Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_of_large`)
and across the change of scalars `Λ ≃ ULift Λ`
(`Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence`); perfectness is then
`AlgebraicGeometry.RingedSite.isPerfect_of_isFiniteTypeLocallyConstantModuleSheaf_homology`, whose
input is Stacks 094G.

This is the perfectness of `Rf̄_* Λ` used in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), with `Λ = ℤ/ℓ`.

The statement consumes `Stacks.EtaleCohomology.etaleDerivedEquivalence`, defined in the standard
model `HasDerivedCategory.standard` of the derived category, as a local instance.

## Main results

In the namespace `Stacks.EtaleCohomology`:

* `isFiniteTypeLocallyConstantModuleSheaf_toModuleSheaf_etaleModulesEquivalence`: a locally
  constant sheaf of finite type, read as a module over the constant ringed site.
* `isPerfect_etaleDerivedEquivalence_functor_obj`: the perfectness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- Sheafification of presheaves of `Λ`-modules on the slices of the small model of the small
étale site, at the module universe `u + 1`. -/
local instance hasSheafify_etaleSmallModel_over_moduleCat (S : Scheme.{u}) (R : Type) [Ring R]
    (V : AsSmall.{u + 1} S.Etale) :
    HasSheafify ((etaleSmallModelTopology.{u, 0} S).over V) (ModuleCat.{u + 1} R) :=
  Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1, 0, u + 1, u + 1} R _ V

/-- `Stacks.ConstantSheaf.hasSheafify_over_moduleCat` with its universes pinned to the slices of
the small model and the coefficient universe `u + 1`; instance search leaves the constraint
`u + 1 =?= max (u + 1) ?x` stuck. -/
local instance hasSheafify_etaleSmallModel_over_moduleCat_succ (S : Scheme.{u})
    (R : Type (u + 1)) [Ring R] (V : AsSmall.{u + 1} S.Etale) :
    HasSheafify ((etaleSmallModelTopology.{u, 0} S).over V) (ModuleCat.{u + 1} R) :=
  Stacks.ConstantSheaf.hasSheafify_over_moduleCat.{u + 1, u + 1, u + 1, u + 1} _ R V

attribute [-instance] Stacks.ConstantSheaf.hasSheafify_over_moduleCat

variable {Λ : Type} [Field Λ] {S : Scheme.{u}}

/-- **A locally constant sheaf of finite type, read as a module over the constant ringed site
`(S_étale, Λ̲)`, is locally constant of finite type there**: on the small model `AsSmall S.Etale`,
with coefficients `ULift Λ`. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_toModuleSheaf_etaleModulesEquivalence
    (N : EtaleModules.{u, 0} Λ S)
    (hN : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      S.smallEtaleTopology Λ N) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u + 1, u + 1, 0}
      (etaleSmallModelTopology.{u, 0} S) (ULift.{u + 1} Λ)
      ((Stacks.ConstantRingModules.toModuleSheaf.{u + 1} (ULift.{u + 1} Λ)
        (etaleSmallModelTopology.{u, 0} S)
        (Stacks.ConstantRingModules.constantRingedSiteRingMap (etaleSmallModelTopology.{u, 0} S)
          (ULift.{u + 1} Λ))).obj ((etaleModulesEquivalence.{u, 0} Λ S).functor.obj N)) := by
  open Stacks.ConstantSheaf in
  have h₁ :=
    isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_of_large.{u, u + 1, 0}
      (etaleSmallModelTopology.{u, 0} S) S.smallEtaleTopology
      (AsSmall.equiv : S.Etale ≌ AsSmall.{u + 1} S.Etale).inverse Λ N hN
  have h₂ := Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence
    (etaleSmallModelTopology.{u, 0} S)
    (uliftScalars.{u, 0} Λ : ModuleCat.{u + 1} Λ ≌ ModuleCat.{u + 1} (ULift.{u + 1} Λ))
    (fun M : ModuleCat.{u + 1} Λ => ModuleCat.isFG Λ M)
    (fun M hM => by
      have := (ModuleCat.isFG_iff _).1 hM
      exact (ModuleCat.isFG_iff _).2
        (ModuleCat.moduleFinite_restrictScalars_of_ringEquiv (ULift.ringEquiv : ULift.{u + 1} Λ ≃+* Λ) M))
    _ h₁ _ (Iso.refl _)
  exact ObjectProperty.prop_of_iso
    (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u + 1, u + 1, 0}
      (etaleSmallModelTopology.{u, 0} S) (ULift.{u + 1} Λ))
    ((Stacks.ConstantRingModules.moduleSheafEquivalence.{u + 1} (ULift.{u + 1} Λ)
      (etaleSmallModelTopology.{u, 0} S)
      (Stacks.ConstantRingModules.constantRingedSiteRingMap (etaleSmallModelTopology.{u, 0} S)
        (ULift.{u + 1} Λ))).counitIso.app _).symm h₂

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **A complex with bounded cohomology all of whose cohomology sheaves are locally constant of
finite type over a field is perfect** (Stacks 08G5) as an object of the derived category of
modules over the constant ringed site `(S_étale, Λ̲)`, the category on which
`Stacks.EtaleCohomology.etaleDerivedHom` and `Stacks.EtaleCohomology.etaleDerivedTensor` are
defined. -/
theorem isPerfect_etaleDerivedEquivalence_functor_obj
    (K : DerivedCategory (EtaleModules.{u, 0} Λ S)) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ n : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      S.smallEtaleTopology Λ ((DerivedCategory.homologyFunctor _ n).obj K)) :
    AlgebraicGeometry.RingedSite.IsPerfect.{u + 1, u + 1, u + 1, u + 1} (etaleRingedSite.{u, 0} Λ S)
      ((etaleDerivedEquivalence.{u, 0} Λ S).functor.obj K) := by
  let Φ := (etaleModulesEquivalence.{u, 0} Λ S).functor
  have : ((etaleDerivedEquivalence.{u, 0} Λ S).functor.obj K).IsGE a :=
    Φ.isGE_obj_mapDerivedCategory K a inferInstance
  have : ((etaleDerivedEquivalence.{u, 0} Λ S).functor.obj K).IsLE b :=
    Φ.isLE_obj_mapDerivedCategory K b inferInstance
  refine AlgebraicGeometry.RingedSite.isPerfect_of_isFiniteTypeLocallyConstantModuleSheaf_homology
    (etaleRingedSite.{u, 0} Λ S) (ULift.{u + 1} Λ)
    (Stacks.ConstantRingModules.constantRingedSiteRingMap (etaleSmallModelTopology.{u, 0} S)
      (ULift.{u + 1} Λ)) _ a b (fun n => ?_)
  exact ObjectProperty.prop_of_iso
    (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u + 1, u + 1, 0}
      (etaleSmallModelTopology.{u, 0} S) (ULift.{u + 1} Λ))
    ((Stacks.ConstantRingModules.toModuleSheaf.{u + 1} (ULift.{u + 1} Λ)
        (etaleSmallModelTopology.{u, 0} S)
        (Stacks.ConstantRingModules.constantRingedSiteRingMap (etaleSmallModelTopology.{u, 0} S)
          (ULift.{u + 1} Λ))).mapIso
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso Φ n).app K).symm)
    (isFiniteTypeLocallyConstantModuleSheaf_toModuleSheaf_etaleModulesEquivalence _ (hK n))

end Derived

end Stacks.EtaleCohomology

end
