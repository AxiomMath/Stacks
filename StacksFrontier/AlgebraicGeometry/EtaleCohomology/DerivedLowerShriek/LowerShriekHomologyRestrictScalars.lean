module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.NagataConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.HigherDirectImageExtendScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LowerShriekGysin
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfCentralIdempotent

/-!
# `R^q f_!` commutes with restriction of scalars, naturally

Let `f : X ⟶ Y` be a morphism of schemes with a compactification `f = f̄ ∘ j`, let `ρ : Λ ⟶ Λ'`
be a homomorphism of commutative rings and `q` a natural number. For a sheaf `G` of
`Λ'`-modules on `X_étale` placed in degree `0`, both sides of

`R^q f_!(res_ρ G) ≅ res_ρ (R^q f_! G)`

are `R^q f̄_*(j_! -)` (extension by zero is exact), and extension by zero and the higher direct
images commute with restriction of scalars. This file records the isomorphism as a natural
isomorphism of functors `EtaleModules Λ' X ⥤ EtaleModules Λ Y`, so that it carries the
endomorphisms of `G` (for instance the action of `Λ'`) across; the tree had only the
existence of an isomorphism object by object
(`Stacks.EtaleCohomology.nonempty_homology_derivedLowerShriek_restrictScalars_iso`).

## Main results

* `Stacks.EtaleCohomology.lowerShriekHomologyIsoRightDerived`: `R^q f_! ≅ R^q f̄_* ∘ j_!`,
  naturally.
* `Stacks.EtaleCohomology.lowerShriekHomologyRestrictScalarsIso`:
  `res_ρ ⋙ R^q f_! ≅ R^q f_! ⋙ res_ρ`.
* `Stacks.EtaleCohomology.lowerShriekHomology_map_etaleModuleSMul`: `R^q f_!` carries
  multiplication by a scalar to multiplication by that scalar (also for extension by zero and
  restriction along an étale morphism).

## Implementation notes

`Stacks.EtaleCohomology.lowerShriekHomology` lives in the standard model
`HasDerivedCategory.standard`, and so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

-- instances of `Stacks.Models.RegularModelSituation` whose conclusions (`QuasiCompact ?f`, ...)
-- match every goal and send instance search into a loop; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

section RightDerived

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))

/-- **`R^q f_! = R^q f̄_* ∘ j_!` on sheaves, naturally**: `Rf_! = Rf̄_* ∘ Rj_!` and
`Rj_!(G[0]) = (j_! G)[0]`, extension by zero being exact. -/
def lowerShriekHomologyIsoRightDerived (q : ℕ) :
    lowerShriekHomology Λ f j q ≅
      etaleModuleExtensionByZero.{u, 0} Λ j.immersion ⋙
        (etaleModuleDirectImage.{u, 0} Λ j.toBase).rightDerived q :=
  lowerShriekHomologyIsoSingle Λ f j q ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
          (etaleModuleExtensionByZero.{u, 0} Λ
            j.immersion).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus ≪≫
        Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) 0)
      (etaleModuleDerivedDirectImage.{u, 0} Λ j.toBase ⋙
        DerivedCategory.Plus.homologyFunctor _ (q : ℤ)) ≪≫
    Functor.isoWhiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ j.immersion)
      (Stacks.DerivedIndexing.rightDerivedIso (etaleModuleDirectImage.{u, 0} Λ j.toBase) q).symm

end RightDerived

section RestrictScalars

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X Y : Scheme.{u}} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f))

/-- **`R^q f_!` commutes with restriction of scalars, naturally**: for a homomorphism of
commutative rings `ρ : Λ ⟶ Λ'`, `R^q f_!(res_ρ G) ≅ res_ρ(R^q f_! G)` naturally in the sheaf `G`
of `Λ'`-modules. Both sides are `R^q f̄_*(j_! -)`
(`Stacks.EtaleCohomology.lowerShriekHomologyIsoRightDerived`); extension by zero commutes with
`res_ρ` (`Stacks.EtaleCohomology.etaleModuleExtensionByZeroRestrictScalars`), and so do the
higher direct images ([Stacks, Tag 0D6J],
`Stacks.EtaleCohomology.etaleModuleRightDerivedDirectImageRestrictScalarsNatIso`). -/
def lowerShriekHomologyRestrictScalarsIso (q : ℕ) :
    etaleModuleRestrictScalars ρ X ⋙ lowerShriekHomology Λ f j q ≅
      lowerShriekHomology Λ' f j q ⋙ etaleModuleRestrictScalars ρ Y :=
  Functor.isoWhiskerLeft (etaleModuleRestrictScalars ρ X)
      (lowerShriekHomologyIsoRightDerived Λ f j q) ≪≫
    Functor.isoWhiskerRight (etaleModuleExtensionByZeroRestrictScalars ρ j.immersion)
      ((etaleModuleDirectImage.{u, 0} Λ j.toBase).rightDerived q) ≪≫
    Functor.isoWhiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ' j.immersion)
      (etaleModuleRightDerivedDirectImageRestrictScalarsNatIso ρ j.toBase q).symm ≪≫
    Functor.isoWhiskerRight (lowerShriekHomologyIsoRightDerived Λ' f j q).symm
      (etaleModuleRestrictScalars ρ Y)

end RestrictScalars

section SMul

variable {A : Type} [CommRing A]

/-- Restriction along an étale morphism commutes with multiplication by a scalar. -/
theorem etaleModuleRestriction_map_etaleModuleSMul {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (a : A) (G : EtaleModules.{u, 0} A X) :
    (etaleModuleRestriction.{u, 0} A j).map ((etaleModuleSMul X a).app G) =
      (etaleModuleSMul U a).app ((etaleModuleRestriction.{u, 0} A j).obj G) := by
  apply Sheaf.hom_ext
  ext V x
  rfl

/-- Extension by zero commutes with multiplication by a scalar: it is left adjoint to the
restriction, which does. -/
theorem etaleModuleExtensionByZero_map_etaleModuleSMul {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (a : A) (G : EtaleModules.{u, 0} A U) :
    (etaleModuleExtensionByZero.{u, 0} A j).map ((etaleModuleSMul U a).app G) =
      (etaleModuleSMul X a).app ((etaleModuleExtensionByZero.{u, 0} A j).obj G) :=
  CategoryTheory.map_app_of_adjunction (etaleModuleExtensionByZeroAdj.{u, 0} A j)
    (etaleModuleSMul U a) (etaleModuleSMul X a)
    (etaleModuleRestriction_map_etaleModuleSMul j a) G

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **`R^q f_!` is linear**: it carries multiplication by a scalar `a` on `G` to multiplication
by `a` on `R^q f_! G`. Through `R^q f_! = R^q f̄_* ∘ j_!`, both extension by zero and the higher
direct images do. -/
theorem lowerShriekHomology_map_etaleModuleSMul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (q : ℕ) (a : A) (G : EtaleModules.{u, 0} A X) :
    (lowerShriekHomology A f j q).map ((etaleModuleSMul X a).app G) =
      (etaleModuleSMul Y a).app ((lowerShriekHomology A f j q).obj G) := by
  let e := lowerShriekHomologyIsoRightDerived A f j q
  have h₃ : (etaleModuleExtensionByZero.{u, 0} A j.immersion ⋙
      (etaleModuleDirectImage.{u, 0} A j.toBase).rightDerived q).map ((etaleModuleSMul X a).app G) =
        (etaleModuleSMul Y a).app ((etaleModuleExtensionByZero.{u, 0} A j.immersion ⋙
          (etaleModuleDirectImage.{u, 0} A j.toBase).rightDerived q).obj G) :=
    (congrArg ((etaleModuleDirectImage.{u, 0} A j.toBase).rightDerived q).map
      (etaleModuleExtensionByZero_map_etaleModuleSMul j.immersion a G)).trans
      (rightDerived_etaleModuleDirectImage_map_etaleModuleSMul j.toBase a q _)
  have h₂ : e.hom.app G ≫
      (etaleModuleSMul Y a).app ((etaleModuleExtensionByZero.{u, 0} A j.immersion ⋙
          (etaleModuleDirectImage.{u, 0} A j.toBase).rightDerived q).obj G) =
      (etaleModuleSMul Y a).app ((lowerShriekHomology A f j q).obj G) ≫ e.hom.app G :=
    (etaleModuleSMul Y a).naturality (e.hom.app G)
  calc (lowerShriekHomology A f j q).map ((etaleModuleSMul X a).app G)
      = e.hom.app G ≫ (etaleModuleExtensionByZero.{u, 0} A j.immersion ⋙
          (etaleModuleDirectImage.{u, 0} A j.toBase).rightDerived q).map
            ((etaleModuleSMul X a).app G) ≫ e.inv.app G := (NatIso.naturality_2 e _).symm
    _ = (etaleModuleSMul Y a).app ((lowerShriekHomology A f j q).obj G) := by
      rw [h₃, ← Category.assoc, h₂, Category.assoc, Iso.hom_inv_id_app]
      exact Category.comp_id _

end SMul

end Stacks.EtaleCohomology

end
