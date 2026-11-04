module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleModuleInjectives
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictPushforward
public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction

/-!
# The derived degree-zero square of `ε_a`: the composite half

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site, with underlying morphism `r`, and
let `𝓕` be a quasi-coherent `𝒪_X`-module. This file constructs an isomorphism

`R ⁿ (ε_* ∘ (ε_a)_*)(𝓕ᵃ) ≅ R ⁿ r_* 𝓕`,

where `ε_* = AlgebraicGeometry.SmallEtale.restrictModule` is restriction to the small Zariski
site, taken here inside the derived functor.

## Main definitions

* `AlgebraicGeometry.SmallEtale.preservesInjectiveObjects_restrictModule`: `ε_*` preserves
  injective objects.
* `Stacks.RightDerivedSpelling.rightDerivedIsoOfNatIsoOfAdditive`:
  `CategoryTheory.Functor.rightDerivedIsoOfNatIso` with the additivity of its two functors as
  explicit arguments.

## Main results

* `AlgebraicGeometry.SmallEtale.rightDerivedCompRestrictModuleIso`:
  `R ⁿ (ε_{X*} ⋙ r_*)(𝓕ᵃ) ≅ R ⁿ r_* 𝓕`.
* `AlgebraicGeometry.SmallEtale.rightDerivedPushforwardRestrictModuleIso`: the same read on the
  other composite of the degree-zero square, `R ⁿ (ε_{Y*} ∘ (ε_a)_*)(𝓕ᵃ) ≅ R ⁿ r_* 𝓕`.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace Stacks.RightDerivedSpelling

variable {A E : Type*} [Category* A] [Category* E] [Abelian A] [Abelian E]
  [HasInjectiveResolutions A]

/-- `CategoryTheory.Functor.rightDerivedIsoOfNatIso` with the additivity of its two functors
taken as explicit arguments rather than found by instance search. -/
public def rightDerivedIsoOfNatIsoOfAdditive {F G : A ⥤ E} (hF : F.Additive) (hG : G.Additive)
    (e : F ≅ G) (n : ℕ) :
    F.rightDerived n ≅ G.rightDerived n :=
  letI := hF
  letI := hG
  Functor.rightDerivedIsoOfNatIso e n

end Stacks.RightDerivedSpelling

namespace AlgebraicGeometry.SmallEtale

section Injectives

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The associated-module functor `ε^*` is additive. -/
public instance additive_associatedModule : (associatedModule B S hS).Additive :=
  (associatedModuleAdjunction B S hS).left_adjoint_additive

/-- `ε_*` is left exact. -/
public instance preservesFiniteLimits_restrictModule :
    PreservesFiniteLimits (restrictModule B S hS) :=
  have := (associatedModuleAdjunction B S hS).rightAdjoint_preservesLimits
  inferInstance

/-- `ε_*` preserves injective objects. -/
public instance preservesInjectiveObjects_restrictModule :
    (restrictModule B S hS).PreservesInjectiveObjects :=
  preservesInjectiveObjects_of_isExact _ (associatedModule B S hS)
    (associatedModuleAdjunction B S hS)
    ⟨preservesFiniteLimits_associatedModule B S hS, inferInstance⟩

end Injectives

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The direct image along `ε_a` is additive. -/
public instance additive_pushforward_smallEtaleStructureMapRing :
    (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).Additive :=
  Stacks.SheafOfModules.pushforward_additive _

/-- The direct image along `r` is additive. -/
public instance additive_pushforward_toRingCatSheafHom :
    (SheafOfModules.pushforward.{u} (schemeHom B a).toRingCatSheafHom).Additive :=
  Stacks.SheafOfModules.pushforward_additive _

/-- The right-hand composite of the degree-zero square is additive. -/
public instance additive_restrictModule_comp_pushforward :
    (restrictModule B X.obj X.property ⋙
      SheafOfModules.pushforward.{u} (schemeHom B a).toRingCatSheafHom).Additive where
  map_add := by intros; rfl

/-- The left-hand composite of the degree-zero square is additive. -/
public instance additive_pushforward_comp_restrictModule :
    (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
      restrictModule B Y.obj Y.property).Additive where
  map_add := by intros; rfl

/-- The derived functor of `ε_{X*}` followed by `r_*` at an associated module: for `𝓕` a
quasi-coherent `𝒪_X`-module,

`R ⁿ (ε_{X*} ⋙ r_*)(𝓕ᵃ) ≅ R ⁿ r_* 𝓕`. -/
public def rightDerivedCompRestrictModuleIso (n : ℕ) (𝓕 : (X.obj).Modules)
    (h𝓕 : SheafOfModules.IsQuasicoherent (R := (X.obj).ringCatSheaf) 𝓕) :
    (((restrictModule B X.obj X.property ⋙
        Scheme.Modules.pushforward (schemeHom B a)).rightDerived n).obj
          ((associatedModule B X.obj X.property).obj 𝓕)) ≅
      ((Scheme.Modules.pushforward (schemeHom B a)).rightDerived n).obj 𝓕 :=
  Stacks.RightDerivedComp.objIso (restrictModule B X.obj X.property)
      (injectiveResolution ((associatedModule B X.obj X.property).obj 𝓕))
      (acyclic_restrictModule B X.obj X.property _
        (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B X.obj X.property 𝓕 h𝓕))
      (Scheme.Modules.pushforward (schemeHom B a)) n ≪≫
    ((Scheme.Modules.pushforward (schemeHom B a)).rightDerived n).mapIso
      (@asIso _ _ _ _ _ (unitIsoOnQuasicoherent B X.obj X.property ⟨𝓕, h𝓕⟩)).symm

/-- The same identification read on the other composite of the degree-zero square, with the
restriction to the small Zariski site inside the derived functor:

`R ⁿ (ε_{Y*} ∘ (ε_a)_*)(𝓕ᵃ) ≅ R ⁿ r_* 𝓕`. -/
public def rightDerivedPushforwardRestrictModuleIso (n : ℕ) (𝓕 : (X.obj).Modules)
    (h𝓕 : SheafOfModules.IsQuasicoherent (R := (X.obj).ringCatSheaf) 𝓕) :
    (((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
        restrictModule B Y.obj Y.property).rightDerived n).obj
          ((associatedModule B X.obj X.property).obj 𝓕)) ≅
      ((Scheme.Modules.pushforward (schemeHom B a)).rightDerived n).obj 𝓕 :=
  ((Stacks.RightDerivedSpelling.rightDerivedIsoOfNatIsoOfAdditive ⟨by intros; rfl⟩
      ⟨by intros; rfl⟩ (restrictModulePushforwardIso B a) n).app
      ((associatedModule B X.obj X.property).obj 𝓕)) ≪≫
    rightDerivedCompRestrictModuleIso B a n 𝓕 h𝓕

end AlgebraicGeometry.SmallEtale

end
