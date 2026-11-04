module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions

/-!
# Cohomology along a morphism whose higher direct images vanish

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and `F` an `𝒪_X`-module with
`R^q f_* F = 0` for `q > 0`.  Then `H^n(X, F) ≅ H^n(Y, f_* F)` in every degree, as modules over
`Γ(Y, 𝒪_Y)`, by the collapse of the Leray spectral sequence ([Stacks, Tag 0733] part (1)).

## Main definitions

* `AlgebraicGeometry.Space.cohomologyIsoOfIsZeroHigherDirectImages`: the comparison.
* `AlgebraicGeometry.Space.cohomologyIsoOfIsFinite`: the same along a finite morphism and a
  quasi-coherent module.

## References

* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- For `f : X ⟶ Y` and an `𝒪_X`-module `F` with `R^q f_* F = 0` for `q > 0`,
`H^n(X, F) ≅ H^n(Y, f_* F)` as `Γ(Y, 𝒪_Y)`-modules, the left side a module through the ring map
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`. -/
def cohomologyIsoOfIsZeroHigherDirectImages (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (h : have := hasInjectiveResolutions_modules B S hS X.1 X.2
      ∀ q : ℕ, 0 < q → IsZero (((modulePushforward B S hS f).rightDerived q).obj F)) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
    (globalSectionsRestrictScalars B S hS f).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived n).obj F) ≅
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived n).obj
        ((modulePushforward B S hS f).obj F) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS Y.1 Y.2
  ((derivedGlobalSectionsPushforwardIso B S hS f n).app F).symm ≪≫
    Stacks.RightDerivedComp.objIsoOfAcyclicImage _ _ h
      (acyclicPushforwardOfInjective B S hS f) n

/-- For a finite morphism `f : X ⟶ Y` and a quasi-coherent `𝒪_X`-module `F`,
`H^n(X, F) ≅ H^n(Y, f_* F)` over `Γ(Y, 𝒪_Y)`. -/
def cohomologyIsoOfIsFinite (f : X ⟶ Y) (hf : IsFinite B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
    (globalSectionsRestrictScalars B S hS f).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived n).obj F) ≅
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived n).obj
        ((modulePushforward B S hS f).obj F) :=
  cohomologyIsoOfIsZeroHigherDirectImages B S hS f F
    (fun q hq => isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite B S hS f
      (IsFinite.isAffineHom hf) F hF q hq) n

end AlgebraicGeometry.Space

end
