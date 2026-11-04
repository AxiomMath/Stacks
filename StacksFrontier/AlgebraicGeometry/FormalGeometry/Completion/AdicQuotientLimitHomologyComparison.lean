module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientDerivedLimit
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientLimitAffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AffineEdgeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.CohomologyAffineAdicComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology
public import StacksCore.Tactic.StacksAttribute

/-!
# Part (2) of the theorem on formal functions on the affine sections of the limit sheaf

Let `X` be a locally Noetherian scheme, `ℐ ⊂ 𝒪_X` a quasi-coherent sheaf of ideals and `K` a
pseudo-coherent object of `D(𝒪_X)`. Part (2) of [Stacks, Tag 0A0K] asserts the equality of sheaves

`H^q(K^∧) = lim H^q(K)/ℐⁿH^q(K)`.

Over an affine open `U`, the comparison map

`lim H^q(U, K)/ℐ(U)ⁿH^q(U, K) ⟶ H^q(U, K^∧)`

is the unique `Γ(X, U)`-linear extension of `H^q(RΓ(U, η_K))` over the adic completion, and it is
bijective. This file identifies its source with the sections over `U` of the sheaf
`lim H^q(K)/ℐⁿH^q(K)`, using two isomorphisms over an affine open:

* `H^q(U, K) = Γ(U, H^q(K))`, the hypercohomology edge isomorphism
  `Stacks.Algebraization.homologyIso_derivedSections_of_isAffineOpen` ([Stacks, Tag 0BKT]);
* `Γ(U, lim H^q(K)/ℐⁿH^q(K)) = lim Γ(U, H^q(K))/ℐ(U)ⁿΓ(U, H^q(K))` for the coherent module
  `H^q(K)`, `Stacks.Algebraization.adicQuotientLimitSectionsEquiv`.

## Main definitions

* `homologyCoherentModule`: the cohomology sheaf `H^q(K)` of a pseudo-coherent object on a
  locally Noetherian scheme, as a coherent module.
* `adicCompletionHomologyLimitSectionsEquiv`: the isomorphism
  `lim H^q(U, K)/ℐ(U)ⁿH^q(U, K) ≅ Γ(U, lim H^q(K)/ℐⁿH^q(K))` over an affine open `U`.

## Main results

* `existsUnique_bijective_adicQuotientLimitSections_homology_derivedCompletion`: over every
  affine open `U` there is exactly one `Γ(X, U)`-linear map
  `c : Γ(U, lim H^q(K)/ℐⁿH^q(K)) ⟶ H^q(U, K^∧)` whose composite with the canonical map from
  `H^q(U, K)` is `H^q(RΓ(U, η_K))`, and it is bijective.
* `isDerivedLimit_single_limit_powerQuotients_homology`: part (4) of [Stacks, Tag 0A0K] at the
  coherent module `H^q(K)`.
* `isZero_cohomology_limit_powerQuotients_homology_of_isAffineOpen`: part (5) of
  [Stacks, Tag 0A0K] at the coherent module `H^q(K)`.

## Implementation notes

The sheaf-level statement would further require `Γ(U, H^q(K^∧)) = H^q(U, K^∧)` over an affine
open, which does not follow from quasi-coherence: the cohomology sheaves of a derived completion
need not be quasi-coherent. On `X = Spec ℤ` with `ℐ = (p)` and `K = 𝒪_X` the sheaf `lim 𝒪/pⁿ` has
sections `ℤ_p` over every `D(f)` with `p ∤ f` and `0` over `D(p)`, whereas quasi-coherence would
force `ℚ_p` over `D(p)`.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0A0L](https://stacks.math.columbia.edu/tag/0A0L)
* [Stacks Project, Tag 0BKT](https://stacks.math.columbia.edu/tag/0BKT)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.HypercohomologyEdge
open Stacks.SheafOfModules (opensRingedSite)

universe u

namespace Stacks.Algebraization

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (𝓘 : X.IdealSheafData)
  (K : DerivedCategory X.Modules) (U : X.affineOpens)

/-! ### The cohomology sheaf as a coherent module -/

/-- The cohomology sheaf `H^q(K)` of a pseudo-coherent object `K` on a locally Noetherian scheme,
as a coherent module. -/
def homologyCoherentModule (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (q : ℤ) :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf where
  obj := (DerivedCategory.homologyFunctor X.Modules q).obj K
  property := by
    obtain ⟨P, hP, e⟩ := hK
    exact AlgebraicGeometry.isCoherent_homology_of_isPseudoCoherentFrom X K q
      (AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X K ⟨P, hP, e⟩)
      ⟨P, hP q, e⟩ q le_rfl

/-- The underlying module of `homologyCoherentModule K hK q` is the cohomology sheaf `H^q(K)`. -/
@[simp]
theorem homologyCoherentModule_obj
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (q : ℤ) :
    (homologyCoherentModule K hK q).obj = (DerivedCategory.homologyFunctor X.Modules q).obj K :=
  rfl

/-! ### The affine sections of the inverse limit sheaf -/

/-- For `K` pseudo-coherent on a locally Noetherian `X` and `U` an affine open, the isomorphism

`lim H^q(U, K)/ℐ(U)ⁿH^q(U, K) ≅ Γ(U, lim H^q(K)/ℐⁿH^q(K))`

between the adic completion of the hypercohomology module and the sections over `U` of the
inverse limit of the adic quotient tower of the cohomology sheaf. -/
def adicCompletionHomologyLimitSectionsEquiv
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (q : ℤ) :
    AdicCompletion (𝓘.ideal U)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).obj
          ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)) ≃ₗ[Γ(X, U.1)]
      Γ((show X.Modules from
          limit (C := X.Modules) (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)),
        U.1) :=
  ((AdicCompletion.congr (𝓘.ideal U)
        (homologyIso_derivedSections_of_isAffineOpen X K
          (by
            obtain ⟨P, hP, e⟩ := hK
            exact AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X K
              ⟨P, hP, e⟩) U q).toLinearEquiv).restrictScalars Γ(X, U.1)).trans
    (adicQuotientLimitSectionsEquiv X 𝓘 (homologyCoherentModule K hK q) U)

/-! ### Part (2) on the affine sections of the limit sheaf -/

/-- Part (2) of [Stacks, Tag 0A0K] on the sections over an affine open `U`. With `A = Γ(X, U)`,
`M = H^q(U, K)`, `T = H^q(U, K^∧)` and `a = H^q(RΓ(U, η_K))`, there is exactly one `A`-linear map

`c : Γ(U, lim H^q(K)/ℐⁿH^q(K)) ⟶ T`

whose composite with the canonical map `M ⟶ Γ(U, lim H^q(K)/ℐⁿH^q(K))` is `a`, and it is
bijective. -/
theorem existsUnique_bijective_adicQuotientLimitSections_homology_derivedCompletion
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (q : ℤ) :
    let Hq := fun (L : DerivedCategory X.Modules) ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).obj
        ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj L)
    let Kc := (AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
      (idealSheafSiteSubmodule 𝓘)).obj K
    let Lim := Γ((show X.Modules from
        limit (C := X.Modules) (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)), U.1)
    let a : Hq K →ₗ[Γ(X, U.1)] Hq Kc :=
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).map
      ((derivedSections (structureSheafRing X.toRingedSpace) U.1).map
        ((AlgebraicGeometry.RingedSite.derivedCompletionUnit (opensRingedSite X.sheaf)
          (idealSheafSiteSubmodule 𝓘)).app K))).hom
    ∃ c : Lim →ₗ[Γ(X, U.1)] Hq Kc,
      (∀ m, c (adicCompletionHomologyLimitSectionsEquiv 𝓘 K U hK q
        (AdicCompletion.of (𝓘.ideal U) (Hq K) m)) = a m) ∧ Function.Bijective c ∧
        ∀ c' : Lim →ₗ[Γ(X, U.1)] Hq Kc,
          (∀ m, c' (adicCompletionHomologyLimitSectionsEquiv 𝓘 K U hK q
            (AdicCompletion.of (𝓘.ideal U) (Hq K) m)) = a m) → c' = c := by
  intro Hq Kc Lim a
  obtain ⟨c, hcof, hcbij, hcuniq⟩ :=
    existsUnique_bijective_adicComparison_homology_derivedSections 𝓘 K U hK q
  refine ⟨c ∘ₗ ((adicCompletionHomologyLimitSectionsEquiv 𝓘 K U hK q).symm :
      Lim →ₗ[Γ(X, U.1)] AdicCompletion (𝓘.ideal U) (Hq K)), fun m => ?_, ?_, fun c' hc' => ?_⟩
  · simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using hcof m
  · exact hcbij.comp (adicCompletionHomologyLimitSectionsEquiv 𝓘 K U hK q).symm.bijective
  · have : c' ∘ₗ ((adicCompletionHomologyLimitSectionsEquiv 𝓘 K U hK q) :
        AdicCompletion (𝓘.ideal U) (Hq K) →ₗ[Γ(X, U.1)] Lim) = c := by
      refine hcuniq _ fun m => ?_
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using hc' m
    refine LinearMap.ext fun x => ?_
    have hx := LinearMap.congr_fun this
      ((adicCompletionHomologyLimitSectionsEquiv 𝓘 K U hK q).symm x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      using hx

/-! ### Parts (4) and (5) at the cohomology sheaves -/

/-- Part (4) of [Stacks, Tag 0A0K] at the cohomology sheaf of a pseudo-coherent object: the
ordinary inverse limit of the adic quotient tower of `H^q(K)`, placed in degree zero, is a derived
inverse limit of that tower. -/
theorem isDerivedLimit_single_limit_powerQuotients_homology
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (q : ℤ) :
    let S := (powerQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj
      (isQuasicoherent_of_isCoherent _)).system
    ∃ h : HasProduct (fun n : ℕ =>
        (S ⋙ DerivedCategory.singleFunctor X.Modules 0).obj ⟨n⟩),
      @CategoryTheory.Pretriangulated.IsDerivedLimit (DerivedCategory X.Modules) _ _ _ _ _ _
        (S ⋙ DerivedCategory.singleFunctor X.Modules 0) h
        ((DerivedCategory.singleFunctor X.Modules 0).obj (limit S)) :=
  have : (homologyCoherentModule K hK q).obj.IsCoherent :=
    (homologyCoherentModule K hK q).property
  isDerivedLimit_single_limit_powerQuotients 𝓘 (homologyCoherentModule K hK q).obj

/-- Part (5) of [Stacks, Tag 0A0K] at the cohomology sheaf of a pseudo-coherent object: over an
affine open the inverse limit `lim H^q(K)/ℐⁿH^q(K)` has no cohomology in positive degree. -/
theorem isZero_cohomology_limit_powerQuotients_homology_of_isAffineOpen
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (q : ℤ) (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf U.1 p
      (show X.Modules from
        limit (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj))) :=
  have : (homologyCoherentModule K hK q).obj.IsCoherent :=
    (homologyCoherentModule K hK q).property
  isZero_cohomology_limit_powerQuotients_of_isAffineOpen 𝓘
    (homologyCoherentModule K hK q).obj U p hp

end Stacks.Algebraization

end
