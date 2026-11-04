module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimit
public import StacksFrontier.RingTheory.LocalCohomology.AdicProjectionInjectivity

/-!
# Part (1) of Stacks 0EFY at `T = {𝔪}` over an `I`-adically complete ring

In Situation [Stacks, Tag 0EFU] with `A` local, `I`-adically complete and `T = {𝔪}`, there is an
integer `m₀` such that the canonical map `Hⁱ_𝔪(M) ⟶ Hⁱ_𝔪(M/IⁿM)` is injective for every `i ≤ s` and
every `n ≥ m₀`, provided the derived `I`-adic completion `RΓ_𝔪(M)^∧` is the derived limit of the
tower `n ↦ RΓ_𝔪(M/IⁿM)` along its canonical projections
`Dualizing.completedLocalCohomologyProjection`. This is part (1) of [Stacks, Tag 0EFY] in that
case.

## Main results

* `Stacks.Algebraization.isIso_homology_completedLocalCohomologyUnit_maximalIdeal` — the derived
  `I`-adic completion unit `RΓ_𝔪(M) ⟶ RΓ_𝔪(M)^∧` is an isomorphism on cohomology in degrees
  `i ≤ s`.
* `exists_forall_injective_homology_localCohomologyAdicQuotientMap_of_eq_closedPoint` — part (1) of
  [Stacks, Tag 0EFY] at `T = {𝔪}` over an `I`-adically complete ring.

## References

* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

/-- The arrow of [Stacks, Tag 0EFL] at `J' = J` is the derived `I`-adic completion unit followed by
the shrinking identification. -/
theorem localCohomologyToCompletedLocalCohomology_eq_unit_comp
    (A : Type u) [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    localCohomologyToCompletedLocalCohomology A I J J hI hJ hJ M hV =
      Dualizing.completedLocalCohomologyUnit A I J hI hJ M ≫
        (completedLocalCohomologyShrinkIso A I J J hI hJ hJ M hV).hom :=
  rfl

section Local

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  (S : BootstrapSituation.{u, u, u})

/-- In the bootstrap situation with `A` local, `I`-adically complete and `T = {𝔪}`, the derived
`I`-adic completion unit `RΓ_𝔪(M) ⟶ RΓ_𝔪(M)^∧` is an isomorphism on cohomology in degrees `i ≤ s`.
-/
public theorem isIso_homology_completedLocalCohomologyUnit_maximalIdeal
    [IsLocalRing S.A] [IsAdicComplete S.I S.A] (hT : S.T = {closedPoint S.A})
    (i : ℤ) (hi : i ≤ S.s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i).map
      (Dualizing.completedLocalCohomologyUnit S.A S.I (maximalIdeal S.A)
        S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
        (ModuleCat.of S.A S.M))) := by
  have h := isIso_homology_localCohomologyToCompletedLocalCohomology_maximalIdeal S hT i hi
  rw [localCohomologyToCompletedLocalCohomology_eq_unit_comp, Functor.map_comp] at h
  exact (isIso_comp_right_iff _ _).mp h

/-- **Part (1) of [Stacks, Tag 0EFY] at `T = {𝔪}` over an `I`-adically complete ring.** In
Situation [Stacks, Tag 0EFU] with `A` local, `I`-adically complete and `T = {𝔪}`, there is an
integer `m₀` such that the canonical map `Hⁱ_𝔪(M) ⟶ Hⁱ_𝔪(M/IⁿM)` is injective for every `i ≤ s` and
every `n ≥ m₀`, provided `hproj`: `RΓ_𝔪(M)^∧` is the derived limit of the tower `n ↦ RΓ_𝔪(M/IⁿM)`
along the canonical projections `Dualizing.completedLocalCohomologyProjection`. -/
public theorem exists_forall_injective_homology_localCohomologyAdicQuotientMap_of_eq_closedPoint
    [IsLocalRing S.A] [IsAdicComplete S.I S.A] (hT : S.T = {closedPoint S.A})
    (hproj : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (Dualizing.adicQuotientLocalCohomologySystem S.A S.I (maximalIdeal S.A)
        (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M))
      (Dualizing.completedLocalCohomology S.A S.I (maximalIdeal S.A)
        S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M))
      (Dualizing.completedLocalCohomologyProjection S.A S.I (maximalIdeal S.A)
        S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
        (ModuleCat.of S.A S.M))) :
    ∃ m₀ : ℕ, ∀ i : ℤ, i ≤ S.s → ∀ n : ℕ, m₀ ≤ n →
      Function.Injective ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i).map
        (Dualizing.localCohomologyAdicQuotientMap S.A S.I (maximalIdeal S.A)
          (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) n)).hom :=
  Stacks.LocalCohomology.exists_forall_injective_homology_localCohomologyAdicQuotientMap
    S.A S.I (ModuleCat.of S.A S.M) S.s _ _ hproj
    (Dualizing.completedLocalCohomologyUnit S.A S.I (maximalIdeal S.A)
      S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M))
    (Dualizing.completedLocalCohomologyUnit_comp_projection S.A S.I (maximalIdeal S.A)
      S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M))
    (isIso_homology_completedLocalCohomologyUnit_maximalIdeal S hT)

end Local

end Stacks.Algebraization

end
