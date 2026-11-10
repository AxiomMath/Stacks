module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapClosedPointProZero
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalization
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapShrink
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapUniverse
public import StacksFrontier.RingTheory.Dualizing.FiniteDimension
public import StacksFrontier.RingTheory.LocalCohomology.LocalizedIdealPowerTower

/-!
# Pro-vanishing of local cohomology at a point of the locus

Let `S` be a bootstrap situation (`Stacks.Algebraization.BootstrapSituation`) with locus `T`.
Over the local ring `A_𝔮` at a prime `𝔮 ∈ T` the locus becomes the closed point. For every
`𝔮 ∈ T`, every degree `i ≤ s` and every `m`, some transition map

`H^i_{𝔮A_𝔮}((I^kM)_𝔮) ⟶ H^i_{𝔮A_𝔮}((I^mM)_𝔮)`

vanishes.

## Main definitions

* `Stacks.Algebraization.BootstrapSituation.localizeClosedPoint` — the situation over `A_𝔮` with
  locus the closed point.

## Main results

* `Stacks.Algebraization.closedPoint_mem_locus` — for `𝔮 ∈ T` the closed point of `A_𝔮` lies in
  the locus of the localized situation.
* `Stacks.Algebraization.exists_localized_localCohomology_idealPowerTower_map_eq_zero` — the
  per-prime pro-zero assertion at an arbitrary `𝔮 ∈ T`, for the term-by-term localization of the
  ideal-power tower of `M`.
* `Stacks.Algebraization.exists_map_idealPowerTower_eq_zero_of_uniform` — the inverse system
  `{H^i_T(IⁿM)}` is pro-zero at a general specialization-stable `T`, given a per-prime bound that
  is uniform in `𝔮 ∈ T`.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
* [Stacks Project, Tag 0EF9](https://stacks.math.columbia.edu/tag/0EF9)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (S : BootstrapSituation.{u, u, u})

/-- **The closed point of `A_𝔮` lies in the localized locus**, for `𝔮 ∈ T`. -/
theorem closedPoint_mem_locus (q : PrimeSpectrum S.A) (hq : q ∈ S.T) :
    closedPoint (Localization q.asIdeal.primeCompl) ∈ locus S q.asIdeal.primeCompl := by
  change PrimeSpectrum.comap (algebraMap S.A (Localization q.asIdeal.primeCompl))
    (closedPoint (Localization q.asIdeal.primeCompl)) ∈ S.T
  rwa [show PrimeSpectrum.comap (algebraMap S.A (Localization q.asIdeal.primeCompl))
      (closedPoint (Localization q.asIdeal.primeCompl)) = q from
    PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal]

/-- **The bootstrap situation over `A_𝔮` whose locus is the closed point.** For `𝔮 ∈ T` this is
the localization of the situation at `𝔮`, with its locus shrunk to the closed point. -/
def BootstrapSituation.localizeClosedPoint (q : PrimeSpectrum S.A) (hq : q ∈ S.T) :
    BootstrapSituation.{u, u, u} :=
  (S.localize q.asIdeal.primeCompl).shrink
    {closedPoint (Localization q.asIdeal.primeCompl)}
    (Set.singleton_subset_iff.2 (closedPoint_mem_locus S q hq))
    (IsLocalRing.isClosed_singleton_closedPoint
      (Localization q.asIdeal.primeCompl)).stableUnderSpecialization

/-- **The per-prime pro-zero assertion at `𝔮 ∈ T`, over the local ring `A_𝔮`.** For `i ≤ s` and
every `m` some transition map of the system `{H^i_{𝔮A_𝔮}((I_𝔮)ⁿ(M_𝔮))}` vanishes. -/
theorem exists_map_idealPowerTower_eq_zero_atPrime
    (q : PrimeSpectrum S.A) (hq : q ∈ S.T) (i : ℤ) (hi : i ≤ S.s) (m : ℕ) :
    ∃ (k : ℕ) (h : m ≤ k),
      (localCohomologyWithSupportInModuleFunctor.{u, u}
          (Localization q.asIdeal.primeCompl)
          {closedPoint (Localization q.asIdeal.primeCompl)} i).map
        ((idealPowerTower.{u, u}
          (S.I.map (algebraMap S.A (Localization q.asIdeal.primeCompl)))
          (ModuleCat.of (Localization q.asIdeal.primeCompl)
            (LocalizedModule q.asIdeal.primeCompl S.M))).map (homOfLE h).op) = 0 := by
  have : IsLocalRing (BootstrapSituation.localizeClosedPoint S q hq).A :=
    inferInstanceAs (IsLocalRing (Localization q.asIdeal.primeCompl))
  exact exists_map_idealPowerTower_eq_zero_closedPoint
    (BootstrapSituation.localizeClosedPoint S q hq) rfl i hi m

/-- The value of `ModuleCat.localizedModuleFunctor T` at `M`, a `Shrink` of the localized module,
is isomorphic to the localized module `LocalizedModule T M`. -/
def localizedModuleShrinkIso (T : Submonoid S.A) :
    (ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of S.A S.M) ≅
      ModuleCat.of (Localization T) (LocalizedModule T S.M) :=
  (Shrink.linearEquiv (Localization T) (LocalizedModule T S.M)).toModuleIso

/-- **The per-prime pro-zero assertion at an arbitrary `𝔮 ∈ T`.** For every `𝔮 ∈ T`, every
`i ≤ s` and every `m` there is a `k ≥ m` such that the transition map

`H^i_{𝔮A_𝔮}((IᵏM)_𝔮) ⟶ H^i_{𝔮A_𝔮}((IᵐM)_𝔮)`

vanishes. -/
theorem exists_localized_localCohomology_idealPowerTower_map_eq_zero
    (q : PrimeSpectrum S.A) (hq : q ∈ S.T) (i : ℤ) (hi : i ≤ S.s) (m : ℕ) :
    ∃ (k : ℕ) (h : m ≤ k),
      (idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
          ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
          localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) i).map
        (homOfLE h).op = 0 := by
  have : IsNoetherianRing (Localization q.asIdeal.primeCompl) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  obtain ⟨k, h, hk⟩ := exists_map_idealPowerTower_eq_zero_atPrime S q hq i hi m
  refine ⟨k, h, ?_⟩
  rw [localCohomology_localizedIdealPowerTower_map_eq_zero_iff.{u, u}
    q.asIdeal.primeCompl S.I (ModuleCat.of S.A S.M) i h]
  refine (natIso_map_eq_zero_iff
    (Functor.isoWhiskerRight
      (idealPowerTowerIsoOfIso.{u, u}
        (S.I.map (algebraMap S.A (Localization q.asIdeal.primeCompl)))
        (localizedModuleShrinkIso S q.asIdeal.primeCompl))
      (localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) i))
    (homOfLE h).op).2 ?_
  refine (natIso_map_eq_zero_iff
    (localCohomologyWithSupportInModuleFunctorIso (Localization q.asIdeal.primeCompl)
      (maximalIdeal (Localization q.asIdeal.primeCompl)) (IsNoetherian.noetherian _) i)
    ((idealPowerTower.{u, u}
      (S.I.map (algebraMap S.A (Localization q.asIdeal.primeCompl)))
      (ModuleCat.of (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl S.M))).map (homOfLE h).op)).1 ?_
  rwa [show PrimeSpectrum.zeroLocus
      ((maximalIdeal (Localization q.asIdeal.primeCompl) :
        Ideal (Localization q.asIdeal.primeCompl)) :
        Set (Localization q.asIdeal.primeCompl)) =
      {closedPoint (Localization q.asIdeal.primeCompl)} from zeroLocus_maximalIdeal]

/-- **Pro-vanishing at a general specialization-stable `T`, from a uniform per-prime bound.**
Suppose that for every `m` the transition maps `H^i_{𝔮A_𝔮}((IᵏM)_𝔮) ⟶ H^i_{𝔮A_𝔮}((IᵐM)_𝔮)`
vanish for **every** `𝔮 ∈ T` as soon as `k ≥ m'(m)`. Then the inverse system `{H^i_T(IⁿM)}` is
pro-zero. -/
theorem exists_map_idealPowerTower_eq_zero_of_uniform (i : ℕ) (m' : ℕ → ℕ)
    (hm' : ∀ m, m ≤ m' m)
    (huniform : ∀ (m k : ℕ) (hbound : m' m ≤ k), ∀ q ∈ S.T,
      (idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M) ⋙
        ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization q.asIdeal.primeCompl) (i : ℤ)).map
          (homOfLE ((hm' m).trans hbound)).op = 0)
    (m : ℕ) :
    ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, u} S.A S.T (i : ℤ)).map
        ((idealPowerTower.{u, u} S.I (ModuleCat.of S.A S.M)).map (homOfLE h).op) = 0 :=
  exists_map_idealPowerTower_eq_zero_of_local.{u, u} S.ringKrullDim_lt_top S.T
    S.stableUnderSpecialization S.I (ModuleCat.of S.A S.M) i m' hm'
    huniform m

end Stacks.Algebraization

end
