module

public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.LocalProperties.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Depth along a flat base change, localized at the contracted prime

Let `R₀ → T` be a flat ring map with `T` local and both rings Noetherian, and let `N` be the base
change of a finite `R₀`-module `M₀` to `T`. Write `𝔭 ⊆ R₀` for the contraction of the maximal
ideal of `T`, so that `R₀_𝔭 → T` is a flat local homomorphism and `N` is the base change of
`(M₀)_𝔭`. Then

`depth_T(N) = depth_{R₀_𝔭}((M₀)_𝔭) + depth_T(T / 𝔭T)`.

## Main results

* `Module.depth_eq_add_depth_quotient_of_isBaseChange`: the formula above, for arbitrary models
  `R₀_𝔭` and `(M₀)_𝔭` of the localizations.

## References

* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Module

variable {R₀ T : Type*} [CommRing R₀] [CommRing T] [IsLocalRing T] [IsNoetherianRing R₀]
  [IsNoetherianRing T] [Algebra R₀ T] [Module.Flat R₀ T]
  {M₀ N : Type*} [AddCommGroup M₀] [Module R₀ M₀] [Module.Finite R₀ M₀]
  [AddCommGroup N] [Module R₀ N] [Module T N] [IsScalarTower R₀ T N]

/-- Depth along a flat base change, with the base localized at the contraction `𝔭` of the
maximal ideal of `T`: `depth_T(N) = depth_{R₀_𝔭}((M₀)_𝔭) + depth_T(T/𝔭T)` for `N` the base
change of a finite `R₀`-module `M₀`. -/
@[sga "2 III 2.11" "special case"]
theorem depth_eq_add_depth_quotient_of_isBaseChange (i : M₀ →ₗ[R₀] N) (hi : IsBaseChange T i)
    (Rp : Type*) [CommRing Rp] [Algebra R₀ Rp]
    [IsLocalization.AtPrime Rp ((maximalIdeal T).comap (algebraMap R₀ T))]
    (Mp : Type*) [AddCommGroup Mp] [Module R₀ Mp] [Module Rp Mp] [IsScalarTower R₀ Rp Mp]
    (j : M₀ →ₗ[R₀] Mp)
    [IsLocalizedModule ((maximalIdeal T).comap (algebraMap R₀ T)).primeCompl j] :
    haveI := IsLocalization.AtPrime.isLocalRing Rp ((maximalIdeal T).comap (algebraMap R₀ T))
    Module.depth T (maximalIdeal T) N =
      Module.depth Rp (maximalIdeal Rp) Mp +
        Module.depth T (maximalIdeal T)
          (T ⧸ (((maximalIdeal T).comap (algebraMap R₀ T)).map (algebraMap R₀ T)) •
            (⊤ : Submodule T T)) := by
  set P := (maximalIdeal T).comap (algebraMap R₀ T) with hP
  have := IsLocalization.AtPrime.isLocalRing Rp P
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap R₀ T y) := fun y =>
    (IsLocalRing.notMem_maximalIdeal).1 y.2
  let : Algebra Rp T := (IsLocalization.lift (M := P.primeCompl) hunit).toAlgebra
  have : IsScalarTower R₀ Rp T := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := P.primeCompl) hunit x).symm
  have hmax : maximalIdeal Rp = P.map (algebraMap R₀ Rp) :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal P Rp).symm
  have : IsLocalHom (algebraMap Rp T) := by
    refine ((IsLocalRing.local_hom_TFAE (algebraMap Rp T)).out 1 4).2 ?_
    rw [hmax, Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  have : IsNoetherianRing Rp := IsLocalization.isNoetherianRing P.primeCompl Rp inferInstance
  have : Module.Flat Rp T := by
    have : IsLocalizedModule P.primeCompl (LinearMap.id : T →ₗ[R₀] T) :=
      isLocalizedModule_id P.primeCompl T Rp
    exact Module.Flat.of_isLocalizedModule Rp P.primeCompl (LinearMap.id : T →ₗ[R₀] T)
  have : Module.Finite Rp Mp := Module.Finite.of_isLocalizedModule P.primeCompl j
  let : Module Rp N := Module.compHom N (algebraMap Rp T)
  have : IsScalarTower Rp T N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R₀ Rp N := IsScalarTower.of_algebraMap_smul fun r n => by
    show algebraMap Rp T (algebraMap R₀ Rp r) • n = r • n
    rw [← IsScalarTower.algebraMap_apply, algebraMap_smul]
  have hunitN : ∀ x : P.primeCompl, IsUnit (algebraMap R₀ (Module.End R₀ N) x) := fun x => by
    rw [Module.End.isUnit_iff]
    have hu := (hunit x).map (algebraMap T (Module.End T N))
    rw [Module.End.isUnit_iff] at hu
    convert hu using 1
    funext n
    show (x : R₀) • n = algebraMap R₀ T x • n
    rw [algebraMap_smul]
  let g : Mp →ₗ[Rp] N := LinearMap.extendScalarsOfIsLocalization P.primeCompl Rp
    (IsLocalizedModule.lift P.primeCompl j i hunitN)
  have hgj : (g.restrictScalars R₀).comp j = i := IsLocalizedModule.lift_comp _ _ _ hunitN
  have hj : IsBaseChange Rp j := IsLocalizedModule.isBaseChange P.primeCompl Rp j
  have hg : IsBaseChange T g := (IsBaseChange.comp_iff hj).1 (by rwa [hgj])
  rw [← Module.depth_eq_depth_of_linearEquiv (maximalIdeal T) hg.equiv,
    depth_tensorProduct_of_flat (R := Rp) (S := T) (M := Mp) (N := T), hmax,
    Ideal.map_map, ← IsScalarTower.algebraMap_eq]

end Module

end
