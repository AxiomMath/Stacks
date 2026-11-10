module

public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayDegreeOneFibre
public import StacksFrontier.RingTheory.Depth.FlatBaseChangeLocalization
public import Mathlib.RingTheory.Finiteness.Descent

/-!
# Depth on the punctured cone over a standard open

Let `S = ⨁_{d ≥ 0} S_d` be a Noetherian graded ring, `M` a finite graded `S`-module, `f ∈ S_1` and
`𝔭` a prime of `S` with `f ∉ 𝔭`, lying over the prime `𝔮` of `S₍f₎`. Then `M_𝔭` is the base
change of the degree-zero module `M₍f₎` along the flat map `S₍f₎ → S_𝔭`, and [Stacks, Tag 0338]
gives

`depth(M_𝔭) = depth((M₍f₎)_𝔮) + depth(S_𝔭 / 𝔮 S_𝔭)`.

## Main results

* `Stacks.GradedLocalization.isBaseChange_degreeZero_atPrime`: `M_𝔭` is the base change of `M₍f₎`.
* `Stacks.GradedLocalization.depth_localizedModule_eq_add`: the depth formula above.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
-/

@[expose] public noncomputable section

open IsLocalRing HomogeneousLocalization Stacks.GradedLaurent TensorProduct

attribute [local instance] instVAddNatIntGradedLocalizedModule

namespace Stacks.GradedLocalization

variable {S : Type*} {M : Type*} {σ : Type*} {τ : Type*}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨] {f : S}

attribute [local instance] awayModule

variable (p : Ideal S) [p.IsPrime] (hp : f ∉ p)

/-- The `S₍f₎`-module structure on `M_𝔭`, through `S₍f₎ → S_𝔭`. -/
abbrev atPrimeAwayModule : Module (Away 𝒜 f) (LocalizedModule p.primeCompl M) :=
  Module.compHom _ (awayDegreeZeroToAtPrime 𝒜 p hp)

/-- **`M_𝔭` is the base change of the degree-zero module `M₍f₎` along `S₍f₎ → S_𝔭`**, for `f` of
degree one not in `𝔭`. -/
theorem isBaseChange_degreeZero_atPrime (hf : f ∈ 𝒜 1) :
    letI := (awayDegreeZeroToAtPrime 𝒜 p hp).toAlgebra
    letI := atPrimeAwayModule (M := M) 𝒜 p hp
    haveI : IsScalarTower (Away 𝒜 f) (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∃ i : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f →ₗ[Away 𝒜 f] LocalizedModule p.primeCompl M,
      IsBaseChange (Localization.AtPrime p) i := by
  set B := Away 𝒜 f
  set Af := Localization.Away f
  set T := Localization.AtPrime p
  set Mf := LocalizedModule (Submonoid.powers f) M
  set Mp := LocalizedModule p.primeCompl M
  let : Algebra Af T := (awayToAtPrime p hp).toAlgebra
  have : IsScalarTower S Af T :=
    IsScalarTower.of_algebraMap_eq fun x => (awayToAtPrime_algebraMap p hp x).symm
  let : Algebra B T := (awayDegreeZeroToAtPrime 𝒜 p hp).toAlgebra
  have : IsScalarTower B Af T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module Af Mp := Module.compHom Mp (algebraMap Af T)
  let : Module B Mp := atPrimeAwayModule (M := M) 𝒜 p hp
  have : IsScalarTower Af T Mp := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower B T Mp := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower B Af Mp := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower S Af Mp := IsScalarTower.of_algebraMap_smul fun r m => by
    change algebraMap Af T (algebraMap S Af r) • m = r • m
    rw [← IsScalarTower.algebraMap_apply, algebraMap_smul]
  have hle : Submonoid.powers f ≤ p.primeCompl := (Submonoid.powers_le (P := p.primeCompl)).2 hp
  let h₀ : Mf →ₗ[S] Mp := IsLocalizedModule.liftOfLE (Submonoid.powers f) p.primeCompl hle
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap p.primeCompl M)
  let h : Mf →ₗ[Af] Mp := LinearMap.extendScalarsOfIsLocalization (Submonoid.powers f) Af h₀
  have hh₀ : (h.restrictScalars S).comp (LocalizedModule.mkLinearMap (Submonoid.powers f) M) =
      LocalizedModule.mkLinearMap p.primeCompl M :=
    IsLocalizedModule.liftOfLE_comp (Submonoid.powers f) p.primeCompl hle _ _
  have hbase : IsBaseChange Af (LocalizedModule.mkLinearMap (Submonoid.powers f) M) :=
    IsLocalizedModule.isBaseChange (Submonoid.powers f) Af _
  have hh : IsBaseChange T h := (IsBaseChange.comp_iff hbase).1 (by
    rw [hh₀]
    exact IsLocalizedModule.isBaseChange p.primeCompl T _)
  exact ⟨(h.restrictScalars B).comp (GradedModuleDegreeZeroLocalization 𝒜 𝒨 f).subtype,
    (isBaseChange_degreeZero 𝒜 𝒨 hf (M := M)).comp hh⟩

/-- **The depth formula on the punctured cone.** For `f ∈ S_1` and a prime `𝔭 ∌ f` lying over the
prime `𝔮` of `S₍f₎`,

`depth(M_𝔭) = depth((M₍f₎)_𝔮) + depth(S_𝔭 / 𝔮 S_𝔭)`. -/
theorem depth_localizedModule_eq_add [IsNoetherianRing S] [Module.Finite S M] (hf : f ∈ 𝒜 1) :
    Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl M) =
      Module.depth (Localization.AtPrime (baseIdeal 𝒜 p hp))
          (maximalIdeal (Localization.AtPrime (baseIdeal 𝒜 p hp)))
          (LocalizedModule (baseIdeal 𝒜 p hp).primeCompl
            (GradedModuleDegreeZeroLocalization 𝒜 𝒨 f)) +
        Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p ⧸ (baseIdeal 𝒜 p hp).map (awayDegreeZeroToAtPrime 𝒜 p hp) •
            (⊤ : Submodule (Localization.AtPrime p) (Localization.AtPrime p))) := by
  set B := Away 𝒜 f
  set Af := Localization.Away f
  set T := Localization.AtPrime p
  set M0 := GradedModuleDegreeZeroLocalization 𝒜 𝒨 f
  let : Algebra Af T := (awayToAtPrime p hp).toAlgebra
  have : IsScalarTower S Af T :=
    IsScalarTower.of_algebraMap_eq fun x => (awayToAtPrime_algebraMap p hp x).symm
  let : Algebra B T := (awayDegreeZeroToAtPrime 𝒜 p hp).toAlgebra
  have : IsScalarTower B Af T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := atPrimeAwayModule (M := M) 𝒜 p hp
  have : IsScalarTower B T (LocalizedModule p.primeCompl M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨i, hi⟩ := isBaseChange_degreeZero_atPrime 𝒜 𝒨 p hp hf (M := M)
  have : IsNoetherianRing B := isNoetherianRing_away 𝒜 hf
  have : IsNoetherianRing T := IsLocalization.isNoetherianRing p.primeCompl T inferInstance
  have : Module.Free B Af := Module.Free.of_basis (awayZpowBasis 𝒜 hf)
  have : Module.Flat B Af := inferInstance
  have : Module.Flat Af T :=
    have := isLocalization_awayToAtPrime p hp
    IsLocalization.flat T (p.primeCompl.map (algebraMap S Af))
  have : Module.Flat B T := Module.Flat.trans B Af T
  have : Module.Finite B M0 := by
    rcases subsingleton_or_nontrivial Af with hst | hnt
    · have : Subsingleton (LocalizedModule (Submonoid.powers f) M) :=
        Module.subsingleton Af _
      have : Subsingleton M0 := inferInstance
      exact Module.Finite.of_finite
    · have : Module.Finite Af (LocalizedModule (Submonoid.powers f) M) :=
        Module.Finite.of_isLocalizedModule (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      have : Module.Finite Af (Af ⊗[B] M0) :=
        Module.Finite.equiv (isBaseChange_degreeZero 𝒜 𝒨 hf (M := M)).equiv.symm
      exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat Af
  exact Module.depth_eq_add_depth_quotient_of_isBaseChange i hi
    (Localization.AtPrime (baseIdeal 𝒜 p hp))
    (LocalizedModule (baseIdeal 𝒜 p hp).primeCompl M0)
    (LocalizedModule.mkLinearMap (baseIdeal 𝒜 p hp).primeCompl M0)

end Stacks.GradedLocalization

end
