module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.Functoriality
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
public import StacksFrontier.Algebra.Module.IPowerTorsion

/-!
# A surjection with power torsion kernel becomes an isomorphism away from the torsion

Let `R` be a ring, `𝔞 ⊆ R` an ideal and `U ⊆ Spec R` an open consisting of primes not containing
`𝔞`. A surjection `φ : M → N` of `R`-modules whose kernel is `𝔞`-power torsion induces an
isomorphism `M̃|_U ≅ Ñ|_U`: on the stalk at a prime `𝔭 ∈ U` the map is the localization of `φ`,
which is surjective, and injective because an element of an `𝔞`-power torsion module is killed by
a power of an element of `𝔞` not in `𝔭`.

## Main results

* `Stacks.LefschetzCone.isIso_restrict_tilde_map_of_isIPowerTorsion_ker`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.LefschetzCone

/-- **A surjection with `𝔞`-power torsion kernel is an isomorphism over the primes off `V(𝔞)`.** -/
public theorem isIso_restrict_tilde_map_of_isIPowerTorsion_ker {R : CommRingCat.{u}}
    {M N : ModuleCat.{u} R} (φ : M ⟶ N) (𝔞 : Ideal R) (U : (Spec R).Opens)
    (hU : ∀ y : U.toScheme, ¬ 𝔞 ≤ (U.ι.base y).asIdeal)
    (hsurj : Function.Surjective φ.hom) (hker : IsIPowerTorsion R (LinearMap.ker φ.hom) 𝔞) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (tilde.map φ)) := by
  refine ExtensionByZeroModules.isIso_of_stalk_isIso U.toScheme.ringCatSheaf _ fun y => ?_
  set x : PrimeSpectrum.Top R := U.ι.base y with hx
  have hdirect : IsIso ((Scheme.Modules.toPresheaf (Spec R) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} x).map (tilde.map φ)) := by
    have hinj : Function.Injective (IsLocalizedModule.map x.asIdeal.primeCompl
        (tilde.toStalk M x).hom (tilde.toStalk N x).hom φ.hom) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro z hz
      rw [LinearMap.mem_ker] at hz
      obtain ⟨⟨m, s⟩, rfl⟩ :=
        IsLocalizedModule.mk'_surjective x.asIdeal.primeCompl (tilde.toStalk M x).hom z
      simp only [Function.uncurry_apply_pair] at hz ⊢
      rw [IsLocalizedModule.map_mk'] at hz
      obtain ⟨t, ht⟩ := (IsLocalizedModule.mk'_eq_zero' _ _).1 hz
      have htm : (t : R) • m ∈ LinearMap.ker φ.hom := by
        rw [LinearMap.mem_ker, map_smul]
        exact ht
      obtain ⟨n, -, hn⟩ := hker ⟨_, htm⟩
      obtain ⟨a, ha𝔞, hap⟩ := Set.not_subset.1 (hU y)
      have hzero : (a ^ n * t) • m = 0 := by
        have := hn (a ^ n) (Ideal.pow_mem_pow ha𝔞 n)
        rw [mul_smul]
        exact congrArg Subtype.val this
      have hmem : a ^ n * (t : R) ∈ x.asIdeal.primeCompl :=
        x.asIdeal.primeCompl.mul_mem (x.asIdeal.primeCompl.pow_mem hap n) t.2
      rw [Submodule.mem_bot]
      exact (IsLocalizedModule.mk'_eq_zero' _ _).2 ⟨⟨_, hmem⟩, hzero⟩
    have hsurj' : Function.Surjective (IsLocalizedModule.map x.asIdeal.primeCompl
        (tilde.toStalk M x).hom (tilde.toStalk N x).hom φ.hom) := by
      intro z
      obtain ⟨⟨n, s⟩, rfl⟩ :=
        IsLocalizedModule.mk'_surjective x.asIdeal.primeCompl (tilde.toStalk N x).hom z
      obtain ⟨m, rfl⟩ := hsurj n
      exact ⟨IsLocalizedModule.mk' (tilde.toStalk M x).hom m s,
        IsLocalizedModule.map_mk' _ _ _ _ _ _⟩
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab => hinj ?_, fun z => ?_⟩
    · exact (tilde.toStalk_map φ x a).symm.trans (hab.trans (tilde.toStalk_map φ x b))
    · obtain ⟨m, hm⟩ := hsurj' z
      exact ⟨m, (tilde.toStalk_map φ x m).trans hm⟩
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι y) (tilde.map φ)).mpr
    hdirect

end Stacks.LefschetzCone

end
