module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Existence
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.AdicCompletion.DvrValuedPoints
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
public import Mathlib.RingTheory.Localization.Cardinality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A complete discrete valuation ring through a non-closed prime of a Noetherian local ring

Let `R` be a Noetherian local ring and `𝔭 ⊂ R` a prime ideal other than the maximal ideal.
There is a complete discrete valuation ring `D` with a local homomorphism `R ⟶ D` whose kernel
is `𝔭`: take a discrete valuation ring of the fraction field of `R/𝔭` dominating `R/𝔭`
(Stacks 00PH) and complete it (Stacks 0AP1). Geometrically, `Spec D ⟶ Spec R` sends the generic
point to `𝔭` and the closed point to the closed point. The cardinality of `D` is bounded by
`#R ^ ℵ₀`, which is what keeps `Spec D` in a big site containing `Spec R`.

## Main results

* `IsLocalRing.exists_isAdicComplete_isDiscreteValuationRing_ker_eq`.

## References

* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks Project, Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1)
-/

@[expose] public section

open IsLocalRing Cardinal

universe u

namespace IsLocalRing

/-- **A complete discrete valuation ring through a non-closed prime.** For a Noetherian local
ring `R` and a prime `𝔭 ≠ 𝔪`, there is a complete discrete valuation ring `D` of cardinality at
most `max ℵ₀ #R ^ ℵ₀` with a local homomorphism `R ⟶ D` of kernel `𝔭`. -/
@[ega "IV 15.7.7" "Dominating complete DVR"]
theorem exists_isAdicComplete_isDiscreteValuationRing_ker_eq {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ maximalIdeal R) :
    ∃ (D : Type u) (_ : CommRing D) (_ : IsDomain D) (_ : IsDiscreteValuationRing D)
      (ρ : R →+* D), IsNoetherianCompleteLocalRing D ∧ IsLocalHom ρ ∧ RingHom.ker ρ = 𝔭 ∧
        #D ≤ max ℵ₀ #R ^ ℵ₀ := by
  let R₀ := R ⧸ 𝔭
  have hloc : IsLocalRing R₀ := IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔭)
    Ideal.Quotient.mk_surjective
  have hnf : ¬ IsField R₀ := fun hf =>
    h𝔭 (IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField 𝔭 hf))
  let K₀ := FractionRing R₀
  obtain ⟨A₀, hA₀, hA₀K, hA₀loc⟩ :=
    exists_isDiscreteValuationRing_isFractionRing_of_not_isField (R := R₀) K₀ (L := K₀) hnf
  let D := AdicCompletion (maximalIdeal A₀) A₀
  obtain ⟨hDdom, hDdvr⟩ :=
    (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := A₀)).mp ⟨inferInstance, hA₀⟩
  let ρ : R →+* D := (algebraMap A₀ D).comp ((algebraMap R₀ A₀).comp (Ideal.Quotient.mk 𝔭))
  have hinj₁ : Function.Injective (algebraMap R₀ A₀) := fun a b hab =>
    IsFractionRing.injective R₀ K₀ (congrArg (fun x : A₀ => (x : K₀)) hab)
  have hinj₂ : Function.Injective (algebraMap A₀ D) := AdicCompletion.of_injective _ _
  have hker : RingHom.ker ρ = 𝔭 := by
    ext r
    rw [RingHom.mem_ker]
    change algebraMap A₀ D (algebraMap R₀ A₀ (Ideal.Quotient.mk 𝔭 r)) = 0 ↔ r ∈ 𝔭
    rw [map_eq_zero_iff _ hinj₂, map_eq_zero_iff _ hinj₁, Ideal.Quotient.eq_zero_iff_mem]
  have hlocρ : IsLocalHom ρ := by
    have : IsLocalHom (Ideal.Quotient.mk 𝔭) := .of_surjective _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap A₀ D) := inferInstance
    exact RingHom.isLocalHom_comp _ _
  have hcomplete : IsNoetherianCompleteLocalRing D :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hcard : #D ≤ max ℵ₀ #R ^ ℵ₀ :=
    calc #D ≤ #A₀ ^ ℵ₀ := AdicCompletion.mk_le_pow_aleph0 _
      _ ≤ #K₀ ^ ℵ₀ := power_le_power_right (mk_le_of_injective Subtype.val_injective)
      _ = #R₀ ^ ℵ₀ := by rw [mk_fractionRing]
      _ ≤ #R ^ ℵ₀ := power_le_power_right (mk_le_of_surjective Ideal.Quotient.mk_surjective)
      _ ≤ max ℵ₀ #R ^ ℵ₀ := power_le_power_right (le_max_right _ _)
  exact ⟨D, inferInstance, hDdom, hDdvr, ρ, hcomplete, hlocρ, hker, hcard⟩

end IsLocalRing

end
