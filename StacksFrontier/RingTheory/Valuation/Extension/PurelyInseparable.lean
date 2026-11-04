module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring

@[expose] public section

/-!
# Integral closure of a valuation ring in a purely inseparable extension

Let `A` be a valuation ring with fraction field `K` of exponential characteristic `p`, and let
`L/K` be a purely inseparable field extension. The integral closure `B` of `A` in `L` is a
valuation ring with fraction field `L`, and the inclusion `A → B` is an injective local
homomorphism, so that `A ⊆ B` is an extension of valuation rings.

## Main definitions

* `integralClosureValuationSubring`: the integral closure of `A` in `L`, as a valuation subring
  of `L`.

## Main results

* `mem_or_inv_mem_integralClosure`: for every `x : L`, either `x` or `x⁻¹` is integral over `A`.
* `isFractionRing_integralClosure_purelyInseparable`: `L` is the fraction field of
  `integralClosure A L`.
* `isLocalHom_algebraMap_integralClosure`: the inclusion `A → integralClosure A L` is a local
  homomorphism.
* `integralClosure_isValuationRing_of_isPurelyInseparable`: the conjunction of the above.

## Implementation notes

A valuation ring with fraction field `K` is modelled by `A : ValuationSubring K`, and the
characteristic hypothesis by `[ExpChar K p]`. The fraction field of `B` being `L` is stated as
`IsFractionRing (integralClosure A L) L`.
-/

variable {K : Type*} [Field K] (A : ValuationSubring K)
variable {L : Type*} [Field L] [Algebra K L]
variable (p : ℕ)

/-- If `L/K` is purely inseparable, then for every `x : L`, either `x` or `x⁻¹` lies in the
integral closure of `A` in `L`.

Some power `x ^ p ^ n` is the image of an element `k ∈ K`, and either `k ∈ A` or `k⁻¹ ∈ A`;
in the first case `x ^ p ^ n` is integral over `A`, hence so is `x`, and in the second case the
same argument applies to `x⁻¹` (the case `x = 0` being trivial). -/
theorem mem_or_inv_mem_integralClosure [ExpChar K p] [IsPurelyInseparable K L] (x : L) :
    x ∈ integralClosure A L ∨ x⁻¹ ∈ integralClosure A L := by
  obtain ⟨n, k, hk⟩ := IsPurelyInseparable.pow_mem K p x
  have hp : 0 < p ^ n := by have := expChar_pos K p; positivity
  rcases A.mem_or_inv_mem k with hkA | hkA
  · left
    have hbridge : x ^ p ^ n = algebraMap A L (⟨k, hkA⟩ : A) := by
      rw [← hk, IsScalarTower.algebraMap_apply A K L, ValuationSubring.algebraMap_apply]
    exact IsIntegral.of_pow hp (by rw [hbridge]; exact isIntegral_algebraMap)
  · right
    by_cases hx : x = 0
    · simp [hx]
    have hbridge : (x⁻¹) ^ p ^ n = algebraMap A L (⟨k⁻¹, hkA⟩ : A) := by
      rw [IsScalarTower.algebraMap_apply A K L, ValuationSubring.algebraMap_apply]
      simp only [inv_pow, ← hk, map_inv₀]
    exact IsIntegral.of_pow hp (by rw [hbridge]; exact isIntegral_algebraMap)

/-- The integral closure of `A` in a purely inseparable extension `L/K`, as a valuation subring
of `L`. -/
noncomputable def integralClosureValuationSubring [ExpChar K p] [IsPurelyInseparable K L] :
    ValuationSubring L :=
  ValuationSubring.ofSubring (integralClosure A L).toSubring
    (fun x => mem_or_inv_mem_integralClosure A p x)

/-- An element of `L` lies in `integralClosureValuationSubring A p` if and only if it is
integral over `A`. -/
@[simp]
theorem mem_integralClosureValuationSubring [ExpChar K p] [IsPurelyInseparable K L] {x : L} :
    x ∈ integralClosureValuationSubring A p ↔ x ∈ integralClosure A L := Iff.rfl

/-- If `L/K` is purely inseparable, then `L` is the fraction field of the integral closure of
`A` in `L`: every `z : L` is either `z / 1` or `1 / z⁻¹` with numerator and denominator in it,
by `mem_or_inv_mem_integralClosure`. -/
theorem isFractionRing_integralClosure_purelyInseparable [ExpChar K p] [IsPurelyInseparable K L] :
    IsFractionRing (integralClosure A L) L := by
  apply IsFractionRing.of_field
  intro z
  rcases mem_or_inv_mem_integralClosure A p z with hz | hz
  · exact ⟨⟨z, hz⟩, 1, by simp⟩
  · by_cases hz0 : z = 0
    · exact ⟨0, 1, by simp [hz0]⟩
    · exact ⟨1, ⟨z⁻¹, hz⟩, by simp⟩

/-- The inclusion `A → integralClosure A L` is injective, since its composite with
`integralClosure A L → L` is the injective map `A → K → L`. -/
theorem algebraMap_integralClosure_injective :
    Function.Injective (algebraMap A (integralClosure A L)) := by
  refine Function.Injective.of_comp (f := algebraMap (integralClosure A L) L) ?_
  rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A K L]
  exact (algebraMap K L).injective.comp Subtype.val_injective

/-- The inclusion `A → integralClosure A L` is a local homomorphism, being an injective
integral ring map. -/
theorem isLocalHom_algebraMap_integralClosure :
    IsLocalHom (algebraMap A (integralClosure A L)) :=
  RingHom.IsIntegral.isLocalHom (fun x => Algebra.IsIntegral.isIntegral x)
    (algebraMap_integralClosure_injective A)

/-- Let `A` be a valuation ring with fraction field `K` of exponential characteristic `p`, and
let `L/K` be a purely inseparable field extension. Then the integral closure `B` of `A` in `L`
satisfies the valuation-ring criterion, has fraction field `L`, and the inclusion `A → B` is an
injective local homomorphism. -/
@[stacks 0H37]
theorem integralClosure_isValuationRing_of_isPurelyInseparable [ExpChar K p] [IsPurelyInseparable K
  L] :
    -- (1) `B` is a valuation ring: the valuation criterion holds.
    (∀ x : L, x ∈ integralClosure A L ∨ x⁻¹ ∈ integralClosure A L) ∧
    -- (2) `Frac(B) = L`.
    IsFractionRing (integralClosure A L) L ∧
    -- (3) the inclusion `A → B` is injective and a local homomorphism.
    (Function.Injective (algebraMap A (integralClosure A L)) ∧
      IsLocalHom (algebraMap A (integralClosure A L))) :=
  ⟨fun x => mem_or_inv_mem_integralClosure A p x,
    isFractionRing_integralClosure_purelyInseparable A p,
    algebraMap_integralClosure_injective A, isLocalHom_algebraMap_integralClosure A⟩
