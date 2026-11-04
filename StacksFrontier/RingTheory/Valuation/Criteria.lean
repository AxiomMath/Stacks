module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuationSubring

import StacksCore.Tactic.StacksAttribute

/-!
# Criteria for a domain to be a valuation ring

Stacks 00IB (for `x` in the fraction field of a valuation ring, `x` or `x⁻¹` is integral),
Stacks 052K (a subring of a field closed under this dichotomy is a valuation ring with that
field as its fraction field) and Stacks 090Q (a domain is a valuation ring iff it is local
with every finitely generated ideal principal) are all Mathlib's; the `add_to_stacks` lines
below record them.

## Main results

* `valuationRing_isIntegrallyClosed` (Stacks 00IC): a valuation ring is a normal domain.
* `valuation_ring_noetherian_iff_dvr_or_field` (Stacks 00II): a valuation ring is Noetherian
  iff it is a discrete valuation ring or a field.
-/

@[expose] public section

-- The former @[stacks 00IB] theorem is the forward direction of the Mathlib equivalence.
add_to_stacks 00IB ValuationRing.iff_isInteger_or_isInteger

-- The former @[stacks 052K] theorem is Mathlib's `ValuationSubring` — a subring of a field
-- with `x ∈ A ∨ x⁻¹ ∈ A` — together with its two instances.
add_to_stacks 052K "the hypothesis, as a structure" ValuationSubring
add_to_ega "II 7.1.1" ValuationSubring
add_to_stacks 052K "it is a valuation ring" ValuationSubring.instValuationRingSubtypeMem
add_to_stacks 052K "with fraction field `K`" ValuationSubring.instIsFractionRingSubtypeMem

-- The former @[stacks 090Q] theorem is the Mathlib equivalence, with `IsBezout` unfolded by
-- `IsBezout.isPrincipal_of_FG` and `IsBezout.mk`.
add_to_stacks 090Q ValuationRing.iff_local_bezout_domain
add_to_stacks 090Q "every finitely generated ideal is principal" IsBezout.isPrincipal_of_FG

/-- (Stacks Tag 00IC) A valuation ring (which is a domain) is a normal domain,
i.e. it is integrally closed in its field of fractions. -/
@[ega "II 7.1.1" "more general"]
theorem valuationRing_isIntegrallyClosed
    (A : Type*) [CommRing A] [IsDomain A] [ValuationRing A] :
    IsIntegrallyClosed A :=
  inferInstance

/-- A valuation ring is Noetherian if and only if it is a discrete valuation ring
or a field. -/
@[stacks 00II, ega "II 7.1.6" "valuation ring ⇒ DVR"]
theorem valuation_ring_noetherian_iff_dvr_or_field
    (A : Type*) [CommRing A] [IsDomain A] [ValuationRing A] :
    IsNoetherianRing A ↔ IsDiscreteValuationRing A ∨ IsField A := by
  refine ⟨fun _ ↦ ?_, ?_⟩
  · by_cases hF : IsField A
    · exact .inr hF
    have : IsPrincipalIdealRing A := IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
    exact .inl ⟨fun heq ↦ hF (IsLocalRing.isField_iff_maximalIdeal_eq.mpr heq)⟩
  · rintro (_ | hF)
    · infer_instance
    let := hF.toField
    infer_instance

end
