module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Maximal-ideal-adic completeness transports along a ring isomorphism

A ring isomorphism of local rings carries the maximal ideal to the maximal ideal, so it
carries completeness for the maximal-ideal-adic topology to completeness for the
maximal-ideal-adic topology.
-/

@[expose] public section

open IsLocalRing

/-- Adic completeness for the maximal ideal transports along a ring isomorphism of local
rings. -/
theorem isAdicComplete_maximalIdeal_of_ringEquiv {S T : Type*}
    [CommRing S] [CommRing T] [IsLocalRing S] [IsLocalRing T] (e : S ≃+* T)
    [IsAdicComplete (maximalIdeal S) S] : IsAdicComplete (maximalIdeal T) T := by
  have hmap : Ideal.map e (maximalIdeal S) = maximalIdeal T :=
    eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
  rw [← hmap]
  exact (IsAdicComplete.congr_ringEquiv (maximalIdeal S) e).2 inferInstance
