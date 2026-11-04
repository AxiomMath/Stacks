module

public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Transport of the algebraic order of vanishing along a ring isomorphism

`Ring.ord R r` is the length of `R ⧸ (r)`, and a ring isomorphism `e : R ≃+* S` leaves it
unchanged: `Ring.ord R r = Ring.ord S (e r)`.

## Main results

* `Stacks.OrderOfVanishing.ord_eq_of_ringEquiv`: the order of vanishing of an element equals
  that of its image under a ring isomorphism.
-/

@[expose] public section

namespace Stacks.OrderOfVanishing

/-- `Ring.ord` is invariant under a ring isomorphism: the order of vanishing of an element equals
that of its image. -/
theorem ord_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (r : R) : Ring.ord R r = Ring.ord S (e r) := by
  have h : (Ideal.span {e r}).comap (e : R →+* S) = Ideal.span {r} := by
    ext y
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
    refine ⟨fun ⟨c, hc⟩ ↦ ⟨e.symm c, ?_⟩, fun ⟨c, hc⟩ ↦ ⟨e c, by simp [hc]⟩⟩
    simpa using congrArg e.symm hc
  show Module.length R (R ⧸ Ideal.span {r}) = Module.length S (S ⧸ Ideal.span {e r})
  rw [Module.length_quotient, Module.length_quotient, ← h]
  exact Order.coheight_orderIso e.idealComapOrderIso (Ideal.span {e r})

end Stacks.OrderOfVanishing

end
