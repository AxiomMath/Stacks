module

public import Mathlib.Algebra.Algebra.Basic

/-!
## Supplements to `Mathlib/Algebra/Algebra/Basic.lean`

Additional lemmas about the canonical algebra map `R → Module.End R N` sending a scalar to
the endomorphism it induces.
-/

@[expose] public section

universe u v

/-- If `b` acts invertibly on a module and `a ∣ b`, then `a` acts invertibly as well. -/
theorem Module.isUnit_algebraMap_end_of_dvd {R : Type u} [CommSemiring R] {N : Type v}
    [AddCommMonoid N] [Module R N] {a b : R} (h : a ∣ b)
    (hb : IsUnit (algebraMap R (Module.End R N) b)) :
    IsUnit (algebraMap R (Module.End R N) a) := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul] at hb
  exact (((Commute.all a c).map (algebraMap R (Module.End R N))).isUnit_mul_iff.mp hb).1
