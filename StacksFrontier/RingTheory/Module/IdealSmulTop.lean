module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# An ideal acting on the whole ring

Scaling the top submodule of `R` by an ideal `I` gives back `I`.
-/

@[expose] public section

/-- `I • (⊤ : Submodule R R) = I`: an ideal acting on the whole ring recovers itself. -/
public theorem Ideal.smul_top_eq_self {R : Type*} [CommRing R] (I : Ideal R) :
    I • (⊤ : Submodule R R) = I := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

end
