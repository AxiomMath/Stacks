module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Simple modules have finite length

A simple module `M` over a ring `R` has exactly the two submodules `0` and `M`, so it is both
Noetherian and Artinian, hence of finite length (`isFiniteLength_iff_isNoetherian_isArtinian`).

## Main results

* `IsSimpleModule.isFiniteLength`: a simple module has finite length.
-/

@[expose] public section

/-- A simple module has finite length. -/
theorem IsSimpleModule.isFiniteLength (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : IsFiniteLength R M :=
  isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end
