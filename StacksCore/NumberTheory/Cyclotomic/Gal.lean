module

public import Mathlib.NumberTheory.Cyclotomic.Gal
import StacksCore.FieldTheory.Galois.Basic

/-! # Cyclotomic polynomials -/

@[expose] public section

open Nat IntermediateField

/-- **Stacks 0EXN**.
For a cyclotomic extension `L = K(ζ_n)` of `K`, the degree `[L : K]` divides Euler's totient
`φ(n)`. This follows from the injection of `Gal(L/K)` into `(ℤ/nℤ)ˣ`. -/
@[stacks 0EXN]
theorem IsCyclotomicExtension.finrank_dvd_totient
    (K L : Type*) (n : ℕ) [Field K] [Field L] [Algebra K L] [IsCyclotomicExtension {n} K L] :
    Module.finrank K L ∣ φ n := by
  obtain rfl | hn0 := eq_or_ne n 0
  · have h := IsCyclotomicExtension.isCyclotomicExtension_zero_iff.mp ‹_›
    rw [Module.finrank_of_bijective_algebraMap ⟨RingHom.injective _, h⟩]
    exact one_dvd _
  obtain ⟨μ, hμ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n}) K L (by simp) hn0
  have := NeZero.mk hn0
  have := IsCyclotomicExtension.finite_of_singleton n K L
  have := IsCyclotomicExtension.isGalois {n} K L
  simpa [IsGalois.fintypeCard_aut_eq_finrank K L, ZMod.card_units_eq_totient]
    using Subgroup.card_dvd_of_injective _ <| IsPrimitiveRoot.autToPow_injective K hμ
