module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import StacksFrontier.RingTheory.RegularLocalRing.SystemOfParameters

/-!
# Replacing one member of a regular system of parameters

A regular system of parameters `y 0, …, y (n-1)` of a local ring `R` is by definition a family
whose cotangent images are a basis of `𝔪/𝔪²`, so it carries a basis
(`IsRegularSystemOfParameters.basis`). If `z ∈ 𝔪` has a nonzero coefficient at `y i` in that
basis, then `y` with its `i`-th member replaced by `z` is again a regular system of parameters.

## Main definitions

* `IsRegularSystemOfParameters.basis`: the basis of `𝔪/𝔪²` given by the cotangent images of a
  regular system of parameters.

## Main results

* `IsRegularSystemOfParameters.update`: replacing the `i`-th member of a regular system of
  parameters by an element of `𝔪` with nonzero `i`-th coefficient gives a regular system of
  parameters.

## Implementation notes

Independence is Mathlib's `LinearIndependent.update`, whose hypothesis asks for a non-zero-divisor
`r` and a `Finsupp` of coefficients with a non-zero-divisor entry at `i`; over the residue field
`r = 1` works and "non-zero-divisor" is "nonzero". Spanning is then automatic from
`LinearIndependent.span_eq_top_of_card_eq_finrank'`, since the cotangent space is
finite-dimensional of dimension `n`. The primed form is used so that `n = 0` is allowed.
-/

@[expose] public section

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}

namespace IsRegularSystemOfParameters

/-- The basis of the cotangent space `𝔪/𝔪²` given by the cotangent images of a regular system of
parameters. -/
noncomputable def basis {y : Fin n → maximalIdeal R} (hy : IsRegularSystemOfParameters y) :
    Module.Basis (Fin n) (ResidueField R) (CotangentSpace R) :=
  Module.Basis.mk hy.linearIndependent hy.span_eq_top.ge

/-- The basis of a regular system of parameters `y` is the family of cotangent images of `y`. -/
theorem coe_basis {y : Fin n → maximalIdeal R} (hy : IsRegularSystemOfParameters y) :
    (hy.basis : Fin n → CotangentSpace R) =
      fun i => (maximalIdeal R).toCotangent (y i) :=
  Module.Basis.coe_mk _ _

/-- The `i`-th vector of the basis of a regular system of parameters `y` is the cotangent image of
`y i`. -/
@[simp]
theorem basis_apply {y : Fin n → maximalIdeal R} (hy : IsRegularSystemOfParameters y)
    (i : Fin n) : hy.basis i = (maximalIdeal R).toCotangent (y i) :=
  congrFun hy.coe_basis i

/-- If a local ring has a regular system of parameters, its cotangent space is finite-dimensional
over the residue field. -/
theorem finiteDimensional_cotangentSpace {y : Fin n → maximalIdeal R}
    (hy : IsRegularSystemOfParameters y) :
    FiniteDimensional (ResidueField R) (CotangentSpace R) :=
  Module.Finite.of_basis hy.basis

/-- If a local ring has a regular system of parameters of length `n`, its cotangent space has
dimension `n` over the residue field. -/
theorem finrank_cotangentSpace {y : Fin n → maximalIdeal R}
    (hy : IsRegularSystemOfParameters y) :
    Module.finrank (ResidueField R) (CotangentSpace R) = n := by
  rw [Module.finrank_eq_card_basis hy.basis, Fintype.card_fin]

/-- **One-member replacement.** If `y` is a regular system of parameters of a local ring and
`z ∈ 𝔪` has a nonzero coefficient at `y i` in the cotangent basis of `y`, then `y` with its
`i`-th member replaced by `z` is again a regular system of parameters. -/
theorem update {y : Fin n → maximalIdeal R} (hy : IsRegularSystemOfParameters y) (i : Fin n)
    (z : maximalIdeal R)
    (hz : hy.basis.repr ((maximalIdeal R).toCotangent z) i ≠ 0) :
    IsRegularSystemOfParameters (Function.update y i z) := by
  have hfd := hy.finiteDimensional_cotangentSpace
  have hupd : (fun j => (maximalIdeal R).toCotangent ((Function.update y i z) j)) =
      Function.update (fun j => (maximalIdeal R).toCotangent (y j)) i
        ((maximalIdeal R).toCotangent z) :=
    funext fun j =>
      Function.apply_update (fun _ (x : maximalIdeal R) => (maximalIdeal R).toCotangent x) y i z j
  have hind : LinearIndependent (ResidueField R)
      (fun j => (maximalIdeal R).toCotangent ((Function.update y i z) j)) := by
    rw [hupd]
    refine hy.linearIndependent.update i _
      ⟨1, one_mem _, hy.basis.repr ((maximalIdeal R).toCotangent z),
        mem_nonZeroDivisors_iff_ne_zero.mpr hz, ?_⟩
    rw [one_smul, ← hy.coe_basis]
    exact (hy.basis.linearCombination_repr _).symm
  refine ⟨hind, ?_⟩
  refine hind.span_eq_top_of_card_eq_finrank' ?_
  rw [Fintype.card_fin, hy.finrank_cotangentSpace]

end IsRegularSystemOfParameters

end
