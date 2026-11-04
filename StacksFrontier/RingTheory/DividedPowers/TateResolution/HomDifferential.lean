module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TwistedDerivation

/-! # A homomorphism out of a set-variable extension commutes with the differentials

Let `C` be the graded divided power algebra obtained from `A` by adjoining a set of variables of
a single positive degree, as recorded by
`DividedPowers.TateResolution.IsSetVariableExtension`, and let `G : C → D` be a homomorphism of
graded divided power algebras into another differential graded algebra with divided powers. This
file proves that `G` commutes with the two differentials as soon as it does on the coefficients
and on the adjoined variables.

This is the differential half of the stepwise mapping property. The mapping property
`DividedPowers.TateResolution.IsSetVariableExtension.existsUnique_ringHom` produces a ring
homomorphism out of the extension from its restriction to the coefficients and a homogeneous value
for each variable, and it says nothing about differentials, because
`DividedPowers.TateResolution.GradedDPHom` carries none. Tate's lifting argument, however, builds
a map of *differential* graded algebras stage by stage, choosing at each stage a value for the new
variable whose boundary is prescribed; what makes that work is exactly the statement below, that
having chosen such values the resulting map commutes with the differentials everywhere.

The proof is the twisted-derivation uniqueness argument of
`DividedPowers.TateResolution.eq_zero_of_twisted_graded_leibniz`, applied to the difference
`x ↦ G (d_C x) - d_D (G x)`. That difference is additive, kills degree zero because both
differentials do, and obeys the signed Leibniz rule along `G` because both differentials do and `G`
preserves degrees; so it vanishes identically once it vanishes on the coefficients, the variables
and the divided powers of the variables. The last of these is not an extra hypothesis: the divided
powers of a variable are handled by the compatibility of the divided powers with the differential
on both sides, which turns `d (γₙ x)` into `d x · γₙ₋₁ x`.

## Main results

* `DividedPowers.TateResolution.IsSetVariableExtension.algHom_comm_differential` — a
  degree-preserving, divided-power-preserving algebra homomorphism out of a set-variable divided
  power extension commutes with the differentials as soon as it does on the coefficients and on
  the variables.

## References

* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
* [Stacks Project, Tag 09PJ](https://stacks.math.columbia.edu/tag/09PJ)
* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w y z

section CommDifferential

variable {R : Type u} {A : Type v} {C : Type z} {D : Type y} {J : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C] [Ring D] [Algebra R D]
  {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  {γ : DividedPowerStructure Aᵢ}
  {Cᵢ : ℕ → Submodule R C} [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
  {δ : DividedPowerStructure Cᵢ}
  {Dᵢ : ℕ → Submodule R D} [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
  {ε : DividedPowerStructure Dᵢ}
  {ι : A →ₐ[R] C} {T : J → C} {deg : ℕ} {hdeg : 0 < deg}

/-- **A homomorphism out of a set-variable divided power extension commutes with the
differentials as soon as it does on the coefficients and on the variables.**

`G` is asked to be an `R`-algebra homomorphism preserving homogeneous degrees and divided powers —
that is, the underlying data of a `DividedPowers.TateResolution.GradedDPHom` — between two
differential graded algebras whose divided powers are compatible with their differentials. Under
those hypotheses the two maps `G ∘ d_C` and `d_D ∘ G` agree on all of `C` once they agree on the
image of the coefficient algebra and on each adjoined variable.

This is the inductive step of Tate's construction of a map of differential graded divided power
algebras out of a tower: at each stage one chooses, for each new variable, a value of the right
degree whose boundary is the image of the cycle that the variable kills, which is precisely the
hypothesis `hgen`. -/
public theorem IsSetVariableExtension.algHom_comm_differential
    (hC : IsSetVariableExtension Aᵢ γ Cᵢ δ ι T deg hdeg)
    {dC : C →ₗ[R] C} {dD : D →ₗ[R] D}
    (hdgaC : IsDifferentialGradedAlgebra Cᵢ dC)
    (hdgaD : IsDifferentialGradedAlgebra Dᵢ dD)
    (hcompC : IsCompatibleWithDifferential δ dC)
    (hcompD : IsCompatibleWithDifferential ε dD)
    (G : C →ₐ[R] D)
    (hgrade : ∀ (m : ℕ) (x : C), x ∈ Cᵢ m → G x ∈ Dᵢ m)
    (hdpow : ∀ (n : ℕ) (x : C), x ∈ positiveEvenPart Cᵢ → ε.dpow n (G x) = G (δ.dpow n x))
    (hcoeff : ∀ a : A, G (dC (ι a)) = dD (G (ι a)))
    (hgen : ∀ j : J, G (dC (T j)) = dD (G (T j)))
    (x : C) : G (dC x) = dD (G x) := by
  classical
  set E : C →+ D :=
    { toFun := fun z => G (dC z) - dD (G z)
      map_zero' := by simp
      map_add' := by intro z w; simp only [map_add]; abel } with hE
  have hEapply : ∀ z : C, E z = G (dC z) - dD (G z) := fun _ => rfl
  have hzero : ∀ z : C, z ∈ Cᵢ 0 → E z = 0 := by
    intro z hz
    rw [hEapply, hdgaC.d_grade_zero hz, map_zero,
      hdgaD.d_grade_zero (hgrade 0 z hz), sub_zero]
  have hleib : ∀ (i k : ℕ) (z w : C), z ∈ Cᵢ i → w ∈ Cᵢ k →
      E (z * w) = E z * G.toRingHom w + (-1 : D) ^ i * (G.toRingHom z * E w) := by
    intro i k z w hz hw
    have hGz : G z ∈ Dᵢ i := hgrade i z hz
    have hGw : G w ∈ Dᵢ k := hgrade k w hw
    simp only [hEapply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [hdgaC.leibniz hz hw, show G (z * w) = G z * G w from map_mul G z w,
      hdgaD.leibniz hGz hGw, map_add, map_smul, map_mul, map_mul,
      neg_one_pow_smul (R := R), neg_one_pow_smul (R := R)]
    simp only [sub_mul, mul_sub]
    abel
  have hcoeff' : ∀ a : A, E (ι a) = 0 := by
    intro a
    rw [hEapply, hcoeff a, sub_self]
  have hgen' : ∀ j : J, E (T j) = 0 := by
    intro j
    rw [hEapply, hgen j, sub_self]
  have hdp : ∀ (j : J) (n : ℕ), E (δ.dpow n (T j)) = 0 := by
    intro j n
    by_cases hTpos : T j ∈ positiveEvenPart Cᵢ
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [δ.dpow_zero hTpos]
        exact hzero 1 (SetLike.one_mem_graded Cᵢ)
      · have hn' : n ≠ 0 := hn.ne'
        have hGTpos : G (T j) ∈ positiveEvenPart Dᵢ :=
          algHom_mem_positiveEvenPart Cᵢ Dᵢ G hgrade hTpos
        rw [hEapply, hcompC.d_dpow hn' hTpos, map_mul, hgen j,
          ← hdpow (n - 1) (T j) hTpos, ← hdpow n (T j) hTpos,
          hcompD.d_dpow hn' hGTpos, sub_self]
    · rw [δ.dpow_null hTpos]
      exact hzero 0 (Submodule.zero_mem _)
  exact sub_eq_zero.1 (eq_zero_of_twisted_graded_leibniz hC G.toRingHom E hzero hleib
    hcoeff' hgen' hdp x)

end CommDifferential

end DividedPowers.TateResolution

end
