module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedProduct
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ScalarRestriction

/-! # Divided powers and maps out of an even variable algebra

A ring homomorphism out of the even variable algebra of Tag 09PI which preserves homogeneous
degrees and is compatible with divided powers on the coefficients is automatically compatible with
the divided powers of the whole extension. Unlike the odd case, where the divided powers of
`x + yT` have a closed form valid in any graded divided power algebra, there is no such formula
here, and the statement is proved by the graph argument: the graph of the homomorphism is a
subring of the product, the extension is a single finite variable stage over its coefficients, and
finite variable stages are stable under divided powers.

## Main results

* `DividedPowers.TateResolution.evenVariableDividedPowerStructure_dpow_monomial_one` — the divided
  powers of the adjoined variable are its divided power monomials.
* `DividedPowers.TateResolution.evenVariableAlgebra_ringHom_dpow` — a degree-preserving ring
  homomorphism out of an even variable algebra which is divided-power compatible on the
  coefficients is divided-power compatible.

## Implementation notes

The graph argument is run over `ℤ` rather than over the ambient coefficient ring. This is not a
weakening: the gradings and divided powers do not involve the coefficients (see
`StacksFrontier.RingTheory.DividedPowers.TateResolution.ScalarRestriction`), while the argument needs
the coefficient inclusion to be an algebra homomorphism, which over `ℤ` is automatic and over `R`
is false for the abstractly-supplied algebra structure on a subring of a graded divided power
algebra.

## References

* [Stacks Project, Tag 09PI](https://stacks.math.columbia.edu/tag/09PI)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

universe u v z

open EvenVariableAlgebra

section

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

/-- The divided powers of the adjoined even variable are its divided power monomials. -/
public theorem evenVariableDividedPowerStructure_dpow_monomial_one
    (γ : DividedPowerStructure 𝒜) (d : ℕ) [Fact (Even d)] (hd : 0 < d) (n : ℕ) :
    (evenVariableDividedPowerStructure d hd γ).dpow n (monomial 1 (1 : A)) =
      monomial n (1 : A) := by
  simpa [dividedPowerMonomialCoefficient, Nat.div_self (Nat.factorial_pos n)] using
    dpow_monomial_one d hd γ n 1 (by omega)

end

section

attribute [local instance 2000] Ring.toIntAlgebra

variable {R : Type u} {B : Type v} {D : Type z} [CommRing R] [Ring B] [Algebra R B]
  [Ring D] [Algebra R D]
  (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
  (β : DividedPowerStructure ℬ)
  (𝒟 : ℕ → Submodule R D) [GradedAlgebra 𝒟] [IsStrictlyGradedComm 𝒟]
  (δ : DividedPowerStructure 𝒟)

/-- A positive even coefficient of an even variable algebra is positive even in the coefficient
algebra. -/
private theorem mem_positiveEvenPart_of_coeffEmbedding_mem
    (β' : DividedPowerStructure ℬ) (d : ℕ) (hd : 0 < d)
    (heven : Even d) {b : B}
    (hb : coeffEmbedding b ∈ positiveEvenPart (EvenVariableAlgebra.grade ℬ d)) :
    b ∈ positiveEvenPart ℬ := by
  obtain ⟨r, hr, -⟩ := existsUnique_evenVariableAlgebra_ringHom ℬ ℬ β' (RingHom.id B)
    (fun _ _ hb => hb) d hd heven 0 (Submodule.zero_mem _)
  have h := ringHom_mem_positiveEvenPart (EvenVariableAlgebra.grade ℬ d) ℬ r hr.2.2 hb
  rwa [hr.1 b, RingHom.id_apply] at h

/-- A degree-preserving ring homomorphism out of an even variable algebra which restricts to a
divided-power compatible map on the coefficients is itself compatible with divided powers. -/
@[stacks 09PI "mapping property"]
public theorem evenVariableAlgebra_ringHom_dpow
    (h : B →+* D)
    (hdpow : ∀ (n : ℕ) (b : B), b ∈ positiveEvenPart ℬ → δ.dpow n (h b) = h (β.dpow n b))
    (d : ℕ) [Fact (Even d)] (hd : 0 < d) (t : D) (ht : t ∈ 𝒟 d)
    (g : EvenVariableAlgebra B →+* D)
    (hg1 : ∀ b : B, g (coeffEmbedding b) = h b)
    (hg2 : ∀ n : ℕ, g (monomial n (1 : B)) = δ.dpow n t)
    (hg3 : ∀ (m : ℕ) (x : EvenVariableAlgebra B),
      x ∈ EvenVariableAlgebra.grade ℬ d m → g x ∈ 𝒟 m)
    (n : ℕ) (x : EvenVariableAlgebra B)
    (hx : x ∈ positiveEvenPart (EvenVariableAlgebra.grade ℬ d)) :
    δ.dpow n (g x) = g ((evenVariableDividedPowerStructure d hd β).dpow n x) := by
  classical
  have heven : Even d := Fact.out
  have htpos : t ∈ positiveEvenPart 𝒟 := by
    obtain ⟨c, hc⟩ : ∃ c, d = 2 * c := by obtain ⟨c, hc⟩ := heven; exact ⟨c, by omega⟩
    refine Submodule.mem_iSup_of_mem (c - 1) ?_
    rw [show 2 * (c - 1 + 1) = d by omega]
    exact ht
  set γC := evenVariableDividedPowerStructure d hd β with hγC
  let ιZ : B →ₐ[ℤ] EvenVariableAlgebra B :=
    { coeffEmbedding with
      commutes' := fun r => by
        simp only [algebraMap_int_eq, eq_intCast]
        exact map_intCast coeffEmbedding r }
  let T : Unit → EvenVariableAlgebra B := fun _ => monomial 1 1
  have hδT : ∀ m : ℕ, γC.dpow m (T ()) = monomial m (1 : B) := fun m =>
    evenVariableDividedPowerStructure_dpow_monomial_one ℬ β d hd m
  have hmon : ∀ (m : ℕ) (a : B), monomial m a = ιZ a * γC.dpow m (T ()) := by
    intro m a
    rw [hδT m]
    show monomial m a = monomial 0 a * monomial m 1
    rw [monomial_mul_monomial]
    simp
  have hfinite : ∀ y : EvenVariableAlgebra B,
      y ∈ finiteVariableStage (γC.restrictScalars ℤ) ιZ T {()} := by
    intro y
    induction y using EvenVariableAlgebra.induction_on with
    | zero => exact Subring.zero_mem _
    | add m a y hy =>
        refine Subring.add_mem _ ?_ hy
        rw [hmon m a]
        exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨a, rfl⟩))
          (Subring.subset_closure (Or.inr ⟨(), by simp, Or.inr ⟨m, rfl⟩⟩))
  have hrefl : ∀ b : B, coeffEmbedding b ∈
      positiveEvenPart (EvenVariableAlgebra.grade ℬ d) → b ∈ positiveEvenPart ℬ := fun b hb =>
    mem_positiveEvenPart_of_coeffEmbedding_mem ℬ β d hd heven hb
  have hcoeffdpow : ∀ (m : ℕ) (b : B),
      coeffEmbedding b ∈ positiveEvenPart (EvenVariableAlgebra.grade ℬ d) →
      γC.dpow m (coeffEmbedding b) = coeffEmbedding (β.dpow m b) := fun m b hb =>
    dpow_coeffEmbedding d hd β m (hrefl b hb)
  have key := ringHom_dpow_of_finiteVariableStage
    (restrictGrade ℤ ℬ) (restrictGrade ℤ (EvenVariableAlgebra.grade ℬ d))
    (restrictGrade ℤ 𝒟) (γC.restrictScalars ℤ) (δ.restrictScalars ℤ) ιZ T {()} d
    (fun m a ha => (coeffEmbedding_mem_grade_iff ℬ d m a).2 ha)
    (fun _ => (mem_restrictGrade ℤ _ _ _).2
      (by simpa only [one_mul] using monomial_one_mem_grade ℬ d 1))
    (fun m a ha => ⟨β.dpow m a, (hcoeffdpow m a
      ((mem_positiveEvenPart_restrictGrade ℤ _ _).1 ha)).symm⟩)
    g (fun m y hy => hg3 m y hy) (fun r => by simp)
    (fun m a ha => by
      have hb := (mem_positiveEvenPart_restrictGrade ℤ _ _).1 ha
      show δ.dpow m (g (coeffEmbedding a)) = g (γC.dpow m (coeffEmbedding a))
      rw [hcoeffdpow m a hb, hg1, hg1]
      exact hdpow m a (hrefl a hb))
    (fun m _ _ => by
      show δ.dpow m (g (monomial 1 1)) = g (γC.dpow m (monomial 1 1))
      rw [hδT m, hg2, hg2, δ.dpow_one htpos])
    (hfinite x) ((mem_positiveEvenPart_restrictGrade ℤ _ _).2 hx) n
  exact key

end

end DividedPowers.TateResolution

end
