module

public import StacksFrontier.RingTheory.Smoothing.ApproximationHenselianGRing

/-!
# Sections of finitely generated subalgebras of the completion of a henselian G-ring

Let `Λ` be a Noetherian henselian local G-ring with completion `Λ^∧`. Every homomorphism
`ι : A ⟶ Λ^∧` from a finite type `Λ`-algebra `A` admits a `Λ`-algebra homomorphism `σ : A ⟶ Λ`
congruent to `ι` modulo `𝔪 Λ^∧`. This is the form in which the approximation property of
[Stacks, Tag 07QY] is used at the end of the proof of [Stacks, Tag 0E7C]: "we can apply the
approximation property for G-rings to find a map `A → Λ` which induces the same map `A → κ` as we
obtain from `A → Λ^∧`."

## Main results

* `AlgebraicGeometry.C1590Private.exists_approximationSection`: the statement above.

## References

* [Stacks Project, Tag 07QY](https://stacks.math.columbia.edu/tag/07QY)
* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace AlgebraicGeometry.C1590Private

/-- **An approximate section over a henselian G-ring** ([Stacks, Tag 07QY]). Let `Λ` be a
Noetherian henselian local G-ring and `ι : A ⟶ Λ^∧` a homomorphism from a finite type
`Λ`-algebra to the completion. There is a `Λ`-algebra homomorphism `σ : A ⟶ Λ` with
`ι(a) ≡ σ(a)` modulo `𝔪 Λ^∧` for every `a ∈ A`. -/
theorem exists_approximationSection {Λ : Type u} [CommRing Λ] [HenselianLocalRing Λ]
    (hG : IsGRing Λ) {A : Type*} [CommRing A] [Algebra Λ A] [Algebra.FiniteType Λ A]
    (ι : A →ₐ[Λ] AdicCompletion (maximalIdeal Λ) Λ) :
    ∃ σ : A →ₐ[Λ] Λ, ∀ a : A, ι a - algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) (σ a) ∈
      (maximalIdeal Λ).map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)) := by
  have : IsNoetherianRing Λ := hG.1
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹_›
  let gens : Fin n → AdicCompletion (maximalIdeal Λ) Λ := fun i => ι (φ (MvPolynomial.X i))
  have hgens : ∀ p, MvPolynomial.aeval gens p = ι (φ p) := fun p => by
    have h : ι.comp φ = MvPolynomial.aeval gens := MvPolynomial.algHom_ext fun i => by
      simp [gens]
    rw [← h, AlgHom.comp_apply]
  -- the relations, a finite set
  obtain ⟨t, ht⟩ := (RingHom.ker φ.toRingHom).fg_of_isNoetherianRing
  let f : Fin t.card → MvPolynomial (Fin n) Λ := fun j => (t.equivFin.symm j : _)
  have hf : ∀ j, MvPolynomial.aeval gens (f j) = 0 := fun j => by
    have hmem : f j ∈ RingHom.ker φ.toRingHom := by
      rw [← ht]
      exact Ideal.subset_span (t.equivFin.symm j).2
    rw [hgens, show φ (f j) = 0 from hmem, map_zero]
  -- the approximate solution
  obtain ⟨b, hb, hsol⟩ := Stacks.Smoothing.exists_approximate_solution_of_henselian_isGRing hG f
    gens hf 1
  let ψ : MvPolynomial (Fin n) Λ →ₐ[Λ] Λ := MvPolynomial.aeval b
  refine ⟨AlgHom.liftOfSurjective φ hφ ψ ?_, fun a => ?_⟩
  · rw [← ht, Ideal.span_le]
    intro p hp
    have h := hsol (t.equivFin ⟨p, hp⟩)
    simp only [f, Equiv.symm_apply_apply] at h
    exact h
  obtain ⟨p, rfl⟩ := hφ a
  rw [AlgHom.liftOfSurjective_apply, ← hgens]
  have e : algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) (ψ p) =
      MvPolynomial.aeval (fun i => algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) (b i)) p :=
    MvPolynomial.comp_aeval_apply b (Algebra.ofId Λ _) p
  rw [e]
  -- the congruence, through the quotient by `𝔪 Λ^∧`
  refine Ideal.Quotient.eq.1 ?_
  have key : (Ideal.Quotient.mkₐ Λ ((maximalIdeal Λ).map
      (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)))).comp (MvPolynomial.aeval gens) =
      (Ideal.Quotient.mkₐ Λ _).comp
        (MvPolynomial.aeval fun i => algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) (b i)) :=
    MvPolynomial.algHom_ext fun i => by
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq.2 (by simpa only [pow_one] using hb i)
  exact DFunLike.congr_fun key p

end AlgebraicGeometry.C1590Private

end
