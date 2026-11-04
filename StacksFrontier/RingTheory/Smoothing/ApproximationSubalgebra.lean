module

public import StacksFrontier.RingTheory.Smoothing.ApproximationHenselianGRing

/-!
# Approximating a finitely generated subalgebra of the completion

Let `(R, 𝔪)` be a henselian Noetherian local G-ring and let `A ⊆ R^∧` be a finitely generated
`R`-subalgebra of its `𝔪`-adic completion. By the approximation property of G-rings
(Stacks 07QY) there is an `R`-algebra map `A ⟶ R` which agrees with the inclusion `A ⊆ R^∧`
modulo `𝔪 R^∧`. This is the form in which the approximation property is used in the proof of
Stacks 0E7C: a datum defined over `A` is specialized to `R` without changing its reduction to the
residue field.

## Main results

* `Stacks.Smoothing.exists_algHom_sub_mem_map_of_fg`: the statement above.

## References

* [Stacks Project, Tag 07QY](https://stacks.math.columbia.edu/tag/07QY)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace Stacks.Smoothing

/-- Polynomial evaluation respects congruence modulo an ideal: if `a i ≡ c i mod J` for all `i`,
then `aeval a p ≡ aeval c p mod J`. -/
private theorem aeval_sub_aeval_mem_of_sub_mem {R S σ : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (J : Ideal S) {a c : σ → S} (h : ∀ i, a i - c i ∈ J) (p : MvPolynomial σ R) :
    MvPolynomial.aeval a p - MvPolynomial.aeval c p ∈ J := by
  rw [← Ideal.Quotient.eq]
  have hac : (Ideal.Quotient.mkₐ R J) ∘ a = (Ideal.Quotient.mkₐ R J) ∘ c := by
    funext i
    simp only [Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (h i)
  exact (MvPolynomial.comp_aeval_apply (f := a) (φ := Ideal.Quotient.mkₐ R J) (p := p)).trans
    ((congrArg (fun q => MvPolynomial.aeval q p) hac).trans
      (MvPolynomial.comp_aeval_apply (f := c) (φ := Ideal.Quotient.mkₐ R J) (p := p)).symm)

/-- A finitely generated subalgebra `A` of `S` is the image of a surjection
`MvPolynomial (Fin n) R →ₐ[R] A` given by evaluation at elements of `S`. -/
private theorem exists_surjective_aeval_of_fg {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {A : Subalgebra R S} (hA : A.FG) :
    ∃ (n : ℕ) (a : Fin n → S) (π : MvPolynomial (Fin n) R →ₐ[R] A),
      Function.Surjective π ∧ ∀ p, (π p : S) = MvPolynomial.aeval a p := by
  obtain ⟨s, hs⟩ := hA
  obtain ⟨n, a, hrangea⟩ := s.finite_toSet.fin_embedding
  have hrange : (MvPolynomial.aeval (R := R) a).range = A := by
    rw [← Algebra.adjoin_range_eq_range_aeval, hrangea, hs]
  refine ⟨n, a, (MvPolynomial.aeval (R := R) a).codRestrict A fun p => hrange ▸ ⟨p, rfl⟩,
    ?_, fun _ => rfl⟩
  rintro ⟨x, hx⟩
  rw [← hrange] at hx
  obtain ⟨p, hp⟩ := hx
  exact ⟨p, Subtype.ext hp⟩

/-- **Approximating a finitely generated subalgebra of the completion.** Let `R` be a henselian
Noetherian local G-ring and `A` a finitely generated `R`-subalgebra of `R^∧`. There is an
`R`-algebra map `φ : A ⟶ R` with `a - φ(a) ∈ 𝔪 R^∧` for every `a ∈ A` (Stacks 07QY). -/
theorem exists_algHom_sub_mem_map_of_fg {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsNoetherianRing R] (hG : IsGRing R)
    (A : Subalgebra R (AdicCompletion (maximalIdeal R) R)) (hA : A.FG) :
    ∃ φ : A →ₐ[R] R, ∀ a : A, (a : AdicCompletion (maximalIdeal R) R) -
      algebraMap R (AdicCompletion (maximalIdeal R) R) (φ a) ∈
        (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  classical
  set R' := AdicCompletion (maximalIdeal R) R
  set J := (maximalIdeal R).map (algebraMap R R')
  -- a presentation of `A` by polynomials in its generators
  obtain ⟨n, a, π, hπ, hπval⟩ := exists_surjective_aeval_of_fg hA
  -- the relations among the generators, finitely many by the Hilbert basis theorem
  obtain ⟨m, f, ht⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (RingHom.ker π))
  have hf : ∀ j, f j ∈ RingHom.ker π := fun j => ht ▸ Ideal.subset_span ⟨j, rfl⟩
  have ha : ∀ j, MvPolynomial.aeval a (f j) = 0 := fun j => by
    rw [← hπval, RingHom.mem_ker.mp (hf j)]
    rfl
  -- the approximation property of G-rings
  obtain ⟨b, hb, hsol⟩ := exists_approximate_solution_of_henselian_isGRing hG f a ha 1
  let ψ : MvPolynomial (Fin n) R →ₐ[R] R := MvPolynomial.aeval b
  have hker : RingHom.ker π ≤ RingHom.ker ψ := by
    rw [← ht, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hsol j
  refine ⟨AlgHom.liftOfSurjective π hπ ψ hker, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := hπ x
  rw [show AlgHom.liftOfSurjective π hπ ψ hker (π p) = ψ p from AlgHom.liftOfSurjective_apply ..,
    hπval]
  have h := aeval_sub_aeval_mem_of_sub_mem J (c := algebraMap R R' ∘ b)
    (fun i => by simpa using hb i) p
  rwa [MvPolynomial.aeval_algebraMap_apply] at h

end Stacks.Smoothing

end
