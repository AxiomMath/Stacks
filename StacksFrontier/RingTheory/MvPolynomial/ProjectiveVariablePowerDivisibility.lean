module

public import StacksFrontier.RingTheory.MvPolynomial.FreeModuleVariablePowerDivisibility

@[expose] public noncomputable section

open MvPolynomial

universe u v w x

namespace MvPolynomial

/-- **Two denominators at distinct variables are cleared by a common cofactor, in a projective
module over a ring isomorphic to a polynomial ring.** Let `e : R[Tᵤ] ≃+* B` and let `P` be a
projective `B`-module. If `e(Tⱼ)^l • u = e(Tᵢ)^k • v` in `P` with `i ≠ j`, there is `w ∈ P` with
`u = e(Tᵢ)^k • w` and `v = e(Tⱼ)^l • w`. A projective module is a direct summand of a free one,
where the cofactor is found coordinatewise
(`MvPolynomial.exists_eq_mul_X_pow_of_mul_X_pow_eq_mul_X_pow` transported along `e`), and the
retraction carries it back. -/
theorem exists_eq_smul_pow_of_smul_eq_smul_of_projective {R : Type u} [CommRing R]
    {σ : Type v} {B : Type w} [CommRing B] (e : MvPolynomial σ R ≃+* B) {P : Type x}
    [AddCommGroup P] [Module B P] [Module.Projective B P] {i j : σ} (hij : i ≠ j) {u v : P}
    {k l : ℕ} (h : e (X j) ^ l • u = e (X i) ^ k • v) :
    ∃ w : P, u = e (X i) ^ k • w ∧ v = e (X j) ^ l • w := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective B P)
  set d : σ →₀ ℕ := Finsupp.single i k with hd
  have key : ∀ p : P,
      s u p = e (X i) ^ k * e ((e.symm (s u p)).divMonomial d) ∧
        s v p = e (X j) ^ l * e ((e.symm (s u p)).divMonomial d) := by
    intro p
    have hp : e.symm (s u p) * X j ^ l = e.symm (s v p) * X i ^ k := by
      simpa [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, mul_comm] using
        congrArg (fun z => e.symm (s z p)) h
    obtain ⟨c, hu, hv⟩ := exists_eq_mul_X_pow_of_mul_X_pow_eq_mul_X_pow hij hp
    have hdiv : (e.symm (s u p)).divMonomial d = c := by
      rw [hu, hd, X_pow_eq_monomial, divMonomial_monomial_mul]
    rw [hdiv]
    constructor
    · rw [← e.apply_symm_apply (s u p), hu, map_mul, map_pow]
    · rw [← e.apply_symm_apply (s v p), hv, map_mul, map_pow]
  let w' : P →₀ B := (s u).mapRange (fun b => e ((e.symm b).divMonomial d)) (by simp)
  have hu' : s u = e (X i) ^ k • w' := Finsupp.ext fun p => (key p).1
  have hv' : s v = e (X j) ^ l • w' := Finsupp.ext fun p => (key p).2
  refine ⟨Finsupp.linearCombination B id w', ?_, ?_⟩
  · rw [← map_smul, ← hu']
    exact (LinearMap.congr_fun hs u).symm
  · rw [← map_smul, ← hv']
    exact (LinearMap.congr_fun hs v).symm

end MvPolynomial
