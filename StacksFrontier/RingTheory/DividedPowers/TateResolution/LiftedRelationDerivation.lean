module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DividedPowerDGALift
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Polynomial
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SquareZeroLift

/-!
# Computing the derivation on a lifted relation

A relation among equations of a polynomial presentation determines a degree-two
homology class modulo the annihilator of a principal square-zero extension. The
derivation of Tag 09PS sends this class to the coefficient of the lifted relation.

## Main results

* `DividedPowers.TateResolution.squareZeroExtensionDerivation_liftedRelation` computes the value
  of the derivation on the class associated to a relation.

## Implementation notes

The degree-two homology class is specified by a homogeneous representative whose
differential vanishes modulo `IA`. Its image under the derivation is represented
by a degree-zero element of `A/IA`; the augmentation compares this representative
with the lifted relation in `S/IS`. The map to `S` and its exactness in degrees
zero and one express precisely `S = H₀(A)` and `H₁(A) = 0`.

## References

* [Stacks Project, Tag 09PT](https://stacks.math.columbia.edu/tag/09PT)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open scoped BigOperators

universe u v w z t s

private theorem exists_coefficient_preimage
    {R : Type u} {A : Type v} {σ : Type z}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (ι : MvPolynomial σ R →ₐ[R] A)
    (hpoly : GradedDividedPowerPolynomial 𝒜 γ ι)
    {a : A} (ha : a ∈ 𝒜 0) : ∃ p, ι p = a := by
  refine Subring.closure_induction (s := Set.range ι) (p := fun x _ => ∃ p, ι p = x)
    ?_ ?_ ?_ ?_ ?_ ?_ (gradeZero_mem_coefficientClosure 𝒜 γ ι hpoly ha)
  · rintro x ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  · exact ⟨0, map_zero ι⟩
  · exact ⟨1, map_one ι⟩
  · rintro x y _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, map_add ι p q⟩
  · rintro x _ ⟨p, rfl⟩
    exact ⟨-p, map_neg ι p⟩
  · rintro x y _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p * q, map_mul ι p q⟩

/-- A relation with coefficients annihilating the square-zero generator yields a
degree-two class whose derivation is the coefficient of the lifted relation. -/
@[stacks 09PT]
public theorem squareZeroExtensionDerivation_liftedRelation
    {R' : Type u} {R : Type v} {A : Type w} {σ : Type z} {S : Type t}
    [CommRing R'] [CommRing R] [Ring A] [Algebra R A]
    [CommRing S] [Algebra R S]
    (q : R' →+* R) (hq : Function.Surjective q)
    (f : R') (hker : RingHom.ker q = Ideal.span {f})
    (hsq : (RingHom.ker q) ^ 2 = ⊥)
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜)
    (d : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 d]
    [IsCompatibleWithDifferential γ d]
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hpoly : GradedDividedPowerPolynomial 𝒜 γ ι)
    (hfinite₀ : Finite σ)
    (hfinite : ∀ n : ℕ, Finite (hpoly.indices n))
    (ε : A →ₐ[R] S)
    (hε₀ : ∀ s : S, ∃ a : A, a ∈ 𝒜 0 ∧ ε a = s)
    (hεd : ∀ a : A, ε (d a) = 0)
    (hH₀ : ∀ a : A, a ∈ 𝒜 0 → ε a = 0 →
      ∃ b : A, b ∈ 𝒜 1 ∧ d b = a)
    (hH₁ : ∀ a : A, a ∈ 𝒜 1 → d a = 0 →
      ∃ b : A, b ∈ 𝒜 2 ∧ d b = a)
    (n m : ℕ)
    (φ : MvPolynomial (Fin n) R →ₐ[R] S)
    (_hφ : Function.Surjective φ)
    (F r : Fin m → MvPolynomial (Fin n) R)
    (hkerφ : RingHom.ker φ.toRingHom = Ideal.span (Set.range F))
    (hrel : ∑ j, r j * F j = 0)
    (hcoeff : ∀ (j : Fin m) (e : Fin n →₀ ℕ),
      MvPolynomial.coeff e (r j) ∈
        Ideal.map q (Ideal.span {f}).annihilator)
    (F' r' : Fin m → MvPolynomial (Fin n) R')
    (g : MvPolynomial (Fin n) R')
    (hF : ∀ j, MvPolynomial.map q (F' j) = F j)
    (hr : ∀ j, MvPolynomial.map q (r' j) = r j)
    (hlift : ∑ j, r' j * F' j = g * MvPolynomial.C f) :
    let I : Ideal R := Ideal.map q (Ideal.span {f}).annihilator
    let J : Submodule R A := I • ⊤
    let IS : Ideal S := Ideal.map (algebraMap R S) I
    let θ := (squareZeroExtensionDerivation q hq f hker hsq 𝒜 γ d ι hpoly
      hfinite₀ hfinite).val
    ∃ ξ y : A,
      ξ ∈ 𝒜 2 ∧ d ξ ∈ J ∧ y ∈ 𝒜 0 ∧
      θ (Submodule.Quotient.mk ξ) = Submodule.Quotient.mk y ∧
      Ideal.Quotient.mk IS (ε y) =
        Ideal.Quotient.mk IS (φ (MvPolynomial.map q g)) := by
  let I : Ideal R := Ideal.map q (Ideal.span {f}).annihilator
  let J : Submodule R A := I • ⊤
  let ext := squareZeroExtensionDerivation q hq f hker hsq 𝒜 γ d ι hpoly hfinite₀ hfinite
  rcases ext.property with ⟨_, hθdegree, _, _, B, hBRing, hBAlg, hBRest⟩
  let _ : Ring B := hBRing
  rcases hBRest with ⟨ℬ, hBGraded, hBRest⟩
  let _ : Algebra R' B := hBAlg
  let _ : GradedAlgebra ℬ := hBGraded
  rcases hBRest with ⟨hBStrict, hBRest⟩
  let _ : IsStrictlyGradedComm ℬ := hBStrict
  rcases hBRest with ⟨_, ι', hpolyB, _, π, D, κ, hπsurj, _, hπι, _, _, _, hπker,
    hDzero, _, hDmul, _, hπD, hκ, hθκ⟩
  have hX (i : Fin n) : ∃ p, ε (ι p) = φ (MvPolynomial.X i) := by
    obtain ⟨a, ha, hεa⟩ := hε₀ (φ (MvPolynomial.X i))
    obtain ⟨p, rfl⟩ := exists_coefficient_preimage 𝒜 γ ι hpoly ha
    exact ⟨p, hεa⟩
  choose p hp using hX
  let ψ : MvPolynomial (Fin n) R →ₐ[R] A := ι.comp (MvPolynomial.aeval p)
  have hεψ (x : MvPolynomial (Fin n) R) : ε (ψ x) = φ x := by
    have hext : (ε.comp ι).comp (MvPolynomial.aeval p) = φ :=
      MvPolynomial.algHom_ext fun i => by simp [hp]
    exact DFunLike.congr_fun hext x
  have hψgrade (x) : ψ x ∈ 𝒜 0 := hpoly.coefficient_mem (MvPolynomial.aeval p x)
  have hφF (j : Fin m) : φ (F j) = 0 := RingHom.mem_ker.mp
    (show F j ∈ RingHom.ker φ.toRingHom from hkerφ ▸ Ideal.subset_span ⟨j, rfl⟩)
  choose u hu1 hdu using fun j => hH₀ (ψ (F j)) (hψgrade (F j)) (by simp [hεψ, hφF])
  have hz1 : ∑ j, ψ (r j) * u j ∈ 𝒜 1 :=
    Submodule.sum_mem _ fun j _ => SetLike.mul_mem_graded (hψgrade (r j)) (hu1 j)
  have hdz : d (∑ j, ψ (r j) * u j) = 0 := by
    rw [map_sum]
    simp_rw [IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := d) (hψgrade (r _)) (hu1 _),
      IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d) (hψgrade _), hdu]
    simp only [zero_mul, zero_add, pow_zero, one_smul]
    simpa using congrArg ψ hrel
  obtain ⟨ξ, hξ2, hdξ⟩ := hH₁ _ hz1 hdz
  obtain ⟨y, hy0, hθξ⟩ := hθdegree 0 ξ (by simpa using hξ2)
  choose p' hmapP using fun i => MvPolynomial.map_surjective (f := q) hq (p i)
  let ψB : MvPolynomial (Fin n) R' →ₐ[R'] B := ι'.comp (MvPolynomial.aeval p')
  have hmap (x : MvPolynomial (Fin n) R') :
      MvPolynomial.map q (MvPolynomial.aeval p' x) =
        MvPolynomial.aeval p (MvPolynomial.map q x) := by
    induction x using MvPolynomial.induction_on with
    | C a => simp
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
    | mul_X a i ha =>
      rw [map_mul, map_mul, map_mul, map_mul, ha, MvPolynomial.aeval_X, MvPolynomial.map_X,
        MvPolynomial.aeval_X, hmapP]
  have hψB (x : MvPolynomial (Fin n) R') : π (ψB x) = ψ (MvPolynomial.map q x) :=
    (hπι (MvPolynomial.aeval p' x)).trans (congrArg ι (hmap x))
  choose rA hrA hann using fun j =>
    exists_map_eq_and_coeff_mem_annihilator q hq f (r j) (hcoeff j)
  choose b hb using fun j => exists_eq_C_mul_of_map_eq_zero q f hker (r' j - rA j)
    (by rw [map_sub, hr j, hrA j, sub_self])
  have hrAf (j : Fin m) : MvPolynomial.C f * rA j = 0 := by
    ext e
    rw [MvPolynomial.coeff_C_mul]
    simpa [smul_eq_mul, mul_comm] using
      (Submodule.mem_annihilator_span_singleton f _).mp (hann j e)
  have hliftA : ∑ j, rA j * F' j = (g - ∑ j, b j * F' j) * MvPolynomial.C f := by
    have hr' (j : Fin m) : r' j = rA j + MvPolynomial.C f * b j := by
      linear_combination hb j
    have hsum : ∑ j, r' j * F' j =
        (∑ j, rA j * F' j) + MvPolynomial.C f * ∑ j, b j * F' j := by
      simp_rw [hr', add_mul, mul_assoc]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    linear_combination hlift - hsum
  choose v hπv using fun j => hπsurj (u j)
  choose c hc using fun j => (hπker (D (v j) - ψB (F' j))).mp
    (by simp [hπD, hπv, hdu, hψB, hF])
  obtain ⟨w, hπw⟩ := hπsurj ξ
  obtain ⟨c₀, hc₀⟩ := (hπker (D w - ∑ j, ψB (rA j) * v j)).mp
    (by simp [hπD, hπw, hdξ, hψB, hrA, hπv])
  let e₀ : B := ψB (g - ∑ j, b j * F' j) + D c₀
  have hscalar (j : Fin m) : algebraMap R' B f * ψB (rA j) = 0 := by
    simpa [MvPolynomial.algHom_C] using congrArg ψB (hrAf j)
  have hD (j : Fin m) : D (ψB (rA j) * v j) = ψB (rA j) * ψB (F' j) := by
    rw [differential_mul_of_mem_gradeZero ℬ D hDzero hDmul
      (show ψB (rA j) ∈ ℬ 0 from hpolyB.coefficient_mem _), sub_eq_iff_eq_add'.mp (hc j),
      mul_add, ← mul_assoc, ← Algebra.commutes f (ψB (rA j)), hscalar, zero_mul, add_zero]
  have hsum : ∑ j, ψB (rA j) * ψB (F' j) = ψB (g - ∑ j, b j * F' j) * algebraMap R' B f := by
    simpa [MvPolynomial.algHom_C] using congrArg ψB hliftA
  have hDsqw : D (D w) = algebraMap R' B f * e₀ := by
    simp only [sub_eq_iff_eq_add'.mp hc₀, map_add, map_sum, hD]
    rw [hsum, ← Algebra.smul_def f c₀, map_smul, Algebra.smul_def, ← Algebra.commutes, mul_add]
  obtain ⟨hDker, hθw⟩ := hθκ w
  have hθe : ext.val (Submodule.Quotient.mk ξ) = Submodule.Quotient.mk (π e₀) := by
    rw [← hπw, hθw, ← hκ e₀ (by rwa [← hDsqw])]
    exact congrArg κ (Subtype.ext hDsqw)
  have hεe : ε (π e₀) = φ (MvPolynomial.map q g) := by simp [e₀, hψB, hπD, hεψ, hεd, hF, hφF]
  refine ⟨ξ, y, hξ2, ?_, hy0, hθξ, Ideal.Quotient.eq.mpr ?_⟩
  · rw [hdξ]
    exact Submodule.sum_mem _ fun j _ => eval_mul_mem_smul_top I ψ (r j) (hcoeff j) (u j)
  · have hdiffJ : y - π e₀ ∈ J := (Submodule.Quotient.eq J).mp (by simpa using hθξ.symm.trans hθe)
    have hle : I • (⊤ : Submodule R A) ≤
        Submodule.comap ε.toLinearMap ((I.map (algebraMap R S)).restrictScalars R) := by
      refine Submodule.smul_le.mpr fun t ht a _ => ?_
      show ε (t • a) ∈ I.map (algebraMap R S)
      rw [Algebra.smul_def, map_mul, ε.commutes]
      exact Ideal.mul_mem_right (ε a) _ (Ideal.mem_map_of_mem (algebraMap R S) ht)
    simpa [hεe, I] using hle hdiffJ

end DividedPowers.TateResolution

end
