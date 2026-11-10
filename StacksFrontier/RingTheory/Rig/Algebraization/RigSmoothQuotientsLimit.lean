module

public import StacksFrontier.RingTheory.Rig.Algebraization.AlgebraizationTowerComparison
public import StacksFrontier.RingTheory.Restricted.RigSmoothSmoothLocus
public import StacksFrontier.RingTheory.Rig.RigSmoothPointwiseDescent
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeKer
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeCotangent
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeExt
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeComparison

/-!
# Rig-smoothness from smooth quotients and a rig-smooth completion

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `a ∈ I`. Let `B'` be an `a`-adically complete
`A`-algebra of finite type modulo `a`, and let `B' → B` be bijective modulo every power of `I`,
with `B` an `I`-adically complete `A`-algebra of finite type modulo `I` (so `B` is the `I`-adic
completion of `B'`). If `B` is rig-smooth over `(A, I)` and every quotient `B' ⧸ aⁿ⁺¹` is
smooth over `Spec(A ⧸ aⁿ⁺¹) ∖ V(I)`, then `B'` is rig-smooth over `(A, (a))`.

This is the smoothening lemma `lemma:smoothify` of Gabber–Zavyalov, used in their proof of
[Gabber–Zavyalov, Theorem 1.2], the main claim of Stacks Remark 0GAX: the induction on the number
of generators of `I` algebraizes `B` modulo powers of the first generator `f₁`, passes to the limit
`B'` of those algebraizations, and this file shows that `B'` is rig-smooth over `(A, (f₁))`, so
that the principal case applies to it.

## Main results

* `Rig.isRigSmooth_of_isBijectiveMod_of_smoothAwayFrom_quotients`: the statement above.
* `Rig.QuotientsLimit.localized_hneg_hzero_of_liesOver`: at a prime of `B'` under a prime of `B`
  off `V(I B)`, the cohomology of `NL^∧_{B'/A}` is that of `NL^∧_{B/A}`.
* `Rig.QuotientsLimit.exists_mem_cotangentFactorizationIdeal_of_smoothAwayFrom`: at a prime of
  `B'` containing `a` but not `I`, the differential of `NL^∧_{B'/A}` splits after inverting an
  element outside the prime.

## Implementation notes

The proof is the one of Gabber–Zavyalov, read at the maximal ideals of `B'` rather than through
the faithfully flat cover `B' → B × ∏ᵢ B'[1/fᵢ]^∧` and derived limits. By Stacks 0GAJ read at a
single prime (`Rig.isRigSmooth_of_forall_prime`) one has to show, at a prime `q` of `B'` not
containing `a`, that `H⁻¹(NL^∧_{B'/A})_q = 0` and `H⁰(NL^∧_{B'/A})_q` is free. Every maximal
ideal `m ⊇ q` contains `a`, because `B'` is `a`-adically complete.

* If `I B' ⊆ m`, there is a prime of `B` over `q` (going down for the flat map `B' → B`, which is
  the `I`-adic completion of the Noetherian ring `B'`). For the compatible presentations of
  Stacks 0GAG the comparison `J'/J'² ⊗_{B'} B → J/J²` of conormal modules is onto
  (Stacks 0GAG) and injective, the latter by the Artin–Rees lemma in `A[x]^∧_{(a)}` and Krull's
  intersection theorem in `B`; so `NL^∧_{B/A} = NL^∧_{B'/A} ⊗_{B'} B`, and both conclusions
  descend along the flat local map `B'_q → B_{q'}` from the rig-smoothness of `B`.
* If `I B' ⊄ m`, take `n` beyond the Artin–Rees exponent of the presentation ideal `J'` for `(a)`.
  Smoothness of `B' ⧸ aⁿ⁺¹` at `m` gives `t ∉ m` and a splitting `ψ̄` of multiplication by `t`
  through the differential of the polynomial presentation of `B' ⧸ aⁿ⁺¹`. The comparison
  `J'/J'² → J̄/J̄²` is onto with kernel in `a · J'/J'²` (Artin–Rees), so a lift `ψ` of `ψ̄`
  satisfies `ψ ∘ d ≡ t` modulo `a`, and the Cayley–Hamilton theorem turns this into a genuine
  factorization of multiplication by some `s ∉ m`.

## References

* [Stacks Project, Tag 0GAX](https://stacks.math.columbia.edu/tag/0GAX)
* [Stacks Project, Tag 0GAJ](https://stacks.math.columbia.edu/tag/0GAJ)
* [Stacks Project, Tag 0GAG](https://stacks.math.columbia.edu/tag/0GAG)
* O. Gabber, B. Zavyalov, *Noetherian rig-smooth algebraization*, arXiv:2402.08741,
  Lemma `smoothify`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Rig

namespace QuotientsLimit

/-- The base change of the quotient map by the range of `d` is onto, with kernel the range of the
base change of `d`. -/
private theorem surjective_and_exact_baseChange_mkQ_range {R : Type*} (T : Type*) [CommRing R]
    [CommRing T] [Algebra R T] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (d : M →ₗ[R] N) :
    Function.Surjective ((LinearMap.range d).mkQ.baseChange T) ∧
      Function.Exact (d.baseChange T) ((LinearMap.range d).mkQ.baseChange T) := by
  simp only [LinearMap.baseChange_eq_lTensor]
  exact ⟨LinearMap.lTensor_surjective T (Submodule.mkQ_surjective _),
    lTensor_exact T (LinearMap.exact_map_mkQ_range d) (Submodule.mkQ_surjective _)⟩

/-- **Artin–Rees, in the form used for conormal modules.** For ideals `𝔞, J` of a Noetherian
ring there is `k` such that an element of `J` lying in `𝔞ᵏ⁺ⁿ` lies in `𝔞ⁿ J`. -/
private theorem exists_mem_mul_of_mem_pow {R : Type*} [CommRing R] [IsNoetherianRing R]
    (𝔞 J : Ideal R) : ∃ k : ℕ, ∀ (n : ℕ) (z : R), z ∈ J → z ∈ 𝔞 ^ (k + n) → z ∈ 𝔞 ^ n * J := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔞 (M := R) (J : Submodule R R)
  refine ⟨k, fun n z hzJ hz ↦ ?_⟩
  have hmem : z ∈ 𝔞 ^ (k + n) • (⊤ : Submodule R R) ⊓ (J : Submodule R R) :=
    ⟨by rwa [smul_eq_mul, Ideal.mul_top], hzJ⟩
  rw [hk (k + n) le_self_add, Nat.add_sub_cancel_left] at hmem
  exact Submodule.smul_mono le_rfl inf_le_right hmem

/-- Approximation by images of an ideal `L`: if every element of `T` agrees with the image of an
element of `R` modulo `E`, then every element of `L.map f` agrees with the image of an element
of `L` modulo `E`. -/
private theorem exists_mem_sub_mem_of_mem_map_of_approx {R T F : Type*} [CommRing R]
    [CommRing T] [FunLike F R T] [RingHomClass F R T] (f : F) (E : Ideal T)
    (happrox : ∀ c : T, ∃ x, c - f x ∈ E) (L : Ideal R)
    {y : T} (hy : y ∈ L.map f) : ∃ l ∈ L, y - f l ∈ E := by
  let S : Ideal T :=
    { carrier := {y | ∃ l ∈ L, y - f l ∈ E}
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      add_mem' := by
        rintro y y' ⟨l, hl, h⟩ ⟨l', hl', h'⟩
        refine ⟨l + l', L.add_mem hl hl', ?_⟩
        rw [map_add, add_sub_add_comm]
        exact E.add_mem h h'
      smul_mem' := by
        rintro c y ⟨l, hl, h⟩
        obtain ⟨x, hx⟩ := happrox c
        refine ⟨x * l, L.mul_mem_left x hl, ?_⟩
        have hEq : c • y - f (x * l) = f x * (y - f l) + (c - f x) * y := by
          rw [map_mul, smul_eq_mul]
          ring
        rw [hEq]
        exact E.add_mem (E.mul_mem_left _ h) (E.mul_mem_right _ hx) }
  have hle : L.map f ≤ S := Ideal.map_le_iff_le_comap.mpr fun l hl ↦ ⟨l, hl, by simp⟩
  exact hle hy

/-! ### Linear algebra -/

section LinearAlgebra

variable {R : Type*} [CommRing R]

/-- If multiplication by `s` on the source of `d : M → R^r` factors through `d`, then at a prime
`q` not containing `s` the kernel of `d` vanishes and the cokernel of `d` is free. -/
theorem subsingleton_ker_and_free_coker_of_mem [IsNoetherianRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {r : ℕ} (d : M →ₗ[R] (Fin r → R)) {s : R}
    (hs : s ∈ cotangentFactorizationIdeal d) (q : Ideal R) [q.IsPrime] (hsq : s ∉ q) :
    Subsingleton (LocalizedModule q.primeCompl (LinearMap.ker d)) ∧
      Module.Free (Localization.AtPrime q)
        (LocalizedModule q.primeCompl ((Fin r → R) ⧸ LinearMap.range d)) := by
  obtain ⟨h, hh⟩ := hs
  have hhd : ∀ x, h (d x) = s • x := fun x ↦ LinearMap.congr_fun hh x
  refine ⟨PointwiseDescent.localized_subsingleton_of_mem_annihilator q.primeCompl s hsq ?_, ?_⟩
  · rw [Module.mem_annihilator]
    rintro ⟨x, hx⟩
    apply Subtype.ext
    simp only [Submodule.coe_smul, ZeroMemClass.coe_zero]
    rw [← hhd x, LinearMap.mem_ker.mp hx, map_zero]
  set C := (Fin r → R) ⧸ LinearMap.range d
  have : Module.FinitePresentation R C := Module.finitePresentation_of_finite R C
  let T := Localization.Away s
  have hunit : IsUnit (algebraMap R T s) :=
    IsLocalization.map_units T (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)
  obtain ⟨c, hc⟩ := hunit.exists_left_inv
  -- the base changed differential is split injective
  have hl : (c • h.baseChange T) ∘ₗ d.baseChange T = LinearMap.id := by
    rw [LinearMap.smul_comp, ← LinearMap.baseChange_comp, hh]
    refine LinearMap.ext fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | tmul t x =>
      rw [LinearMap.smul_apply, LinearMap.baseChange_tmul, LinearMap.id_apply,
        LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.tmul_smul,
        ← algebraMap_smul T s, smul_smul, hc, one_smul]
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  obtain ⟨hsurj, hex⟩ := surjective_and_exact_baseChange_mkQ_range T d
  obtain ⟨σ, hσ⟩ := ((hex.split_tfae'.out 2 1 rfl rfl).mp ⟨hsurj, _, hl⟩).2
  have : Module.Projective T (T ⊗[R] (Fin r → R)) := by
    have : Module.Free T (T ⊗[R] (Fin r → R)) :=
      Module.Free.of_basis ((Pi.basisFun R (Fin r)).baseChange T)
    infer_instance
  have hproj : Module.Projective T (T ⊗[R] C) := Module.Projective.of_split σ _ hσ
  have hproj' : Module.Projective T (LocalizedModule.Away s C) :=
    Module.Projective.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers s) C).symm
  have hsub := (Module.basicOpen_subset_freeLocus_iff (R := R) (M := C) (f := s)).mpr hproj'
  exact Module.mem_freeLocus.mp (hsub (show (⟨q, inferInstance⟩ : PrimeSpectrum R) ∈
    PrimeSpectrum.basicOpen s from hsq))

/-- **The determinant trick.** Let `d : M → F` and `ψ : F → M` with `M` finite, and suppose
that `ψ ∘ d` agrees with multiplication by `t` modulo `𝔞 M`. If `𝔞` lies in a prime `m` not
containing `t`, then the ideal of scalars whose multiplication on `M` factors through `d`
is not contained in `m`. -/
theorem exists_mem_cotangentFactorizationIdeal_notMem {M F : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [AddCommGroup F] [Module R F]
    (d : M →ₗ[R] F) (ψ : F →ₗ[R] M) (t : R) (𝔞 : Ideal R)
    (h : ∀ x, ψ (d x) - t • x ∈ 𝔞 • (⊤ : Submodule R M))
    (m : Ideal R) [m.IsPrime] (h𝔞 : 𝔞 ≤ m) (ht : t ∉ m) :
    ∃ s ∈ cotangentFactorizationIdeal d, s ∉ m := by
  set u : Module.End R M := ψ ∘ₗ d with hu
  set f : Module.End R M := u - t • LinearMap.id with hf
  have hrange : LinearMap.range f ≤ 𝔞 • ⊤ := by
    rintro _ ⟨x, rfl⟩
    exact h x
  obtain ⟨p, hmon, -, hcoeff, hp⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R f 𝔞 hrange
  set Q : Polynomial R := p.comp (Polynomial.X - Polynomial.C t) with hQ
  have hQu : Polynomial.aeval u Q = 0 := by
    rw [hQ, Polynomial.aeval_comp, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Module.algebraMap_end_eq_smul_id, ← hf, hp]
  refine ⟨Q.coeff 0, ⟨-(Polynomial.aeval u Q.divX ∘ₗ ψ), ?_⟩, ?_⟩
  · have hdecomp := Polynomial.divX_mul_X_add Q
    have h0 : Polynomial.aeval u Q.divX * u + (Q.coeff 0) • (1 : Module.End R M) = 0 := by
      rw [← hQu]
      conv_rhs => rw [← hdecomp]
      rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one]
    ext x
    have hx := LinearMap.congr_fun h0 x
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply, LinearMap.zero_apply, hu, LinearMap.comp_apply] at hx
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    rwa [neg_eq_iff_add_eq_zero]
  · intro hm
    have heval : Q.coeff 0 = p.eval (-t) := by
      rw [Polynomial.coeff_zero_eq_eval_zero, hQ, Polynomial.eval_comp, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    rw [heval, Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree,
      one_mul] at hm
    have hrest : ∑ i ∈ Finset.range p.natDegree, p.coeff i * (-t) ^ i ∈ m := by
      refine Ideal.sum_mem _ fun i hi ↦ Ideal.mul_mem_right _ _ (h𝔞 ?_)
      have hlt : 0 < p.natDegree - i := Nat.sub_pos_of_lt (Finset.mem_range.mp hi)
      exact Ideal.pow_le_self hlt.ne' (hcoeff i)
    have htm : (-t) ^ p.natDegree ∈ m := by
      have := m.sub_mem hm hrest
      rwa [add_sub_cancel_left] at this
    exact ht (by simpa using m.neg_mem_iff.mp (‹m.IsPrime›.mem_of_pow_mem _ htm))

end LinearAlgebra

/-! ### Comparing completed polynomial algebras for two ideals -/

section PolynomialComparison

variable {A : Type u} [CommRing A] {I₁ I₂ : Ideal A}
  (hmap : (I₁ ^ 1).map (algebraMap A A) ≤ I₂) (r : ℕ)

/-- The ideal generated by `J` in `A[x]^∧`, written through the polynomial ring or through `A`. -/
theorem map_coeffIdeal_eq (J K : Ideal A) :
    (J.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)).map
        (algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra K r)) =
      J.map (algebraMap A (completedPolynomialAlgebra K r)) := by
  rw [Ideal.map_map]
  congr 1

/-- On polynomials, the comparison map `A[x]^∧_{I₁} → A[x]^∧_{I₂}` is the identity. -/
theorem polynomialBaseChange_algebraMap_self (p : MvPolynomial (Fin r) A) :
    polynomialBaseChange hmap r
        (algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I₁ r) p) =
      algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I₂ r) p := by
  rw [polynomialBaseChange_algebraMap, Algebra.algebraMap_self, MvPolynomial.map_id]

/-- The comparison map carries the ideal generated by `I₂` onto the ideal generated by `I₂`. -/
theorem map_polynomialBaseChange_map (J : Ideal A) :
    (J.map (algebraMap A (completedPolynomialAlgebra I₁ r))).map
        (polynomialBaseChange hmap r) =
      J.map (algebraMap A (completedPolynomialAlgebra I₂ r)) := by
  change Ideal.map (polynomialBaseChange hmap r).toRingHom _ = _
  rw [Ideal.map_map]
  congr 1
  ext x
  simp

/-- Every element of `A[x]^∧_{I₂}` agrees with an element of the image of `A[x]^∧_{I₁}` modulo
any power of `I₂`. -/
theorem exists_sub_polynomialBaseChange_mem (hI₂ : I₂.FG) (N : ℕ)
    (y : completedPolynomialAlgebra I₂ r) :
    ∃ x, y - polynomialBaseChange hmap r x ∈
      (I₂.map (algebraMap A (completedPolynomialAlgebra I₂ r))) ^ N := by
  obtain ⟨p, hp⟩ := AdicCompletion.exists_sub_mem_map_pow
    (I₂.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) (hI₂.map _) N y
  refine ⟨algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I₁ r) p, ?_⟩
  rw [polynomialBaseChange_algebraMap_self, ← map_coeffIdeal_eq, ← Ideal.map_pow]
  exact hp

/-- The comparison map `A[x]^∧_{I₁} → A[x]^∧_{I₂}` is injective modulo every power of `I₂`. -/
theorem mem_pow_of_polynomialBaseChange_mem (hI₁ : I₁.FG) (hI₂ : I₂.FG) (h12 : I₁ ≤ I₂)
    (N : ℕ) (x : completedPolynomialAlgebra I₁ r)
    (hx : polynomialBaseChange hmap r x ∈
      (I₂.map (algebraMap A (completedPolynomialAlgebra I₂ r))) ^ N) :
    x ∈ (I₂.map (algebraMap A (completedPolynomialAlgebra I₁ r))) ^ N := by
  set β := polynomialBaseChange hmap r
  obtain ⟨p, hp⟩ := AdicCompletion.exists_sub_mem_map_pow
    (I₁.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) (hI₁.map _) N x
  set δ := x - algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I₁ r) p
  have hδ : δ ∈ (I₂.map (algebraMap A (completedPolynomialAlgebra I₁ r))) ^ N := by
    rw [Ideal.map_pow, map_coeffIdeal_eq] at hp
    exact Ideal.pow_right_mono (Ideal.map_mono h12) N hp
  have hβδ : β δ ∈ (I₂.map (algebraMap A (completedPolynomialAlgebra I₂ r))) ^ N := by
    rw [← map_polynomialBaseChange_map hmap r, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hδ
  have hp' : algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I₂ r) p ∈
      ((I₂.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) ^ N).map
        (algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I₂ r)) := by
    rw [Ideal.map_pow, map_coeffIdeal_eq, ← polynomialBaseChange_algebraMap_self hmap r]
    have := Ideal.sub_mem _ hx hβδ
    rwa [← map_sub, sub_sub_cancel] at this
  have hpN := AdicCompletion.mem_pow_of_algebraMap_mem_map_pow _ (hI₂.map _) N p hp'
  have hpx : algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I₁ r) p ∈
      (I₂.map (algebraMap A (completedPolynomialAlgebra I₁ r))) ^ N := by
    rw [← map_coeffIdeal_eq, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hpN
  rw [← sub_add_cancel x (algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I₁ r) p)]
  exact Ideal.add_mem _ hδ hpx

/-- Every element of the ideal generated by the image of an ideal `L` agrees with the image of an
element of `L` modulo any power of `I₂`. -/
theorem exists_mem_sub_mem_of_mem_map (hI₂ : I₂.FG) (L : Ideal (completedPolynomialAlgebra I₁ r))
    (N : ℕ) {y : completedPolynomialAlgebra I₂ r} (hy : y ∈ L.map (polynomialBaseChange hmap r)) :
    ∃ l ∈ L, y - polynomialBaseChange hmap r l ∈
      (I₂.map (algebraMap A (completedPolynomialAlgebra I₂ r))) ^ N :=
  exists_mem_sub_mem_of_mem_map_of_approx (polynomialBaseChange hmap r) _
    (exists_sub_polynomialBaseChange_mem hmap r hI₂ N) L hy

/-- **The comparison map is injective on conormal modules modulo powers of `I₂`.** Let `J₁` be
an ideal of `A[x]^∧_{I₁}` and `J₂ ⊆ J₁ · A[x]^∧_{I₂}` an ideal of `A[x]^∧_{I₂}`. If the image of
`z ∈ J₁` lies in `I₂ⁿ J₂ + J₂²`, then `z ∈ I₂ⁿ J₁ + J₁²`. The proof is the Artin–Rees lemma
in the Noetherian ring `A[x]^∧_{I₁}`. -/
theorem mem_of_polynomialBaseChange_mem [IsNoetherianRing A] (hI₁ : I₁.FG) (hI₂ : I₂.FG)
    (h12 : I₁ ≤ I₂) (J₁ : Ideal (completedPolynomialAlgebra I₁ r))
    (J₂ : Ideal (completedPolynomialAlgebra I₂ r))
    (hJ : J₂ ≤ J₁.map (polynomialBaseChange hmap r)) (n : ℕ) {z : completedPolynomialAlgebra I₁ r}
    (hz : z ∈ J₁)
    (hβ : polynomialBaseChange hmap r z ∈
      (I₂.map (algebraMap A (completedPolynomialAlgebra I₂ r))) ^ n * J₂ + J₂ ^ 2) :
    z ∈ (I₂.map (algebraMap A (completedPolynomialAlgebra I₁ r))) ^ n * J₁ + J₁ ^ 2 := by
  set β := polynomialBaseChange hmap r
  set 𝔦 := I₂.map (algebraMap A (completedPolynomialAlgebra I₁ r))
  have : IsNoetherianRing (completedPolynomialAlgebra I₁ r) :=
    AdicCompletion.isNoetherianRing (I₁.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
  set L := 𝔦 ^ n * J₁ + J₁ ^ 2 with hL
  have hLJ : L ≤ J₁ := sup_le Ideal.mul_le_right (Ideal.pow_le_self two_ne_zero)
  have hmapL : (I₂.map (algebraMap A (completedPolynomialAlgebra I₂ r))) ^ n * J₂ + J₂ ^ 2 ≤
      L.map β := by
    rw [hL, Ideal.add_eq_sup, Ideal.add_eq_sup, Ideal.map_sup, Ideal.map_mul, Ideal.map_pow,
      Ideal.map_pow, map_polynomialBaseChange_map]
    exact sup_le_sup (Ideal.mul_mono_right hJ) (Ideal.pow_right_mono hJ 2)
  obtain ⟨k, hk⟩ := exists_mem_mul_of_mem_pow 𝔦 J₁
  obtain ⟨l, hl, hzl⟩ := exists_mem_sub_mem_of_mem_map hmap r hI₂ L (k + n) (hmapL hβ)
  have hAR : z - l ∈ 𝔦 ^ n * J₁ := by
    refine hk n _ (J₁.sub_mem hz (hLJ hl)) ?_
    refine mem_pow_of_polynomialBaseChange_mem hmap r hI₁ hI₂ h12 (k + n) (z - l) ?_
    rwa [map_sub]
  rw [← sub_add_cancel z l]
  exact L.add_mem (Ideal.mem_sup_left hAR) hl

end PolynomialComparison

/-! ### Conormal modules and base change -/

section Conormal

open Algebra.Extension in
/-- The class of `z ∈ J` in `J / J²` lies in `𝔟 · (J / J²)` exactly when `z ∈ 𝔟 J + J²`. -/
theorem cotangent_mk_mem_smul_top_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) (𝔟 : Ideal P.Ring) (z : P.ker) :
    Cotangent.mk z ∈ (𝔟.map (algebraMap P.Ring S)) • (⊤ : Submodule S P.Cotangent) ↔
      z.1 ∈ 𝔟 * P.ker + P.ker ^ 2 := by
  constructor
  · intro hz
    have key : ∀ x ∈ (𝔟.map (algebraMap P.Ring S)) • (⊤ : Submodule S P.Cotangent),
        ∃ w : P.ker, w.1 ∈ 𝔟 * P.ker ∧ Cotangent.mk w = x := by
      intro x hx
      refine Submodule.smul_induction_on hx (fun c hc y _ ↦ ?_) (fun x y hx hy ↦ ?_)
      · obtain ⟨α, hα, rfl⟩ :=
          (Ideal.mem_map_iff_of_surjective _ P.algebraMap_surjective).mp hc
        obtain ⟨w, rfl⟩ := Cotangent.mk_surjective y
        refine ⟨α • w, Ideal.mul_mem_mul hα w.2, ?_⟩
        rw [map_smul, algebraMap_smul]
      · obtain ⟨w₁, hw₁, rfl⟩ := hx
        obtain ⟨w₂, hw₂, rfl⟩ := hy
        exact ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, map_add _ _ _⟩
    obtain ⟨w, hw, hwz⟩ := key _ hz
    have hsub := (Cotangent.mk_eq_mk_iff_sub_mem z w).mp hwz.symm
    rw [← add_sub_cancel w.1 z.1]
    exact Submodule.add_mem_sup hw hsub
  · intro hz
    set T := (𝔟.map (algebraMap P.Ring S)) • (⊤ : Submodule S P.Cotangent)
    have key : ∀ y ∈ 𝔟 * P.ker, y ∈ P.ker ∧ ∀ h : y ∈ P.ker, Cotangent.mk ⟨y, h⟩ ∈ T := by
      intro y hy
      refine Submodule.mul_induction_on hy (fun α hα j hj ↦ ?_) (fun x y hx hy ↦ ?_)
      · refine ⟨Ideal.mul_mem_left _ _ hj, fun h ↦ ?_⟩
        have hEq : (⟨α * j, h⟩ : P.ker) = α • ⟨j, hj⟩ := rfl
        rw [hEq, map_smul, ← algebraMap_smul S α]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hα) Submodule.mem_top
      · refine ⟨Ideal.add_mem _ hx.1 hy.1, fun h ↦ ?_⟩
        have hEq : (⟨x + y, h⟩ : P.ker) = ⟨x, hx.1⟩ + ⟨y, hy.1⟩ := rfl
        rw [hEq, map_add]
        exact Submodule.add_mem _ (hx.2 _) (hy.2 _)
    obtain ⟨y, hy, v, hv, hyv⟩ := Submodule.mem_sup.mp hz
    obtain ⟨hyJ, hyT⟩ := key y hy
    have hvJ : v ∈ P.ker := Ideal.pow_le_self two_ne_zero hv
    have hEq : z = ⟨y, hyJ⟩ + ⟨v, hvJ⟩ := Subtype.ext hyv.symm
    rw [hEq, map_add, (Cotangent.mk_eq_zero_iff (⟨v, hvJ⟩ : P.ker)).mpr hv, add_zero]
    exact hyT hyJ

variable {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]

/-- **Injectivity of a base-changed map, detected modulo powers of an ideal.** Let `R₂` be
Noetherian, let `𝔟 ⊆ R₁` be an ideal with `𝔟 R₂` in the Jacobson radical, such that `R₁` is
dense in `R₂` for the `𝔟`-adic topology. If `π₀ : M₁ → M₂` (with `M₁` finite) satisfies
`π₀ m ∈ 𝔟ⁿ M₂ → m ∈ 𝔟ⁿ M₁` for all `n`, then `R₂ ⊗ M₁ → M₂` is injective. -/
theorem injective_liftBaseChange_of_mem_smul [IsNoetherianRing R₂] {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R₁ M₁] [Module.Finite R₁ M₁] [AddCommGroup M₂] [Module R₂ M₂]
    [Module R₁ M₂] [IsScalarTower R₁ R₂ M₂] (π₀ : M₁ →ₗ[R₁] M₂) (𝔟 : Ideal R₁)
    (hjac : 𝔟.map (algebraMap R₁ R₂) ≤ (⊥ : Ideal R₂).jacobson)
    (happrox : ∀ (n : ℕ) (y : R₂), ∃ x, y - algebraMap R₁ R₂ x ∈ (𝔟.map (algebraMap R₁ R₂)) ^ n)
    (hmod : ∀ (n : ℕ) (m : M₁), π₀ m ∈ (𝔟.map (algebraMap R₁ R₂)) ^ n • (⊤ : Submodule R₂ M₂) →
      m ∈ 𝔟 ^ n • (⊤ : Submodule R₁ M₁)) :
    Function.Injective (π₀.liftBaseChange R₂) := by
  set 𝔠 := 𝔟.map (algebraMap R₁ R₂)
  set π := π₀.liftBaseChange R₂
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hall : x ∈ ⨅ n : ℕ, 𝔠 ^ n • (⊤ : Submodule R₂ (R₂ ⊗[R₁] M₁)) := by
    refine Submodule.mem_iInf _ |>.mpr fun n ↦ ?_
    -- every element is congruent to a pure tensor `1 ⊗ m` modulo `𝔠ⁿ`
    have happ : ∀ y : R₂ ⊗[R₁] M₁, ∃ m : M₁,
        y - (1 : R₂) ⊗ₜ m ∈ 𝔠 ^ n • (⊤ : Submodule R₂ (R₂ ⊗[R₁] M₁)) := by
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul b m =>
        obtain ⟨c, hc⟩ := happrox n b
        refine ⟨c • m, ?_⟩
        have hEq : b ⊗ₜ[R₁] m - (1 : R₂) ⊗ₜ[R₁] (c • m) =
            (b - algebraMap R₁ R₂ c) • ((1 : R₂) ⊗ₜ[R₁] m) := by
          rw [sub_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
            smul_eq_mul, mul_one, mul_one, ← TensorProduct.smul_tmul,
            Algebra.algebraMap_eq_smul_one]
        rw [hEq]
        exact Submodule.smul_mem_smul hc Submodule.mem_top
      | add y y' hy hy' =>
        obtain ⟨m, hm⟩ := hy
        obtain ⟨m', hm'⟩ := hy'
        refine ⟨m + m', ?_⟩
        rw [TensorProduct.tmul_add, add_sub_add_comm]
        exact Submodule.add_mem _ hm hm'
    obtain ⟨m, hm⟩ := happ x
    have hπ : π (x - (1 : R₂) ⊗ₜ m) ∈ 𝔠 ^ n • (⊤ : Submodule R₂ M₂) := by
      have := Submodule.mem_map_of_mem (f := π) hm
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have hπm : π₀ m ∈ 𝔠 ^ n • (⊤ : Submodule R₂ M₂) := by
      rwa [map_sub, hx, zero_sub, Submodule.neg_mem_iff, LinearMap.liftBaseChange_tmul,
        one_smul] at hπ
    have hm₁ := hmod n m hπm
    have h1m : (1 : R₂) ⊗ₜ[R₁] m ∈ 𝔠 ^ n • (⊤ : Submodule R₂ (R₂ ⊗[R₁] M₁)) := by
      refine Submodule.smul_induction_on hm₁ (fun c hc m' _ ↦ ?_) (fun m₁ m₂ h₁ h₂ ↦ ?_)
      · rw [TensorProduct.tmul_smul, ← algebraMap_smul R₂ c]
        refine Submodule.smul_mem_smul ?_ Submodule.mem_top
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hc
      · rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ h₁ h₂
    rw [← sub_add_cancel x ((1 : R₂) ⊗ₜ m)]
    exact Submodule.add_mem _ hm h1m
  rwa [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ hjac, Submodule.mem_bot] at hall

/-- **Comparison of two-term complexes.** If `R₂ ⊗ M₁ → M₂` is bijective and intertwines
`R₂ ⊗ d₁` with `d₂`, then the kernel of `R₂ ⊗ d₁` embeds in the kernel of `d₂`, and the base
change of the cokernel of `d₁` is the cokernel of `d₂`. -/
theorem baseChange_twoTerm {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R₁ M₁] [AddCommGroup M₂]
    [Module R₂ M₂] {r : ℕ} (d₁ : M₁ →ₗ[R₁] (Fin r → R₁)) (d₂ : M₂ →ₗ[R₂] (Fin r → R₂))
    (π : R₂ ⊗[R₁] M₁ →ₗ[R₂] M₂) (hπ : Function.Bijective π)
    (hsq : ∀ x, d₂ (π x) = freeBaseChangeEquiv R₁ R₂ r (d₁.baseChange R₂ x)) :
    (∀ (p : Ideal R₂) [p.IsPrime],
      Subsingleton (LocalizedModule p.primeCompl (LinearMap.ker d₂)) →
        Subsingleton (LocalizedModule p.primeCompl (LinearMap.ker (d₁.baseChange R₂)))) ∧
      Nonempty (R₂ ⊗[R₁] ((Fin r → R₁) ⧸ LinearMap.range d₁) ≃ₗ[R₂]
        (Fin r → R₂) ⧸ LinearMap.range d₂) := by
  refine ⟨fun p _ h ↦ ?_, ?_⟩
  · let f : LinearMap.ker (d₁.baseChange R₂) →ₗ[R₂] LinearMap.ker d₂ :=
      π.restrict fun x hx ↦ by
        rw [LinearMap.mem_ker] at hx ⊢
        rw [hsq, hx, map_zero]
    have hf : Function.Injective f := fun x y hxy ↦
      Subtype.ext (hπ.1 (congrArg Subtype.val hxy))
    exact (LocalizedModule.map_injective p.primeCompl f hf).subsingleton
  · obtain ⟨hsurj, hex⟩ := surjective_and_exact_baseChange_mkQ_range R₂ d₁
    let e₁ := hex.linearEquivOfSurjective hsurj
    have hrange : (LinearMap.range (d₁.baseChange R₂)).map
        (freeBaseChangeEquiv R₁ R₂ r : R₂ ⊗[R₁] (Fin r → R₁) →ₗ[R₂] (Fin r → R₂)) =
        LinearMap.range d₂ := by
      rw [← LinearMap.range_comp]
      have hcomp : (freeBaseChangeEquiv R₁ R₂ r : R₂ ⊗[R₁] (Fin r → R₁) →ₗ[R₂] (Fin r → R₂)) ∘ₗ
          d₁.baseChange R₂ = d₂ ∘ₗ π := LinearMap.ext fun x ↦ (hsq x).symm
      rw [hcomp, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hπ.2)]
    exact ⟨e₁.symm.trans (Submodule.Quotient.equiv _ _ (freeBaseChangeEquiv R₁ R₂ r) hrange)⟩

end Conormal

/-! ### The primes containing `I`: the completion along `I` -/

section CompletionCase

open AdicFiniteTypeAlgebra CompletedPolynomialPresentation

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {a : A}
  {B' : AdicFiniteTypeAlgebra.{u, u} A (Ideal.span {a})} {B : AdicFiniteTypeAlgebra.{u, u} A I}
  [Algebra B'.carrier B.carrier] [IsScalarTower A B'.carrier B.carrier]

omit [IsNoetherianRing A] in
/-- `(a) ⊆ I`, in the form of Stacks Remark 0AL5 with exponent `1`. -/
theorem map_span_pow_one_le (ha : a ∈ I) : ((Ideal.span {a}) ^ 1).map (algebraMap A A) ≤ I := by
  rwa [pow_one, Algebra.algebraMap_self, Ideal.map_id, Ideal.span_le, Set.singleton_subset_iff]

omit [IsNoetherianRing A] in
/-- If `B' → B` is surjective modulo `I`, then `B` is spanned over `A` by the image of `B'`
modulo `I B`. -/
theorem top_le_span_range_sup
    (hθ : IsBijectiveMod (I ^ 1) (IsScalarTower.toAlgHom A B'.carrier B.carrier)) :
    (⊤ : Submodule A B.carrier) ≤
      Submodule.span A (Set.range (algebraMap B'.carrier B.carrier)) ⊔
        Submodule.restrictScalars A B.adicIdeal := by
  intro y _
  obtain ⟨x, hx⟩ := hθ.1 y
  rw [← add_sub_cancel (algebraMap B'.carrier B.carrier x) y]
  refine Submodule.add_mem_sup (Submodule.subset_span ⟨x, rfl⟩) ?_
  rwa [pow_one] at hx

omit [IsNoetherianRing A] in
/-- The ideal `I B` is generated by the image of `I B'`. -/
theorem map_adicIdeal_eq (J : Ideal A) :
    (J.map (algebraMap A B'.carrier)).map (algebraMap B'.carrier B.carrier) =
      J.map (algebraMap A B.carrier) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **`B` is flat over `B'`.** A map `B' → B` into an `I`-adically complete ring which is
bijective modulo every power of `I` identifies `B` with the `I`-adic completion of the
Noetherian ring `B'`, which is flat over `B'`. -/
theorem flat_of_isBijectiveMod
    (hθ : ∀ n, IsBijectiveMod (I ^ n) (IsScalarTower.toAlgHom A B'.carrier B.carrier)) :
    Module.Flat B'.carrier B.carrier := by
  set K := I.map (algebraMap A B'.carrier)
  set f := algebraMap B'.carrier B.carrier
  have hK : K.map f = B.adicIdeal := map_adicIdeal_eq I
  have hKn : ∀ n, (K ^ n).map f = (I ^ n).map (algebraMap A B.carrier) := fun n ↦ by
    rw [← Ideal.map_pow, map_adicIdeal_eq]
  have hbij : ∀ n, Function.Bijective
      (Ideal.quotientMap ((K ^ n).map f) f Ideal.le_comap_map) := by
    intro n
    refine ⟨Ideal.quotientMap_injective' fun x hx ↦ ?_, fun z ↦ ?_⟩
    · rw [Ideal.mem_comap, hKn] at hx
      rw [← Ideal.map_pow]
      exact (hθ n).2 x hx
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨x, hx⟩ := (hθ n).1 y
      refine ⟨Ideal.Quotient.mk _ x, ?_⟩
      rw [Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem, hKn, ← neg_sub]
      exact (Ideal.neg_mem_iff _).2 hx
  have : IsAdicComplete (K.map f) B.carrier := by rw [hK]; exact B.isAdicallyComplete
  let e₁ : AdicCompletion K B'.carrier ≃+* AdicCompletion (K.map f) B.carrier :=
    RingEquiv.ofBijective _
      (Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective f K hbij)
  let E : AdicCompletion K B'.carrier ≃+* B.carrier :=
    e₁.trans (AdicCompletion.ofAlgEquiv (K.map f)).symm.toRingEquiv
  have hE : ∀ x : B'.carrier, E (algebraMap B'.carrier (AdicCompletion K B'.carrier) x) = f x := by
    intro x
    have h := DFunLike.congr_fun
      (_root_.adicCompletionMap_comp_algebraMap f K (K.map f) le_rfl) x
    simp only [RingHom.comp_apply] at h
    change (AdicCompletion.ofAlgEquiv (K.map f)).symm (e₁ _) = f x
    rw [show e₁ (algebraMap B'.carrier (AdicCompletion K B'.carrier) x) =
      _root_.adicCompletionMap f K (K.map f) le_rfl
        (algebraMap B'.carrier (AdicCompletion K B'.carrier) x) from rfl, h,
      AlgEquiv.symm_apply_eq]
    rfl
  let E' : AdicCompletion K B'.carrier ≃ₐ[B'.carrier] B.carrier := AlgEquiv.ofRingEquiv hE
  exact Module.Flat.of_linearEquiv E'.symm.toLinearEquiv

/-- **A prime of `B` over a prime of `B'` lying in a maximal ideal which contains `I`.** -/
theorem exists_liesOver_of_le_maximal
    (hθ : ∀ n, IsBijectiveMod (I ^ n) (IsScalarTower.toAlgHom A B'.carrier B.carrier))
    (q : Ideal B'.carrier) [q.IsPrime] (m : Ideal B'.carrier) [m.IsMaximal] (hqm : q ≤ m)
    (hIm : I.map (algebraMap A B'.carrier) ≤ m) :
    ∃ q' : Ideal B.carrier, q'.IsPrime ∧ q'.LiesOver q := by
  set f := algebraMap B'.carrier B.carrier
  have h1 := hθ 1
  rw [pow_one] at h1
  -- `m B ≠ B`: every element of `m B` agrees with the image of an element of `m` modulo `I B`
  have hne : m.map f ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx, h⟩ := exists_mem_sub_mem_of_mem_map_of_approx (algebraMap B'.carrier B.carrier)
      _ h1.1 m (htop ▸ Submodule.mem_top : (1 : B.carrier) ∈ m.map f)
    rw [← map_one f, ← map_sub] at h
    have := h1.2 (1 - x) h
    exact (Ideal.IsMaximal.ne_top ‹_›) ((Ideal.eq_top_iff_one _).mpr
      (by simpa using m.add_mem (hIm this) hx))
  obtain ⟨m', hm', hle⟩ := Ideal.exists_le_maximal _ hne
  have hcomap : m = m'.comap f :=
    Ideal.IsMaximal.eq_of_le ‹_› (Ideal.comap_ne_top _ hm'.ne_top)
      (Ideal.map_le_iff_le_comap.mp hle)
  have := flat_of_isBijectiveMod hθ
  have : m'.IsPrime := hm'.isPrime
  have : m'.LiesOver m := ⟨hcomap⟩
  obtain ⟨P, -, hP, hPq⟩ := Ideal.exists_ideal_le_liesOver_of_le m' hqm
  exact ⟨P, hP, hPq⟩

/-- **The primes of `B'` seen by `B`.** Let `B'` be `a`-adically complete with `a ∈ I`, and let
`B' → B` be bijective modulo every power of `I`, with `B` rig-smooth over `(A, I)`. For a prime `q`
of `B'` under a prime `q'` of `B` off `V(I B)`, the localization at `q` of `H⁻¹(NL^∧_{B'/A})`
vanishes and that of `H⁰(NL^∧_{B'/A})` is free.

The compatible presentation of Stacks 0GAG computes `NL^∧_{B/A}` as `NL^∧_{B'/A} ⊗_{B'} B`:
the comparison `J'/J'² ⊗_{B'} B → J/J²` is onto by 0GAG and injective by the Artin–Rees lemma
(`Rig.QuotientsLimit.mem_of_polynomialBaseChange_mem`), and both conclusions descend along the
flat local map `B'_q → B_{q'}`. -/
theorem localized_hneg_hzero_of_liesOver (ha : a ∈ I)
    (hθ : ∀ n, IsBijectiveMod (I ^ n) (IsScalarTower.toAlgHom A B'.carrier B.carrier))
    (hB : IsRigSmooth B) (r : ℕ) (g : Fin r → B'.carrier)
    (hgen : Function.Surjective (MvPolynomial.aeval
      (fun i ↦ Ideal.Quotient.mk B'.adicIdeal (g i)) :
        MvPolynomial (Fin r) (A ⧸ Ideal.span {a}) →ₐ[A ⧸ Ideal.span {a}] B'.reduction))
    (q : Ideal B'.carrier) [q.IsPrime] (q' : Ideal B.carrier) [q'.IsPrime] [q'.LiesOver q]
    (hq' : ¬ B.adicIdeal ≤ q') :
    Subsingleton (LocalizedModule q.primeCompl (completedNaiveCotangentComplex B'
        (ofGenerators B' r g (Ideal.fg_of_isNoetherianRing _) hgen)).Hneg) ∧
      Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl
        (completedNaiveCotangentComplex B'
          (ofGenerators B' r g (Ideal.fg_of_isNoetherianRing _) hgen)).Hzero) := by
  have hI₁ : (Ideal.span {a}).FG := Ideal.fg_of_isNoetherianRing _
  have hI : I.FG := Ideal.fg_of_isNoetherianRing I
  have hc : (0 : ℕ) < 1 := Nat.one_pos
  have hmap := map_span_pow_one_le ha
  have h12 : Ideal.span {a} ≤ I := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)
  have hspan := top_le_span_range_sup (hθ 1)
  have := flat_of_isBijectiveMod hθ
  set P₁ := ofGenerators B' r g hI₁ hgen with hP₁
  set P₂ := baseChangePresentation (B₁ := B') hI hc hmap hspan r g hgen with hP₂
  set K₁ := completedNaiveCotangentComplex B' P₁ with hK₁
  set K₂ := completedNaiveCotangentComplex B P₂ with hK₂
  set β := polynomialBaseChange hmap r with hβ
  -- `J₂` is generated by the image of `J₁`
  have hlevel : ∀ (n : ℕ) (p : MvPolynomial (Fin r) A),
      completedAeval B r (fun i ↦ algebraMap B'.carrier B.carrier (g i))
          (algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I r) p) ∈
            B.adicIdeal ^ n →
        algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I r) p ∈
          Ideal.map (polynomialBaseChange hmap r).toRingHom
              (RingHom.ker (completedAeval B' r g).toRingHom) ⊔
            (I.map (algebraMap A (completedPolynomialAlgebra I r))) ^ n := by
    intro n p hp
    rw [completedAeval_algebraMap] at hp
    have hθp : IsScalarTower.toAlgHom A B'.carrier B.carrier (MvPolynomial.aeval g p) ∈
        (I ^ n).map (algebraMap A B.carrier) := by
      rw [MvPolynomial.comp_aeval_apply, Ideal.map_pow]
      exact hp
    have hp' := (hθ n).2 _ hθp
    have hmapP : (I ^ n).map (algebraMap A B'.carrier) =
        ((I.map (algebraMap A (completedPolynomialAlgebra (Ideal.span {a}) r))) ^ n).map
          (completedAeval B' r g) := by
      rw [← Ideal.map_pow]
      exact (map_map_algebraMap (I ^ n) (completedAeval B' r g)).symm
    rw [hmapP] at hp'
    obtain ⟨y, hy, hyeq⟩ := (Ideal.mem_map_iff_of_surjective _
      (completedAeval_surjective B' r g hI₁ hgen)).mp hp'
    have hker₁ : algebraMap (MvPolynomial (Fin r) A)
        (completedPolynomialAlgebra (Ideal.span {a}) r) p - y ∈
          RingHom.ker (completedAeval B' r g).toRingHom := by
      rw [RingHom.mem_ker]
      change completedAeval B' r g _ = 0
      rw [map_sub, completedAeval_algebraMap, hyeq, sub_self]
    have hβy : β y ∈ (I.map (algebraMap A (completedPolynomialAlgebra I r))) ^ n := by
      rw [← map_polynomialBaseChange_map hmap r, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hy
    have hsplit : algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra I r) p =
        β (algebraMap (MvPolynomial (Fin r) A)
          (completedPolynomialAlgebra (Ideal.span {a}) r) p - y) + β y := by
      rw [map_sub, sub_add_cancel, hβ, polynomialBaseChange_algebraMap_self]
    rw [hsplit]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hker₁) hβy
  have hker : P₂.extension.ker ≤
      Ideal.map (baseChangeExtensionHom hI₁ hI hc hmap hspan r g hgen).toRingHom
        P₁.extension.ker := by
    rw [ker_extension_baseChangePresentation hI hc hmap hspan r g hgen,
      ker_extension_ofGenerators hI₁ r g hgen]
    exact ker_le_map_ker_of_polynomial_level hI hmap r g hlevel
  -- the comparison of conormal modules
  set π₀ := baseChangeCotangentMap hI₁ hI hc hmap hspan r g hgen with hπ₀
  set π := π₀.liftBaseChange B.carrier with hπ
  have : Module.Finite B'.carrier P₁.extension.Cotangent := finite_extension_cotangent B' P₁
  have := B.isAdicallyComplete
  have hπsurj : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, hπ, LinearMap.range_liftBaseChange]
    exact span_range_baseChangeCotangentMap_eq_top hI₁ hI hc hmap hspan r g hgen hker
  have hπinj : Function.Injective π := by
    refine injective_liftBaseChange_of_mem_smul π₀ (I.map (algebraMap A B'.carrier)) ?_ ?_ ?_
    · rw [map_adicIdeal_eq]
      exact IsAdicComplete.le_jacobson_bot _
    · intro n y
      obtain ⟨x, hx⟩ := (hθ n).1 y
      refine ⟨x, ?_⟩
      rwa [map_adicIdeal_eq, ← Ideal.map_pow]
    · intro n m hm
      obtain ⟨z, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective m
      have hz₂ : β z.1 ∈ P₂.extension.ker :=
        map_ker_le_ker_baseChangePresentation hI₁ hI hc hmap hspan r g hgen
          (Ideal.mem_map_of_mem _ z.2)
      rw [hπ₀, baseChangeCotangentMap_mk hI₁ hI hc hmap hspan r g hgen z hz₂] at hm
      have hpow₂ : (I.map (algebraMap A B'.carrier)).map (algebraMap B'.carrier B.carrier) ^ n =
          ((I.map (algebraMap A P₂.extension.Ring)) ^ n).map
            (algebraMap P₂.extension.Ring B.carrier) := by
        rw [map_adicIdeal_eq, Ideal.map_pow, Ideal.map_map,
          ← IsScalarTower.algebraMap_eq A P₂.extension.Ring B.carrier]
      rw [hpow₂, cotangent_mk_mem_smul_top_iff] at hm
      have hz₁ := mem_of_polynomialBaseChange_mem hmap r hI₁ hI h12 P₁.extension.ker
        P₂.extension.ker hker n z.2 hm
      have hpow₁ : (I.map (algebraMap A B'.carrier)) ^ n =
          ((I.map (algebraMap A P₁.extension.Ring)) ^ n).map
            (algebraMap P₁.extension.Ring B'.carrier) := by
        rw [Ideal.map_pow, Ideal.map_map,
          ← IsScalarTower.algebraMap_eq A P₁.extension.Ring B'.carrier]
      rw [hpow₁, cotangent_mk_mem_smul_top_iff]
      exact hz₁
  -- the comparison square
  have hsqL : (K₂.differential ∘ₗ π : _ →ₗ[B.carrier] (Fin r → B.carrier)) =
      (freeBaseChangeEquiv B'.carrier B.carrier r).toLinearMap ∘ₗ
        K₁.differential.baseChange B.carrier := by
    refine LinearMap.ext fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      have h1 : K₂.differential (π (b ⊗ₜ m)) =
          b • fun i ↦ algebraMap B'.carrier B.carrier (K₁.differential m i) := by
        rw [hπ, LinearMap.liftBaseChange_tmul, map_smul, hπ₀,
          baseChange_differential hI₁ hI hc hmap hspan r g hgen K₁ K₂ m]
        rfl
      have h2 : freeBaseChangeEquiv B'.carrier B.carrier r
          (K₁.differential.baseChange B.carrier (b ⊗ₜ m)) =
            b • fun i ↦ algebraMap B'.carrier B.carrier (K₁.differential m i) := by
        rw [LinearMap.baseChange_tmul]
        exact freeBaseChangeEquiv_tmul b (K₁.differential m)
      exact h1.trans h2.symm
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsq : ∀ x, K₂.differential (π x) =
      freeBaseChangeEquiv B'.carrier B.carrier r (K₁.differential.baseChange B.carrier x) :=
    fun x ↦ LinearMap.congr_fun hsqL x
  obtain ⟨hnegT, ⟨e⟩⟩ := baseChange_twoTerm K₁.differential K₂.differential π
    ⟨hπinj, hπsurj⟩ hsq
  obtain ⟨hneg₂, hzero₂⟩ :=
    subsingleton_hneg_and_free_hzero_localizedAtPrime_of_isRigSmooth B P₂ hB q' hq'
  have hflat : let := Localization.AtPrime.algebraOfLiesOver q q'
      Module.Flat (Localization.AtPrime q) (Localization.AtPrime q') := by
    let := Localization.AtPrime.algebraOfLiesOver q q'
    infer_instance
  refine ⟨PointwiseDescent.localized_descent q q' hflat K₁.differential (hnegT q' hneg₂), ?_⟩
  have : Module.Finite B'.carrier K₁.Hzero := Module.Finite.quotient _ _
  refine (PointwiseDescent.localized_free_descent (M := K₁.Hzero) q q' hflat).2 ?_
  have hmem : (⟨q', inferInstance⟩ : PrimeSpectrum B.carrier) ∈
      Module.freeLocus B.carrier K₂.Hzero := Module.mem_freeLocus.mpr hzero₂
  have hmem' : (⟨q', inferInstance⟩ : PrimeSpectrum B.carrier) ∈
      Module.freeLocus B.carrier (B.carrier ⊗[B'.carrier] K₁.Hzero) := by
    rw [Module.freeLocus_congr e]
    exact hmem
  exact Module.mem_freeLocus.mp hmem'

end CompletionCase

/-! ### Reduction of a completed polynomial algebra modulo `aⁿ⁺¹` -/

section Reduction

variable {A : Type u} [CommRing A] (a : A) (r k : ℕ)

/-- The ideal generated by `aᵏ⁺¹` in `A[x]^∧_{(a)}` is the `(k+1)`-st power of the ideal generated
by `a`. -/
theorem map_span_pow_eq (R : Type*) [CommRing R] [Algebra A R] :
    ((Ideal.span {a}).map (algebraMap A R)) ^ (k + 1) =
      (Ideal.span {a ^ (k + 1)}).map (algebraMap A R) := by
  rw [← Ideal.map_pow, Ideal.span_singleton_pow]

/-- Every element of `A[x]^∧_{(a)}` is a polynomial modulo `aᵏ⁺¹`. -/
theorem exists_sub_algebraMap_mem (x : completedPolynomialAlgebra (Ideal.span {a}) r) :
    ∃ p : MvPolynomial (Fin r) A,
      x - algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra (Ideal.span {a}) r) p ∈
        (Ideal.span {a ^ (k + 1)}).map
          (algebraMap A (completedPolynomialAlgebra (Ideal.span {a}) r)) := by
  have hfg : (Ideal.span {a} : Ideal A).FG := Submodule.fg_span_singleton a
  obtain ⟨p, hp⟩ := AdicCompletion.exists_sub_mem_map_pow
    ((Ideal.span {a}).map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
    (hfg.map _) (k + 1) x
  refine ⟨p, ?_⟩
  rwa [Ideal.map_pow, map_coeffIdeal_eq, map_span_pow_eq] at hp

/-- An element of `(c)` is a multiple of `c`. -/
theorem exists_mul_of_mem_map_span {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {c : R}
    {x : S} (hx : x ∈ (Ideal.span {c}).map f) : ∃ y, x = y * f c := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩

/-- Reduction of polynomials modulo `aᵏ⁺¹` kills the `(k+1)`-st power of the coefficient ideal. -/
theorem mapAlgHom_eq_zero_of_mem (p : MvPolynomial (Fin r) A)
    (hp : p ∈ ((Ideal.span {a}).map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) ^ (k + 1)) :
    MvPolynomial.mapAlgHom (Algebra.ofId A (A ⧸ Ideal.span {a ^ (k + 1)})) p = 0 := by
  rw [← Ideal.map_pow, Ideal.span_singleton_pow] at hp
  have hker : RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {a ^ (k + 1)})) :
      MvPolynomial (Fin r) A →+* _) = (Ideal.span {a ^ (k + 1)}).map MvPolynomial.C := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [← hker] at hp
  exact hp

/-- The reduction `A[x]^∧_{(a)} → (A ⧸ aᵏ⁺¹)[x]`. -/
def reduction :
    completedPolynomialAlgebra (Ideal.span {a}) r →ₐ[A]
      MvPolynomial (Fin r) (A ⧸ Ideal.span {a ^ (k + 1)}) :=
  (Ideal.Quotient.liftₐ (((Ideal.span {a}).map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) ^
      (k + 1)) (MvPolynomial.mapAlgHom (Algebra.ofId A (A ⧸ Ideal.span {a ^ (k + 1)})))
      (mapAlgHom_eq_zero_of_mem a r k)).comp
    ((AdicCompletion.evalₐ ((Ideal.span {a}).map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
      (k + 1)).restrictScalars A)

/-- On polynomials, the reduction is reduction of coefficients. -/
theorem reduction_algebraMap (p : MvPolynomial (Fin r) A) :
    reduction a r k
        (algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra (Ideal.span {a}) r) p) =
      MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {a ^ (k + 1)})) p := by
  simp [reduction, AdicCompletion.algebraMap_apply]

/-- The reduction kills `aᵏ⁺¹`. -/
theorem reduction_eq_zero_of_mem {x : completedPolynomialAlgebra (Ideal.span {a}) r}
    (hx : x ∈ (Ideal.span {a ^ (k + 1)}).map
      (algebraMap A (completedPolynomialAlgebra (Ideal.span {a}) r))) :
    reduction a r k x = 0 := by
  obtain ⟨y, rfl⟩ := exists_mul_of_mem_map_span _ hx
  rw [map_mul, AlgHom.commutes, IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span {a ^ (k + 1)}),
    Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero, mul_zero]

/-- The reduction is surjective. -/
theorem reduction_surjective : Function.Surjective (reduction a r k) := by
  intro p
  obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective p
  exact ⟨_, reduction_algebraMap a r k p⟩

/-- The kernel of the reduction is generated by `aᵏ⁺¹`. -/
theorem ker_reduction_le :
    RingHom.ker (reduction a r k) ≤ (Ideal.span {a ^ (k + 1)}).map
      (algebraMap A (completedPolynomialAlgebra (Ideal.span {a}) r)) := by
  intro x hx
  obtain ⟨p, hp⟩ := exists_sub_algebraMap_mem a r k x
  have h0 : reduction a r k
      (algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra (Ideal.span {a}) r) p) =
        0 := by
    have := reduction_eq_zero_of_mem a r k hp
    rwa [map_sub, RingHom.mem_ker.mp hx, zero_sub, neg_eq_zero] at this
  rw [reduction_algebraMap] at h0
  have hpk : p ∈ (Ideal.span {a ^ (k + 1)}).map MvPolynomial.C := by
    rw [← Ideal.mk_ker (I := Ideal.span {a ^ (k + 1)}), ← MvPolynomial.ker_map]
    exact h0
  have hpk' := Ideal.mem_map_of_mem
    (algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra (Ideal.span {a}) r)) hpk
  rw [map_coeffIdeal_eq] at hpk'
  rw [← sub_add_cancel x (algebraMap (MvPolynomial (Fin r) A)
    (completedPolynomialAlgebra (Ideal.span {a}) r) p)]
  exact Ideal.add_mem _ hp hpk'

/-- The reduction commutes with the formal partial derivatives. -/
theorem pderiv_reduction (i : Fin r)
    (D : Derivation A (completedPolynomialAlgebra (Ideal.span {a}) r)
      (completedPolynomialAlgebra (Ideal.span {a}) r))
    (hD : ∀ p : MvPolynomial (Fin r) A,
      D (algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra (Ideal.span {a}) r) p) =
        algebraMap (MvPolynomial (Fin r) A) (completedPolynomialAlgebra (Ideal.span {a}) r)
          (MvPolynomial.pderiv i p))
    (x : completedPolynomialAlgebra (Ideal.span {a}) r) :
    MvPolynomial.pderiv i (reduction a r k x) = reduction a r k (D x) := by
  obtain ⟨p, hp⟩ := exists_sub_algebraMap_mem a r k x
  obtain ⟨y, hy⟩ := exists_mul_of_mem_map_span _ hp
  have hx : x = algebraMap (MvPolynomial (Fin r) A)
      (completedPolynomialAlgebra (Ideal.span {a}) r) p +
        y * algebraMap A (completedPolynomialAlgebra (Ideal.span {a}) r) (a ^ (k + 1)) := by
    rw [← hy, add_sub_cancel]
  have hz : reduction a r k (algebraMap A (completedPolynomialAlgebra (Ideal.span {a}) r)
      (a ^ (k + 1))) = 0 :=
    reduction_eq_zero_of_mem a r k (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))
  rw [hx, map_add (reduction a r k), map_mul (reduction a r k), hz, mul_zero, add_zero,
    map_add D, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, zero_add, smul_eq_mul,
    map_add (reduction a r k), map_mul (reduction a r k), hz, zero_mul, add_zero,
    hD, reduction_algebraMap, reduction_algebraMap, MvPolynomial.pderiv_map]

end Reduction

/-! ### The primes not containing `I`: the smooth quotients -/

section SmoothCase

open AdicFiniteTypeAlgebra CompletedPolynomialPresentation Algebra.Extension

attribute [local implicit_reducible] CompletedPolynomialPresentation.extension
  Algebra.Extension.ofSurjective

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {a : A}
  {B' : AdicFiniteTypeAlgebra.{u, u} A (Ideal.span {a})}

/-- **The primes of `B'` off `V(I)`.** Let `m` be a prime of `B'` containing `a` but not `I`,
and suppose every `B' ⧸ aⁿ⁺¹` is isomorphic to a finite type `A ⧸ aⁿ⁺¹`-algebra which is smooth
over `Spec(A ⧸ aⁿ⁺¹) ∖ V(I)`. Then multiplication by some `s ∉ m` on `J / J²` factors through
the differential of `NL^∧_{B'/A}`.

Take `n` beyond the Artin–Rees exponent of `J ⊆ A[x]^∧` for `(a)`. Smoothness of `B' ⧸ aⁿ⁺¹`
at `m` splits the differential of its polynomial presentation after inverting some `t ∉ m`
(`Rig.not_retractionIdeal_le_of_smoothAt`); the comparison `J / J² → J̄ / J̄²` with that
presentation is onto with kernel in `a · J / J²` by the Artin–Rees lemma, so a lift `ψ` of the
splitting satisfies `ψ ∘ d ≡ t` modulo `a`, and the determinant trick
(`Rig.QuotientsLimit.exists_mem_cotangentFactorizationIdeal_notMem`) produces `s`. -/
theorem exists_mem_cotangentFactorizationIdeal_of_smoothAwayFrom (r : ℕ)
    (g : Fin r → B'.carrier)
    (hgen : Function.Surjective (MvPolynomial.aeval
      (fun i ↦ Ideal.Quotient.mk B'.adicIdeal (g i)) :
        MvPolynomial (Fin r) (A ⧸ Ideal.span {a}) →ₐ[A ⧸ Ideal.span {a}] B'.reduction))
    (m : Ideal B'.carrier) [m.IsPrime] (ham : algebraMap A B'.carrier a ∈ m)
    (hIm : ¬ I.map (algebraMap A B'.carrier) ≤ m)
    (hsm : ∀ n, ∃ (C : Type u) (_ : CommRing C) (_ : Algebra (A ⧸ Ideal.span {a ^ (n + 1)}) C)
       (_ : Algebra A C) (_ : IsScalarTower A (A ⧸ Ideal.span {a ^ (n + 1)}) C),
       Algebra.FiniteType (A ⧸ Ideal.span {a ^ (n + 1)}) C ∧
       SmoothAwayFrom (A ⧸ Ideal.span {a ^ (n + 1)}) (I.map (Ideal.Quotient.mk _)) C ∧
       Nonempty ((B'.carrier ⧸ (Ideal.span {a ^ (n + 1)}).map (algebraMap A B'.carrier)) ≃ₐ[A]
         C)) :
    ∃ s ∈ cotangentFactorizationIdeal (completedNaiveCotangentComplex B'
        (ofGenerators B' r g (Ideal.fg_of_isNoetherianRing _) hgen)).differential, s ∉ m := by
  have hI₁ : (Ideal.span {a}).FG := Ideal.fg_of_isNoetherianRing _
  set P₁ := ofGenerators B' r g hI₁ hgen with hP₁
  set K₁ := completedNaiveCotangentComplex B' P₁ with hK₁
  have : IsNoetherianRing (completedPolynomialAlgebra (Ideal.span {a}) r) :=
    AdicCompletion.isNoetherianRing _
  set 𝔞 : Ideal (completedPolynomialAlgebra (Ideal.span {a}) r) :=
    (Ideal.span {a}).map (algebraMap A (completedPolynomialAlgebra (Ideal.span {a}) r)) with h𝔞
  set J₁ : Ideal (completedPolynomialAlgebra (Ideal.span {a}) r) :=
    RingHom.ker (completedAeval B' r g).toRingHom with hJ₁
  have hJ₁P : P₁.extension.ker = J₁ := ker_extension_ofGenerators hI₁ r g hgen
  obtain ⟨k, hk⟩ := exists_mem_mul_of_mem_pow 𝔞 J₁
  obtain ⟨C, _, _, _, _, -, hsmooth, ⟨e⟩⟩ := hsm k
  set Aₙ := A ⧸ Ideal.span {a ^ (k + 1)}
  -- the map `B' → B' ⧸ aᵏ⁺¹ ≅ C`
  set φ : B'.carrier →+* C := e.toRingHom.comp (Ideal.Quotient.mk _) with hφ
  have hφsurj : Function.Surjective φ := e.surjective.comp Ideal.Quotient.mk_surjective
  have hφA : ∀ x : A, φ (algebraMap A B'.carrier x) = algebraMap A C x := by
    intro x
    change e (Ideal.Quotient.mk _ (algebraMap A B'.carrier x)) = _
    rw [Ideal.Quotient.mk_algebraMap, AlgEquiv.commutes]
  have hkerφ : RingHom.ker φ = (Ideal.span {a ^ (k + 1)}).map (algebraMap A B'.carrier) := by
    ext x
    rw [RingHom.mem_ker]
    change e (Ideal.Quotient.mk _ x) = 0 ↔ _
    rw [map_eq_zero_iff e e.injective, Ideal.Quotient.eq_zero_iff_mem]
  let : Algebra B'.carrier C := φ.toAlgebra
  have : IsScalarTower A B'.carrier C := IsScalarTower.of_algebraMap_eq fun x ↦ (hφA x).symm
  have hφalg : algebraMap B'.carrier C = φ := rfl
  -- the reduction of the completed polynomial algebra
  set ρ := reduction a r k with hρ
  have hcompat : ∀ x, MvPolynomial.aeval (fun i ↦ φ (g i)) (ρ x) =
      φ (completedAeval B' r g x) := by
    intro x
    obtain ⟨p, hp⟩ := exists_sub_algebraMap_mem a r k x
    have hδ : completedAeval B' r g (x - algebraMap (MvPolynomial (Fin r) A)
        (completedPolynomialAlgebra (Ideal.span {a}) r) p) ∈ RingHom.ker φ := by
      rw [hkerφ, ← map_map_algebraMap _ (completedAeval B' r g)]
      exact Ideal.mem_map_of_mem _ hp
    have hρδ := reduction_eq_zero_of_mem a r k hp
    rw [map_sub, sub_eq_zero] at hρδ
    rw [map_sub, RingHom.mem_ker, map_sub, sub_eq_zero] at hδ
    rw [hρδ, hδ, reduction_algebraMap, completedAeval_algebraMap,
      ← Ideal.Quotient.algebraMap_eq, MvPolynomial.aeval_map_algebraMap]
    exact (MvPolynomial.comp_aeval_apply g (IsScalarTower.toAlgHom A B'.carrier C) p).symm
  have hGsurj : Function.Surjective
      (MvPolynomial.aeval (R := Aₙ) (fun i ↦ φ (g i))) := by
    intro c
    obtain ⟨b, rfl⟩ := hφsurj c
    obtain ⟨x, rfl⟩ := completedAeval_surjective B' r g hI₁ hgen b
    exact ⟨ρ x, hcompat x⟩
  set G : Algebra.Generators Aₙ C (Fin r) := .ofSurjective (fun i ↦ φ (g i)) hGsurj with hG
  have hGval : ∀ y, algebraMap G.Ring C y = MvPolynomial.aeval (fun i ↦ φ (g i)) y := fun y ↦
    G.algebraMap_apply y
  -- the map of extensions
  let f : P₁.extension.Hom G.toExtension :=
    { toRingHom := ρ.toRingHom
      toRingHom_algebraMap := fun x ↦ by
        change ρ (algebraMap A (completedPolynomialAlgebra (Ideal.span {a}) r) x) = _
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A Aₙ (MvPolynomial (Fin r) Aₙ)]
        rfl
      algebraMap_toRingHom := fun x ↦ by
        change algebraMap G.Ring C (ρ x) = φ (P₁.toAlgHom x)
        exact (hGval _).trans ((hcompat x).trans (congrArg φ
          (DFunLike.congr_fun (ofGenerators_toAlgHom B' r g hI₁ hgen) x)).symm) }
  set πₙ := Cotangent.map f with hπₙ
  have hπₙ_mk : ∀ (z : P₁.extension.ker) (hz : ρ z.1 ∈ G.toExtension.ker),
      πₙ (Cotangent.mk z) = Cotangent.mk ⟨ρ z.1, hz⟩ := fun z _ ↦ Cotangent.map_mk f z
  have hmemG : ∀ z ∈ J₁, ρ z ∈ G.toExtension.ker := by
    intro z hz
    change ρ z ∈ RingHom.ker (algebraMap G.Ring C)
    rw [RingHom.mem_ker, hGval]
    exact (hcompat z).trans ((congrArg φ (RingHom.mem_ker.mp hz)).trans (map_zero φ))
  -- `J̄ = ρ(J₁)`
  have hJG : G.toExtension.ker ≤ J₁.map ρ := by
    intro w hw
    obtain ⟨x, rfl⟩ := reduction_surjective a r k w
    have hw' : algebraMap G.Ring C (ρ x) = 0 := hw
    have hx : φ (completedAeval B' r g x) = 0 := (hcompat x).symm.trans ((hGval _).symm.trans hw')
    have hx' : completedAeval B' r g x ∈ ((Ideal.span {a ^ (k + 1)}).map
        (algebraMap A (completedPolynomialAlgebra (Ideal.span {a}) r))).map
          (completedAeval B' r g :
            completedPolynomialAlgebra (Ideal.span {a}) r →+* B'.carrier) := by
      rwa [map_map_algebraMap, ← hkerφ]
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective _
      (completedAeval_surjective B' r g hI₁ hgen)).mp hx'
    have hxy : x - y ∈ J₁ := by
      rw [hJ₁, RingHom.mem_ker]
      change completedAeval B' r g (x - y) = 0
      rw [map_sub, sub_eq_zero]
      exact hyx.symm
    have : ρ x = ρ (x - y) := by rw [map_sub, reduction_eq_zero_of_mem a r k hy, sub_zero]
    rw [this]
    exact Ideal.mem_map_of_mem _ hxy
  have hπsurj : Function.Surjective πₙ := by
    intro y
    obtain ⟨w, rfl⟩ := Cotangent.mk_surjective y
    obtain ⟨z, hz, hzw⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (reduction_surjective a r k)).mp (hJG w.2)
    have hzP : z ∈ P₁.extension.ker := by rwa [hJ₁P]
    refine ⟨Cotangent.mk ⟨z, hzP⟩, ?_⟩
    rw [hπₙ_mk ⟨z, hzP⟩ (hmemG z hz)]
    congr 1
    exact Subtype.ext hzw
  have hkerπ' : ∀ (z : completedPolynomialAlgebra (Ideal.span {a}) r) (hzP : z ∈ P₁.extension.ker),
      ρ z ∈ G.toExtension.ker ^ 2 → Cotangent.mk (⟨z, hzP⟩ : P₁.extension.ker) ∈
        ((Ideal.span {a}).map (algebraMap A B'.carrier)) •
          (⊤ : Submodule B'.carrier P₁.extension.Cotangent) := by
    intro z hzP hx
    have hzJ : z ∈ J₁ := by rwa [← hJ₁P]
    have hx2 : ρ z ∈ (J₁ ^ 2).map ρ := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hJG 2 hx
    obtain ⟨h, hh, hhz⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (reduction_surjective a r k)).mp hx2
    have hzh : z - h ∈ 𝔞 ^ (k + 1) := by
      rw [h𝔞, map_span_pow_eq]
      apply ker_reduction_le a r k
      rw [RingHom.mem_ker, map_sub, hhz, sub_self]
    have hAR : z - h ∈ 𝔞 * J₁ := by
      rw [← pow_one 𝔞]
      exact hk 1 _ (J₁.sub_mem hzJ (Ideal.pow_le_self two_ne_zero hh)) hzh
    have hz' : z ∈ 𝔞 * J₁ + J₁ ^ 2 := by
      rw [← sub_add_cancel z h]
      exact Submodule.add_mem_sup hAR hh
    have := (cotangent_mk_mem_smul_top_iff P₁.extension 𝔞 ⟨z, hzP⟩).mpr
      (by change z ∈ _; rw [hJ₁P]; exact hz')
    have hmapeq : 𝔞.map (algebraMap P₁.extension.Ring B'.carrier) =
        (Ideal.span {a}).map (algebraMap A B'.carrier) :=
      map_map_algebraMap (Ideal.span {a}) P₁.toAlgHom
    rw [← hmapeq]
    exact this
  have hkerπ : ∀ x, πₙ x = 0 → x ∈ ((Ideal.span {a}).map (algebraMap A B'.carrier)) •
      (⊤ : Submodule B'.carrier P₁.extension.Cotangent) := by
    intro x hx
    obtain ⟨⟨z, hzP⟩, rfl⟩ := Cotangent.mk_surjective x
    have hzJ : z ∈ J₁ := by rwa [← hJ₁P]
    rw [hπₙ_mk ⟨z, hzP⟩ (hmemG z hzJ), Cotangent.mk_eq_zero_iff] at hx
    exact hkerπ' z hzP hx
  -- smoothness of `C` at the image of `m`
  have hkerm : RingHom.ker φ ≤ m := by
    rw [hkerφ, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap A B'.carrier (a ^ (k + 1)) ∈ m
    rw [map_pow]
    exact Ideal.pow_mem_of_mem _ ham _ (Nat.succ_pos k)
  set 𝔪 := m.map φ with h𝔪
  have h𝔪p : 𝔪.IsPrime := Ideal.map_isPrime_of_surjective hφsurj hkerm
  have hcomap : 𝔪.comap φ = m := by
    rw [h𝔪, Ideal.comap_map_of_surjective _ hφsurj, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkerm]
  have hnot : ¬ (I.map (Ideal.Quotient.mk (Ideal.span {a ^ (k + 1)}))).map
      (algebraMap Aₙ C) ≤ 𝔪 := by
    intro hle
    apply hIm
    rw [← hcomap, Ideal.map_le_iff_le_comap]
    intro y hy
    change φ (algebraMap A B'.carrier y) ∈ 𝔪
    rw [hφA, IsScalarTower.algebraMap_apply A Aₙ C, Ideal.Quotient.algebraMap_eq]
    exact hle (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hy))
  have hSA := hsmooth 𝔪 h𝔪p hnot
  obtain ⟨t, ht, ht𝔪⟩ :=
    IsConcreteLE.not_le_iff_exists.mp (not_retractionIdeal_le_of_smoothAt G 𝔪 hSA)
  obtain ⟨ψG, hψG⟩ := ht
  have hψG' : ∀ y, ψG (presentationDifferential G y) = t • y := fun y ↦ LinearMap.congr_fun hψG y
  obtain ⟨t', rfl⟩ := hφsurj t
  have ht' : t' ∉ m := fun h ↦ ht𝔪 (Ideal.mem_map_of_mem φ h)
  -- the comparison square
  have hpd : ∀ (z : completedPolynomialAlgebra (Ideal.span {a}) r) (i : Fin r),
      MvPolynomial.aeval (fun i ↦ φ (g i)) (MvPolynomial.pderiv i (ρ z)) =
        φ (completedAeval B' r g (K₁.partialDeriv i z)) := by
    intro z i
    rw [pderiv_reduction a r k i (K₁.partialDeriv i) (K₁.partialDeriv_polynomial i), hcompat]
    rfl
  have hsqB : ∀ x, presentationDifferential G (πₙ x) = fun i ↦ φ (K₁.differential x i) := by
    intro x
    obtain ⟨z, rfl⟩ := Cotangent.mk_surjective x
    have hzJ : z.1 ∈ J₁ := hJ₁P ▸ z.2
    funext i
    rw [hπₙ_mk z (hmemG z.1 hzJ), presentationDifferential_mk, K₁.differential_mk, hGval]
    change MvPolynomial.aeval _ (MvPolynomial.pderiv i (ρ z.1)) =
      φ (P₁.toAlgHom (K₁.partialDeriv i z.1))
    exact (hpd z.1 i).trans
      (congrArg φ (DFunLike.congr_fun (ofGenerators_toAlgHom B' r g hI₁ hgen) _).symm)
  -- a lift of the splitting
  have hℓ : ∀ i : Fin r, ∃ ℓ, πₙ ℓ = ψG (Pi.single i 1) := fun i ↦ hπsurj _
  choose ℓ hℓ using hℓ
  set ψ : (Fin r → B'.carrier) →ₗ[B'.carrier] P₁.extension.Cotangent :=
    ∑ i, (LinearMap.proj i).smulRight (ℓ i) with hψ
  have hψapp : ∀ v, πₙ (ψ v) = ψG (fun i ↦ φ (v i)) := by
    intro v
    have hv : (fun i ↦ φ (v i)) = ∑ i, φ (v i) • (Pi.single i 1 : Fin r → C) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum, hψ, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.smulRight_apply, LinearMap.proj_apply, map_smul, hℓ, map_smul, ← hφalg,
      algebraMap_smul]
  have hmain : ∀ x, ψ (K₁.differential x) - t' • x ∈
      ((Ideal.span {a}).map (algebraMap A B'.carrier)) •
        (⊤ : Submodule B'.carrier P₁.extension.Cotangent) := by
    intro x
    apply hkerπ
    rw [map_sub, (hψapp (K₁.differential x)).trans (congrArg ψG (hsqB x).symm), hψG', map_smul,
      ← algebraMap_smul C t' (πₙ x),
      hφalg, sub_self]
  have : Module.Finite B'.carrier P₁.extension.Cotangent := finite_extension_cotangent B' P₁
  have h𝔞m : (Ideal.span {a}).map (algebraMap A B'.carrier) ≤ m := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff]
    exact ham
  exact exists_mem_cotangentFactorizationIdeal_notMem K₁.differential ψ t' _ hmain m h𝔞m ht'

end SmoothCase

end QuotientsLimit

open AdicFiniteTypeAlgebra CompletedPolynomialPresentation

/-- **Rig-smoothness from smooth quotients and a rig-smooth completion** (the smoothening lemma
in the proof of [Gabber–Zavyalov, Theorem 1.2], cited in Stacks Remark 0GAX). Let `A` be a
Noetherian ring, `I ⊆ A` an ideal and `a ∈ I`. Let `B'` be an `a`-adically complete `A`-algebra
of finite type modulo `a`, and `θ : B' → B` a map into an object `B` of Stacks 0AL4 over
`(A, I)` which is bijective modulo every power of `I` (so `B` is the `I`-adic completion of
`B'`). If `B` is rig-smooth over `(A, I)` and every `B' ⧸ aⁿ⁺¹` is isomorphic to a finite type
`A ⧸ aⁿ⁺¹`-algebra which is smooth over `Spec(A ⧸ aⁿ⁺¹) ∖ V(I)`, then `B'` is rig-smooth over
`(A, (a))`.

By Stacks 0GAJ read at a single prime (`Rig.isRigSmooth_of_forall_prime`) it suffices to show,
at every prime `q` of `B'` not containing `a`, that `H⁻¹(NL^∧_{B'/A})_q = 0` and that
`H⁰(NL^∧_{B'/A})_q` is free. Choose a maximal ideal `m ⊇ q`; it contains `a`. If `I B' ⊆ m`,
then `q` lies under a prime of `B` off `V(I B)` and both conclusions descend from `B`
(`Rig.QuotientsLimit.localized_hneg_hzero_of_liesOver`). Otherwise the smoothness of the
quotients at `m` and the Artin–Rees lemma split the differential of `NL^∧_{B'/A}` after
inverting an element outside `m`
(`Rig.QuotientsLimit.exists_mem_cotangentFactorizationIdeal_of_smoothAwayFrom`). -/
public theorem isRigSmooth_of_isBijectiveMod_of_smoothAwayFrom_quotients
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {a : A} (ha : a ∈ I)
    (B' : AdicFiniteTypeAlgebra.{u, u} A (Ideal.span {a}))
    (B : AdicFiniteTypeAlgebra.{u, u} A I) (hB : IsRigSmooth B)
    (θ : B'.carrier →ₐ[A] B.carrier) (hθ : ∀ n, IsBijectiveMod (I ^ n) θ)
    (hsm : ∀ n, ∃ (C : Type u) (_ : CommRing C) (_ : Algebra (A ⧸ Ideal.span {a ^ (n + 1)}) C)
       (_ : Algebra A C) (_ : IsScalarTower A (A ⧸ Ideal.span {a ^ (n + 1)}) C),
       Algebra.FiniteType (A ⧸ Ideal.span {a ^ (n + 1)}) C ∧
       SmoothAwayFrom (A ⧸ Ideal.span {a ^ (n + 1)}) (I.map (Ideal.Quotient.mk _)) C ∧
       Nonempty ((B'.carrier ⧸ (Ideal.span {a ^ (n + 1)}).map (algebraMap A B'.carrier)) ≃ₐ[A]
         C)) :
    IsRigSmooth B' := by
  let : Algebra B'.carrier B.carrier := θ.toRingHom.toAlgebra
  have : IsScalarTower A B'.carrier B.carrier :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (θ.commutes x).symm
  have hθ' : ∀ n, IsBijectiveMod (I ^ n) (IsScalarTower.toAlgHom A B'.carrier B.carrier) := by
    have : IsScalarTower.toAlgHom A B'.carrier B.carrier = θ := AlgHom.ext fun _ ↦ rfl
    rw [this]
    exact hθ
  obtain ⟨r, g, hgen⟩ := exists_generating_family B'
  refine isRigSmooth_of_forall_prime B'
    (ofGenerators B' r g (Ideal.fg_of_isNoetherianRing _) hgen) fun q _ hq ↦ ?_
  have haq : algebraMap A B'.carrier a ∉ q := fun h ↦ hq
    (Ideal.map_le_iff_le_comap.mpr (by rwa [Ideal.span_le, Set.singleton_subset_iff]))
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q (Ideal.IsPrime.ne_top ‹_›)
  have ham : algebraMap A B'.carrier a ∈ m := by
    have := B'.isAdicallyComplete
    have hjac := IsAdicComplete.le_jacobson_bot (I := B'.adicIdeal) (R := B'.carrier)
    have hle : (⊥ : Ideal B'.carrier).jacobson ≤ m := sInf_le ⟨bot_le, hm⟩
    exact hle (hjac (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self a)))
  by_cases hIm : I.map (algebraMap A B'.carrier) ≤ m
  · obtain ⟨q', hq'p, hq'⟩ := QuotientsLimit.exists_liesOver_of_le_maximal hθ' q m hqm hIm
    have hq'I : ¬ B.adicIdeal ≤ q' := by
      intro hle
      apply haq
      have hmem : algebraMap A B.carrier a ∈ q' := hle (Ideal.mem_map_of_mem _ ha)
      rw [IsScalarTower.algebraMap_apply A B'.carrier B.carrier] at hmem
      rw [Ideal.over_def q' q, Ideal.under, Ideal.mem_comap]
      exact hmem
    exact QuotientsLimit.localized_hneg_hzero_of_liesOver ha hθ' hB r g hgen q q' hq'I
  · obtain ⟨s, hs, hsm'⟩ :=
      QuotientsLimit.exists_mem_cotangentFactorizationIdeal_of_smoothAwayFrom r g hgen m ham hIm hsm
    exact QuotientsLimit.subsingleton_ker_and_free_coker_of_mem _ hs q fun h ↦ hsm' (hqm h)

end Rig

end
