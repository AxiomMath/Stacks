module

public import StacksFrontier.RingTheory.Smooth.Conormal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The completion of a smooth algebra along a section, compatibly with the section

Let `S` be a smooth `R`-algebra with an `R`-algebra section `σ : S → R`, let `I = Ker(σ)`, and
suppose the conormal module `I/I²` is free, with a basis given by the classes of `t₁, …, t_d ∈ I`.
Evaluation `X_i ↦ t_i` induces `R`-algebra isomorphisms `R[X] ⧸ (X)ⁿ ≃ S ⧸ Iⁿ` for every `n`,
compatible with the transition maps, and hence an isomorphism `S^∧ ≃ R[[X_1, …, X_d]]` of the
`I`-adic completion with the power series ring under which `σ` becomes the constant coefficient.
This is part (2) of [Stacks, Tag 05D5], together with the compatibility with the section.

## Main results

* `exists_adicCompletion_algEquiv_mvPowerSeries_constantCoeff`: the isomorphism
  `S^∧ ≃ₐ[R] R[[X_1, …, X_d]]` carrying `σ` to the constant coefficient.
* `exists_algEquiv_quotient_pow_idealOfVars_mk_eq`: the isomorphisms of truncations, for a formally
  smooth `S`.

## References

* [Stacks Project, Tag 05D5](https://stacks.math.columbia.edu/tag/05D5)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public section

open MvPolynomial

/-- Evaluating polynomials at elements of an ideal `I` carries the `n`-th power of the ideal of
the variables into `Iⁿ`. -/
theorem MvPolynomial.map_aeval_pow_idealOfVars_le {R S ι : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal S) (t : ι → S) (ht : ∀ i, t i ∈ I) (n : ℕ) :
    (idealOfVars ι R ^ n).map (aeval t) ≤ I ^ n := by
  rw [Ideal.map_pow]
  refine Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr ?_)) n
  rintro _ ⟨i, rfl⟩
  simpa using ht i

/-- Let `φ` be a ring endomorphism preserving an ideal `J` and congruent to the identity modulo
`Jⁿ`, with `n ≥ 2`. Then `φ` is congruent to the identity modulo `Jⁿ⁺¹` on `Jⁿ`. -/
theorem Ideal.sub_mem_pow_succ_of_forall_sub_mem_pow {P : Type*} [CommRing P] (J : Ideal P)
    (φ : P →+* P) (hφJ : ∀ x ∈ J, φ x ∈ J) {n : ℕ} (hn : 2 ≤ n)
    (hφ : ∀ x, φ x - x ∈ J ^ n) : ∀ f ∈ J ^ n, φ f - f ∈ J ^ (n + 1) := by
  have hpow : ∀ k, ∀ y ∈ J ^ k, φ y ∈ J ^ k := by
    intro k y hy
    have hle : (J ^ k).map φ ≤ J ^ k := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hφJ) k
    exact hle (Ideal.mem_map_of_mem φ hy)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro f hf
  rw [pow_succ'] at hf
  refine Submodule.mul_induction_on hf ?_ ?_
  · intro x hx y hy
    have h1 : (φ x - x) * φ y ∈ J ^ (m + 1 + 1) := by
      have := Ideal.mul_mem_mul (hφ x) (hpow m y hy)
      rw [← pow_add] at this
      exact Ideal.pow_le_pow_right (by omega) this
    have h2 : x * (φ y - y) ∈ J ^ (m + 1 + 1) := by
      have := Ideal.mul_mem_mul hx (hφ y)
      rwa [← pow_succ'] at this
    have : φ (x * y) - x * y = (φ x - x) * φ y + x * (φ y - y) := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.add_mem _ h1 h2
  · intro a b ha hb
    rw [map_add, add_sub_add_comm]
    exact Ideal.add_mem _ ha hb

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →ₐ[R] R)
variable {ι : Type*} [Finite ι]

/-- If the classes of `t_i ∈ I = Ker(σ)` form a basis of `I/I²`, every element of `I` is an
`R`-linear combination of the `t_i` modulo `I²`. -/
theorem exists_mem_idealOfVars_sub_aeval_mem_ker_sq
    (b : Module.Basis ι R (RingHom.ker σ).Cotangent) (t : ι → S)
    (ht : ∀ i, ∃ hi : t i ∈ RingHom.ker σ, (RingHom.ker σ).toCotangent ⟨t i, hi⟩ = b i)
    (x : S) (hx : x ∈ RingHom.ker σ) :
    ∃ q ∈ idealOfVars ι R, x - aeval t q ∈ RingHom.ker σ ^ 2 := by
  have := Fintype.ofFinite ι
  let I := RingHom.ker σ
  have hti : ∀ i, t i ∈ I := fun i => (ht i).1
  let c := b.repr (I.toCotangent ⟨x, hx⟩)
  let z : I := ∑ i, c i • (⟨t i, hti i⟩ : I)
  have hz : I.toCotangent z = I.toCotangent ⟨x, hx⟩ := by
    simp only [z, map_sum, LinearMap.map_smul_of_tower]
    conv_rhs => rw [← b.sum_repr (I.toCotangent ⟨x, hx⟩)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(ht i).2]
  refine ⟨∑ i, c i • (X i : MvPolynomial ι R), Ideal.sum_mem _ fun i _ =>
    Submodule.smul_of_tower_mem _ (c i) (Ideal.subset_span ⟨i, rfl⟩), ?_⟩
  have hzval : ((z : I) : S) = aeval t (∑ i, c i • (X i : MvPolynomial ι R)) := by
    simp [z, map_sum]
  rw [← hzval]
  exact (Ideal.toCotangent_eq I).mp hz.symm

/-- If the classes of `t_i ∈ I = Ker(σ)` form a basis of `I/I²`, then every element of `Iⁿ` is,
modulo `Iⁿ⁺¹`, the value at `t` of a polynomial in the `n`-th power of the ideal of variables. -/
theorem exists_mem_pow_idealOfVars_sub_aeval_mem_ker_pow_succ
    (b : Module.Basis ι R (RingHom.ker σ).Cotangent) (t : ι → S)
    (ht : ∀ i, ∃ hi : t i ∈ RingHom.ker σ, (RingHom.ker σ).toCotangent ⟨t i, hi⟩ = b i) :
    ∀ (n : ℕ) (x : S), x ∈ RingHom.ker σ ^ n →
      ∃ q ∈ idealOfVars ι R ^ n, x - aeval t q ∈ RingHom.ker σ ^ (n + 1) := by
  let I := RingHom.ker σ
  have hti : ∀ i, t i ∈ I := fun i => (ht i).1
  intro n
  induction n with
  | zero =>
    intro x _
    refine ⟨C (σ x), by simp, ?_⟩
    rw [zero_add, pow_one, aeval_C, RingHom.mem_ker, map_sub, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm m' hm'
      obtain ⟨q, hq, hmq⟩ := ih m hm
      obtain ⟨q', hq', hmq'⟩ := exists_mem_idealOfVars_sub_aeval_mem_ker_sq σ b t ht m' hm'
      refine ⟨q * q', by rw [pow_succ]; exact Ideal.mul_mem_mul hq hq', ?_⟩
      have haq : aeval t q ∈ I ^ n :=
        MvPolynomial.map_aeval_pow_idealOfVars_le I t hti n (Ideal.mem_map_of_mem _ hq)
      have h1 : (m - aeval t q) * m' ∈ I ^ (n + 1 + 1) := by
        have := Ideal.mul_mem_mul hmq hm'
        rwa [← pow_succ] at this
      have h2 : aeval t q * (m' - aeval t q') ∈ I ^ (n + 1 + 1) := by
        have := Ideal.mul_mem_mul haq hmq'
        rwa [← pow_add] at this
      have : m * m' - aeval t (q * q') = (m - aeval t q) * m' + aeval t q * (m' - aeval t q') := by
        rw [map_mul]; ring
      rw [this]
      exact Ideal.add_mem _ h1 h2
    · rintro a b ⟨qa, hqa, ha⟩ ⟨qb, hqb, hb⟩
      refine ⟨qa + qb, Ideal.add_mem _ hqa hqb, ?_⟩
      rw [map_add, add_sub_add_comm]
      exact Ideal.add_mem _ ha hb

/-- If the classes of `t_i ∈ I = Ker(σ)` span `I/I²`, then `S` is generated by the `t_i` modulo
every power of `I`. -/
theorem exists_sub_aeval_mem_ker_pow
    (b : Module.Basis ι R (RingHom.ker σ).Cotangent) (t : ι → S)
    (ht : ∀ i, ∃ hi : t i ∈ RingHom.ker σ, (RingHom.ker σ).toCotangent ⟨t i, hi⟩ = b i)
    (n : ℕ) (x : S) : ∃ p : MvPolynomial ι R, x - aeval t p ∈ RingHom.ker σ ^ n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, -, hq⟩ := exists_mem_pow_idealOfVars_sub_aeval_mem_ker_pow_succ σ b t ht n _ hp
    exact ⟨p + q, by rwa [map_add, ← sub_sub]⟩

/-- If the classes of `t_i ∈ I = Ker(σ)` are linearly independent in `I/I²` and a polynomial `p`
has value at `t` in `I²`, then `p` lies in the square of the ideal of variables. -/
theorem mem_idealOfVars_sq_of_aeval_mem_ker_sq
    (b : Module.Basis ι R (RingHom.ker σ).Cotangent) (t : ι → S)
    (ht : ∀ i, ∃ hi : t i ∈ RingHom.ker σ, (RingHom.ker σ).toCotangent ⟨t i, hi⟩ = b i)
    (p : MvPolynomial ι R) (hp : aeval t p ∈ RingHom.ker σ ^ 2) :
    p ∈ idealOfVars ι R ^ 2 := by
  classical
  have := Fintype.ofFinite ι
  let I := RingHom.ker σ
  have hti : ∀ i, t i ∈ I := fun i => (ht i).1
  have hσ : ∀ q : MvPolynomial ι R, σ (aeval t q) = constantCoeff q := by
    intro q
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have : (fun i => σ (t i)) = 0 := funext fun i => hti i
    rw [this, aeval_zero, Algebra.algebraMap_self, RingHom.id_apply]
  have hp0 : constantCoeff p = 0 := by
    rw [← hσ]
    exact Ideal.pow_le_self two_ne_zero hp
  let c : ι → R := fun i => coeff (Finsupp.single i 1) p
  let q := p - ∑ i, c i • (X i : MvPolynomial ι R)
  have hdeg : ∀ x : ι →₀ ℕ, x.degree < 2 → x = 0 ∨ ∃ i, x = Finsupp.single i 1 := by
    intro x hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h | h
    · left
      exact (Finsupp.degree_eq_zero_iff x).mp (by omega)
    · right
      have hmem : x ∈ {d : ι →₀ ℕ | d.degree = 1} := h
      rw [← Finsupp.range_single_one] at hmem
      obtain ⟨i, rfl⟩ := hmem
      exact ⟨i, rfl⟩
  have hq : q ∈ idealOfVars ι R ^ 2 := by
    rw [mem_pow_idealOfVars_iff']
    intro x hx
    rcases hdeg x hx with rfl | ⟨j, rfl⟩
    · have h0 : coeff 0 p = 0 := (congrFun constantCoeff_eq p).symm.trans hp0
      simp [q, coeff_sum, coeff_X', h0]
    · simp only [q, coeff_sub, coeff_sum, coeff_smul, coeff_X', smul_eq_mul, mul_ite, mul_one,
        mul_zero, Finsupp.single_left_inj one_ne_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, c, sub_self]
  have hlin : aeval t (∑ i, c i • (X i : MvPolynomial ι R)) ∈ I ^ 2 := by
    have hq2 : aeval t q ∈ I ^ 2 :=
      MvPolynomial.map_aeval_pow_idealOfVars_le I t hti 2 (Ideal.mem_map_of_mem _ hq)
    have : aeval t (∑ i, c i • (X i : MvPolynomial ι R)) = aeval t p - aeval t q := by
      simp only [q, map_sub, sub_sub_cancel]
    rw [this]
    exact Ideal.sub_mem _ hp hq2
  let z : I := ∑ i, c i • (⟨t i, hti i⟩ : I)
  have hz0 : I.toCotangent z = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    simpa [z, map_sum, Submodule.coe_sum] using hlin
  have hsum : ∑ i, c i • b i = 0 := by
    rw [← hz0]
    simp only [z, map_sum, LinearMap.map_smul_of_tower]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(ht i).2]
  have hc : ∀ i, c i = 0 := (Fintype.linearIndependent_iff.mp b.linearIndependent) c hsum
  rwa [show q = p by simp [q, hc]] at hq

/-- **Inverse of the truncated comparison maps.** Let `S` be formally smooth over `R`, with a
section `σ` whose kernel `I` has conormal module with basis the classes of `t_i ∈ I`. For every
`n` there is an `R`-algebra map `S → R[X] ⧸ (X)ⁿ⁺²` sending `t_i` to `X_i` and `I` into `(X)`. -/
theorem exists_algHom_quotient_pow_idealOfVars [Algebra.FormallySmooth R S]
    (b : Module.Basis ι R (RingHom.ker σ).Cotangent) (t : ι → S)
    (ht : ∀ i, ∃ hi : t i ∈ RingHom.ker σ, (RingHom.ker σ).toCotangent ⟨t i, hi⟩ = b i)
    (n : ℕ) :
    ∃ h : S →ₐ[R] MvPolynomial ι R ⧸ idealOfVars ι R ^ (n + 2),
      (∀ i, h (t i) = Ideal.Quotient.mk _ (X i)) ∧
      ∀ s ∈ RingHom.ker σ,
        h s ∈ (idealOfVars ι R).map (Ideal.Quotient.mk (idealOfVars ι R ^ (n + 2))) := by
  have hti : ∀ i, t i ∈ RingHom.ker σ := fun i => (ht i).1
  induction n with
  | zero =>
    let Ψ : MvPolynomial ι R ⧸ idealOfVars ι R ^ 2 →ₐ[R] S ⧸ RingHom.ker σ ^ 2 :=
      Ideal.quotientMapₐ (RingHom.ker σ ^ 2) (aeval t)
        (Ideal.map_le_iff_le_comap.mp
          (MvPolynomial.map_aeval_pow_idealOfVars_le (RingHom.ker σ) t hti 2))
    have hΨ : ∀ p, Ψ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval t p) := fun _ => rfl
    have hinj : Function.Injective Ψ := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [hΨ, Ideal.Quotient.eq_zero_iff_mem] at ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (mem_idealOfVars_sq_of_aeval_mem_ker_sq σ b t ht p ha)
    have hsurj : Function.Surjective Ψ := by
      intro a
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨p, hp⟩ := exists_sub_aeval_mem_ker_pow σ b t ht 2 s
      exact ⟨Ideal.Quotient.mk _ p, by rw [hΨ]; exact (Ideal.Quotient.eq.mpr hp).symm⟩
    let e := AlgEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
    refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R (RingHom.ker σ ^ 2)), fun i => ?_,
      fun s hs => ?_⟩
    · show e.symm (Ideal.Quotient.mk _ (t i)) = _
      rw [AlgEquiv.symm_apply_eq]
      show _ = Ψ (Ideal.Quotient.mk _ (X i))
      rw [hΨ, aeval_X]
    · obtain ⟨q, hq, hsq⟩ := exists_mem_idealOfVars_sub_aeval_mem_ker_sq σ b t ht s hs
      have : e.symm (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ q := by
        rw [AlgEquiv.symm_apply_eq]
        show _ = Ψ (Ideal.Quotient.mk _ q)
        rw [hΨ]
        exact Ideal.Quotient.eq.mpr hsq
      show e.symm (Ideal.Quotient.mk _ s) ∈ _
      rw [this]
      exact Ideal.mem_map_of_mem _ hq
  | succ n ih =>
    obtain ⟨h, hht, hhI⟩ := ih
    have hle : idealOfVars ι R ^ (n + 2 + 1) ≤ idealOfVars ι R ^ (n + 2) :=
      Ideal.pow_le_pow_right (Nat.le_succ _)
    let K : Ideal (MvPolynomial ι R ⧸ idealOfVars ι R ^ (n + 2 + 1)) :=
      (idealOfVars ι R ^ (n + 2)).map (Ideal.Quotient.mkₐ R (idealOfVars ι R ^ (n + 2 + 1)))
    have hK : IsNilpotent K := by
      refine ⟨2, ?_⟩
      show K ^ 2 = ⊥
      rw [← Ideal.map_pow, ← pow_mul, Ideal.map_eq_bot_iff_le_ker]
      intro x hx
      show Ideal.Quotient.mkₐ R (idealOfVars ι R ^ (n + 2 + 1)) x = 0
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_pow_right (by omega) hx
    let δ := DoubleQuot.quotQuotEquivQuotOfLEₐ R hle
    let g : S →ₐ[R] (MvPolynomial ι R ⧸ idealOfVars ι R ^ (n + 2 + 1)) ⧸ K :=
      δ.symm.toAlgHom.comp h
    let h' := Algebra.FormallySmooth.lift K hK g
    have hh' : ∀ s, Ideal.Quotient.mk K (h' s) = δ.symm (h s) := fun s =>
      AlgHom.congr_fun (Algebra.FormallySmooth.comp_lift K hK g) s
    have hδ : ∀ p, δ.symm (Ideal.Quotient.mk _ p) =
        Ideal.Quotient.mk K (Ideal.Quotient.mk _ p) := fun p =>
      DoubleQuot.quotQuotEquivQuotOfLE_symm_mk p hle
    have hε : ∀ i, h' (t i) - Ideal.Quotient.mk _ (X i) ∈ K := by
      intro i
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hh', hht i, hδ, sub_self]
    have hmkK : Function.Surjective (Ideal.Quotient.mkₐ R (idealOfVars ι R ^ (n + 2 + 1))) :=
      Ideal.Quotient.mkₐ_surjective R _
    choose ε hεJ hεmk using fun i => (Ideal.mem_map_iff_of_surjective _ hmkK).mp (hε i)
    have hεJ1 : ∀ i, ε i ∈ idealOfVars ι R := fun i => Ideal.pow_le_self (by omega) (hεJ i)
    let β : MvPolynomial ι R →ₐ[R] MvPolynomial ι R := aeval fun i => X i - ε i
    have hβX : ∀ i, β (X i) = X i - ε i := fun i => aeval_X _ i
    have hXε : ∀ i, X i - ε i ∈ idealOfVars ι R := fun i =>
      Ideal.sub_mem _ (Ideal.subset_span ⟨i, rfl⟩) (hεJ1 i)
    have hβJ : ∀ k, (idealOfVars ι R ^ k).map β ≤ idealOfVars ι R ^ k := fun k =>
      MvPolynomial.map_aeval_pow_idealOfVars_le (idealOfVars ι R) _ hXε k
    have hβJ1 : ∀ x ∈ idealOfVars ι R, β x ∈ idealOfVars ι R := fun x hx => by
      simpa using hβJ 1 (by simpa using Ideal.mem_map_of_mem β hx)
    have hβN : ∀ x, β x - x ∈ idealOfVars ι R ^ (n + 2) := by
      intro x
      rw [← Ideal.Quotient.eq]
      have : (Ideal.Quotient.mkₐ R (idealOfVars ι R ^ (n + 2))).comp β =
          Ideal.Quotient.mkₐ R (idealOfVars ι R ^ (n + 2)) := by
        apply MvPolynomial.algHom_ext
        intro i
        rw [AlgHom.comp_apply, hβX, Ideal.Quotient.mkₐ_eq_mk, map_sub,
          Ideal.Quotient.eq_zero_iff_mem.mpr (hεJ i), sub_zero]
      exact AlgHom.congr_fun this x
    have hβε : ∀ i, β (ε i) - ε i ∈ idealOfVars ι R ^ (n + 2 + 1) :=
      fun i => Ideal.sub_mem_pow_succ_of_forall_sub_mem_pow (idealOfVars ι R) β.toRingHom
        hβJ1 (by omega) hβN (ε i) (hεJ i)
    let βbar : MvPolynomial ι R ⧸ idealOfVars ι R ^ (n + 2 + 1) →ₐ[R]
        MvPolynomial ι R ⧸ idealOfVars ι R ^ (n + 2 + 1) :=
      Ideal.quotientMapₐ (idealOfVars ι R ^ (n + 2 + 1)) β
        (Ideal.map_le_iff_le_comap.mp (hβJ (n + 2 + 1)))
    have hβbar : ∀ p, βbar (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (β p) := fun _ => rfl
    refine ⟨βbar.comp h', fun i => ?_, fun s hs => ?_⟩
    · have hti' : h' (t i) = Ideal.Quotient.mk _ (X i) + Ideal.Quotient.mk _ (ε i) := by
        have := hεmk i
        rw [Ideal.Quotient.mkₐ_eq_mk] at this
        rw [this, add_sub_cancel]
      have h1 : Ideal.Quotient.mk (idealOfVars ι R ^ (n + 2 + 1)) (β (ε i)) =
          Ideal.Quotient.mk _ (ε i) := Ideal.Quotient.eq.mpr (hβε i)
      rw [AlgHom.comp_apply, hti', map_add, hβbar, hβbar, h1, hβX, map_sub, sub_add_cancel]
    · obtain ⟨p, hpJ, hp⟩ := (Ideal.mem_map_iff_of_surjective _
        Ideal.Quotient.mk_surjective).mp (hhI s hs)
      have hdiff : h' s - Ideal.Quotient.mk _ p ∈ K := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hh', ← hp, hδ, sub_self]
      have hKJ : K ≤ (idealOfVars ι R).map
          (Ideal.Quotient.mkₐ R (idealOfVars ι R ^ (n + 2 + 1))) :=
        Ideal.map_mono (Ideal.pow_le_self (by omega))
      have hs' : h' s ∈ (idealOfVars ι R).map
          (Ideal.Quotient.mkₐ R (idealOfVars ι R ^ (n + 2 + 1))) := by
        have := Ideal.add_mem _ (hKJ hdiff)
          (Ideal.mem_map_of_mem (Ideal.Quotient.mkₐ R (idealOfVars ι R ^ (n + 2 + 1))) hpJ)
        rwa [Ideal.Quotient.mkₐ_eq_mk, sub_add_cancel] at this
      obtain ⟨r, hrJ, hr⟩ := (Ideal.mem_map_iff_of_surjective _ hmkK).mp hs'
      rw [AlgHom.comp_apply, ← hr, Ideal.Quotient.mkₐ_eq_mk, hβbar]
      exact Ideal.mem_map_of_mem _ (hβJ1 r hrJ)

/-- **The truncated comparison maps are isomorphisms.** Let `S` be formally smooth over `R`, with
a section `σ` whose kernel `I` has conormal module with basis the classes of `t_i ∈ I`. Then
evaluation `X_i ↦ t_i` induces an `R`-algebra isomorphism `R[X] ⧸ (X)ⁿ ≃ S ⧸ Iⁿ` for every `n`. -/
theorem exists_algEquiv_quotient_pow_idealOfVars_mk_eq [Algebra.FormallySmooth R S]
    (b : Module.Basis ι R (RingHom.ker σ).Cotangent) (t : ι → S)
    (ht : ∀ i, ∃ hi : t i ∈ RingHom.ker σ, (RingHom.ker σ).toCotangent ⟨t i, hi⟩ = b i)
    (n : ℕ) :
    ∃ e : (MvPolynomial ι R ⧸ idealOfVars ι R ^ n) ≃ₐ[R] (S ⧸ RingHom.ker σ ^ n),
      ∀ p, e (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval t p) := by
  have hti : ∀ i, t i ∈ RingHom.ker σ := fun i => (ht i).1
  let Ψ : MvPolynomial ι R ⧸ idealOfVars ι R ^ n →ₐ[R] S ⧸ RingHom.ker σ ^ n :=
    Ideal.quotientMapₐ (RingHom.ker σ ^ n) (aeval t)
      (Ideal.map_le_iff_le_comap.mp
        (MvPolynomial.map_aeval_pow_idealOfVars_le (RingHom.ker σ) t hti n))
  have hΨ : ∀ p, Ψ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval t p) := fun _ => rfl
  have hinj : Function.Injective Ψ := by
    obtain ⟨h, hht, hhI⟩ := exists_algHom_quotient_pow_idealOfVars σ b t ht n
    have hle : idealOfVars ι R ^ (n + 2) ≤ idealOfVars ι R ^ n :=
      Ideal.pow_le_pow_right (by omega)
    let h₀ : S →ₐ[R] MvPolynomial ι R ⧸ idealOfVars ι R ^ n :=
      (Ideal.Quotient.factorₐ R hle).comp h
    have hkill : ∀ s ∈ RingHom.ker σ ^ n, h₀ s = 0 := by
      intro s hs
      have hmap : (RingHom.ker σ ^ n).map h ≤
          (idealOfVars ι R ^ n).map (Ideal.Quotient.mk (idealOfVars ι R ^ (n + 2))) := by
        rw [Ideal.map_pow, Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hhI) n
      obtain ⟨p, hpJ, hp⟩ := (Ideal.mem_map_iff_of_surjective _
        Ideal.Quotient.mk_surjective).mp (hmap (Ideal.mem_map_of_mem h hs))
      show Ideal.Quotient.factor hle (h s) = 0
      rw [← hp, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hpJ
    let hbar : S ⧸ RingHom.ker σ ^ n →ₐ[R] MvPolynomial ι R ⧸ idealOfVars ι R ^ n :=
      Ideal.Quotient.liftₐ (RingHom.ker σ ^ n) h₀ hkill
    have hleft : hbar.comp Ψ = AlgHom.id R _ := by
      apply Ideal.Quotient.algHom_ext R
      apply MvPolynomial.algHom_ext
      intro i
      show hbar (Ψ (Ideal.Quotient.mk _ (X i))) = Ideal.Quotient.mk _ (X i)
      rw [hΨ, aeval_X]
      show Ideal.Quotient.factor hle (h (t i)) = _
      rw [hht, Ideal.Quotient.factor_mk]
    exact Function.LeftInverse.injective (g := hbar) fun a => AlgHom.congr_fun hleft a
  have hsurj : Function.Surjective Ψ := by
    intro a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨p, hp⟩ := exists_sub_aeval_mem_ker_pow σ b t ht n s
    exact ⟨Ideal.Quotient.mk _ p, by rw [hΨ]; exact (Ideal.Quotient.eq.mpr hp).symm⟩
  exact ⟨AlgEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, hΨ⟩

/-- A family of `R`-algebra isomorphisms `P ⧸ Jⁿ ≃ₐ[R] S ⧸ Iⁿ` compatible with the transition
maps of the two towers of quotients assembles into an `R`-algebra isomorphism of the `J`-adic and
the `I`-adic completion, which induces the given isomorphisms on the truncations. -/
theorem AdicCompletion.exists_algEquiv_evalₐ_eq_of_quotientPow
    {P S : Type*} [CommRing P] [CommRing S] [Algebra R P] [Algebra R S]
    (J : Ideal P) (I : Ideal S)
    (e : ∀ n, (P ⧸ J ^ n) ≃ₐ[R] (S ⧸ I ^ n))
    (hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (e n).toAlgHom
        = (e m).toAlgHom.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))) :
    ∃ F : AdicCompletion J P ≃ₐ[R] AdicCompletion I S,
      ∀ n x, AdicCompletion.evalₐ I n (F x) = e n (AdicCompletion.evalₐ J n x) := by
  have hevJ : ∀ {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion J P),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn : J ^ n ≤ J ^ m))
          ((AdicCompletion.evalₐ J n) x)
      = (AdicCompletion.evalₐ J m) x := by
    intro m n hmn x
    obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective J P x
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
    show (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) _ = _
    rw [Ideal.Quotient.factor_mk]
    exact AdicCompletion.Ideal.mk_eq_mk J hmn a
  have hevI : ∀ {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I S),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn : I ^ n ≤ I ^ m))
          ((AdicCompletion.evalₐ I n) x)
      = (AdicCompletion.evalₐ I m) x := by
    intro m n hmn x
    obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I S x
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
    show (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) _ = _
    rw [Ideal.Quotient.factor_mk]
    exact AdicCompletion.Ideal.mk_eq_mk I hmn a
  have hF : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
          ((e n).toAlgHom.comp ((AdicCompletion.evalₐ J n).restrictScalars R))
      = (e m).toAlgHom.comp ((AdicCompletion.evalₐ J m).restrictScalars R) := by
    intro m n hmn
    ext x
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom]
    have h1 := AlgHom.congr_fun (hcompat hmn) ((AdicCompletion.evalₐ J n) x)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at h1
    rw [h1]
    exact congrArg (e m) (hevJ hmn x)
  let F : AdicCompletion J P →ₐ[R] AdicCompletion I S :=
    AdicCompletion.liftAlgHom I
      (fun n => (e n).toAlgHom.comp ((AdicCompletion.evalₐ J n).restrictScalars R)) hF
  have hG : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
          ((e n).symm.toAlgHom.comp ((AdicCompletion.evalₐ I n).restrictScalars R))
      = (e m).symm.toAlgHom.comp ((AdicCompletion.evalₐ I m).restrictScalars R) := by
    intro m n hmn
    ext x
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom]
    have h1 := AlgHom.congr_fun (hcompat hmn) ((e n).symm ((AdicCompletion.evalₐ I n) x))
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] at h1
    rw [hevI hmn x] at h1
    apply (e m).injective
    rw [AlgEquiv.apply_symm_apply, ← h1]
  let G : AdicCompletion I S →ₐ[R] AdicCompletion J P :=
    AdicCompletion.liftAlgHom J
      (fun n => (e n).symm.toAlgHom.comp ((AdicCompletion.evalₐ I n).restrictScalars R)) hG
  refine ⟨AlgEquiv.ofAlgHom F G ?_ ?_, fun n x => ?_⟩
  · apply AlgHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    simp only [F, G, AlgHom.comp_apply, AlgHom.id_apply,
      AdicCompletion.evalₐ_liftAlgHom, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply]
  · apply AlgHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    simp only [F, G, AlgHom.comp_apply, AlgHom.id_apply,
      AdicCompletion.evalₐ_liftAlgHom, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply]
  · simp only [F, AlgEquiv.ofAlgHom_apply, AdicCompletion.evalₐ_liftAlgHom, AlgHom.comp_apply,
      AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom]


/-- If `S` is a smooth `R`-algebra, `σ : S →ₐ[R] R` and the conormal module `I/I²` of
`I = Ker(σ)` is free of rank `d`, there is an `R`-algebra isomorphism
`S^∧ ≃ₐ[R] R[[t_1, …, t_d]]` from the `I`-adic completion under which the section `σ` becomes the
constant coefficient: the composite `S → S^∧ ≃ R[[t]] → R` is `σ`. -/
@[sga "3 VIIB 5.5.2" "partial", sga "3 XI 1.2" "(ii), special case"]
theorem exists_adicCompletion_algEquiv_mvPowerSeries_constantCoeff (h : Algebra.Smooth R S)
    (hfree : Module.Free R (RingHom.ker σ).Cotangent) :
    ∃ e : AdicCompletion (RingHom.ker σ) S ≃ₐ[R]
        MvPowerSeries (Fin (Module.finrank R (RingHom.ker σ).Cotangent)) R,
      ∀ x : S, MvPowerSeries.constantCoeff (e (AdicCompletion.of (RingHom.ker σ) S x)) = σ x := by
  set d := Module.finrank R (RingHom.ker σ).Cotangent with hd
  have : Algebra.FormallySmooth R S := h.formallySmooth
  obtain ⟨b, t, ht⟩ : ∃ (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent) (t : Fin d → S),
      ∀ i, ∃ hi : t i ∈ RingHom.ker σ, (RingHom.ker σ).toCotangent ⟨t i, hi⟩ = b i := by
    have : Module.Finite R (RingHom.ker σ).Cotangent := (conormal_finite_projective σ h).left
    obtain hR | hR := subsingleton_or_nontrivial R
    · have : Subsingleton (RingHom.ker σ).Cotangent := Module.subsingleton R _
      let b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent :=
        ⟨{ toFun := 0, map_add' := fun _ _ => Subsingleton.elim _ _,
           map_smul' := fun _ _ => Subsingleton.elim _ _,
           invFun := 0, left_inv := fun _ => Subsingleton.elim _ _,
           right_inv := fun _ => Subsingleton.elim _ _ }⟩
      exact ⟨b, fun _ => 0, fun i => ⟨(RingHom.ker σ).zero_mem, Subsingleton.elim _ _⟩⟩
    · let b := Module.finBasis R (RingHom.ker σ).Cotangent
      have hsurj : Function.Surjective (RingHom.ker σ).toCotangent :=
        Ideal.toCotangent_surjective _
      choose u hu using fun i => hsurj (b i)
      refine ⟨b, fun i => (u i : S), fun i => ⟨(u i).property, ?_⟩⟩
      have : (⟨(u i : S), (u i).property⟩ : ↥(RingHom.ker σ)) = u i := Subtype.ext rfl
      rw [this]; exact hu i
  choose e he using exists_algEquiv_quotient_pow_idealOfVars_mk_eq σ b t ht
  have hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (e n).toAlgHom
      = (e m).toAlgHom.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)) := by
    intro m n hmn
    apply Ideal.Quotient.algHom_ext R
    apply MvPolynomial.algHom_ext
    intro i
    show Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
        (e n (Ideal.Quotient.mk (idealOfVars (Fin d) R ^ n) (X i))) =
      e m (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
        (Ideal.Quotient.mk (idealOfVars (Fin d) R ^ n) (X i)))
    rw [he, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, he]
  obtain ⟨E, hE⟩ := AdicCompletion.exists_algEquiv_evalₐ_eq_of_quotientPow _ _ e
    (fun {m n} hmn => hcompat hmn)
  let eMv : MvPowerSeries (Fin d) R ≃ₐ[R]
      AdicCompletion (idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) :=
    (MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) R).restrictScalars R
  refine ⟨E.symm.trans eMv.symm, ?_⟩
  have hI : ∀ y ∈ RingHom.ker σ, MvPowerSeries.constantCoeff
      ((E.symm.trans eMv.symm) (AdicCompletion.of (RingHom.ker σ) S y)) = 0 := by
    intro y hy
    set p := (E.symm.trans eMv.symm) (AdicCompletion.of (RingHom.ker σ) S y) with hp
    have hEp : E (eMv p) = AdicCompletion.of (RingHom.ker σ) S y := by
      rw [hp, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    have h1 : AdicCompletion.evalₐ (idealOfVars (Fin d) R) 1 (eMv p) = 0 := by
      apply (e 1).injective
      rw [← hE, hEp, AdicCompletion.evalₐ_of, map_zero, Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact hy
    have h2 : AdicCompletion.evalₐ (idealOfVars (Fin d) R) 1 (eMv p) =
        Ideal.Quotient.mk _ (MvPowerSeries.truncTotal 1 p) := by
      show AdicCompletion.evalₐ _ 1 (MvPowerSeries.toAdicCompletion (Fin d) R p) = _
      exact AdicCompletion.evalₐ_liftAlgHom _ _ (fun h ↦ AlgHom.ext fun _ ↦ by
        simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
          MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars h (le_refl _) _) 1 p
    rw [h2, Ideal.Quotient.eq_zero_iff_mem, pow_one] at h1
    have h3 := (MvPolynomial.mem_pow_idealOfVars_iff' 1 _).mp (by rwa [pow_one]) 0 (by simp)
    rw [MvPowerSeries.coeff_truncTotal _ (by simp)] at h3
    simpa using h3
  intro x
  have hx : x - algebraMap R S (σ x) ∈ RingHom.ker σ := by
    simp [RingHom.mem_ker]
  calc MvPowerSeries.constantCoeff
        ((E.symm.trans eMv.symm) (AdicCompletion.of (RingHom.ker σ) S x))
      = MvPowerSeries.constantCoeff ((E.symm.trans eMv.symm)
            (AdicCompletion.of (RingHom.ker σ) S (x - algebraMap R S (σ x)))) +
          MvPowerSeries.constantCoeff ((E.symm.trans eMv.symm)
            (AdicCompletion.of (RingHom.ker σ) S (algebraMap R S (σ x)))) := by
        rw [← map_add, ← map_add, ← map_add, sub_add_cancel]
    _ = σ x := by
        rw [hI _ hx, zero_add, ← AdicCompletion.algebraMap_apply, AlgEquiv.commutes,
          MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          MvPowerSeries.constantCoeff_C]


end
