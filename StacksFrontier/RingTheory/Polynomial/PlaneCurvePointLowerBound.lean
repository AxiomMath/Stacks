module

public import StacksFrontier.FieldTheory.GaloisResolventFactors
public import StacksFrontier.RingTheory.Polynomial.GaloisResolventPoints
public import StacksFrontier.RingTheory.Polynomial.PlaneCurvePointUpperBound

/-!
# The lower bound `q - C √q` for the points of an absolutely irreducible plane curve

Let `g ∈ 𝔽_q[X][Y]` be monic of `Y`-degree `m` and total degree `m`, with `∂g/∂Y ≠ 0`, and
absolutely irreducible. Over `Ω = 𝔽̄_q`, label the roots `b₁, …, b_m` of `g(a, Y)` at a good
`a ∈ 𝔽_q`; Frobenius permutes them by some `π_a`, and the number of `𝔽_q`-points of `g` over `a`
is the number of fixed points of `π_a`. The Galois resolvent `Φ(a, T) = ∏_π (T - Σ cᵢ b_{π i})`
factors over `Ω[X]` into absolutely irreducible `Ψ`, and for each `τ ∈ S_m` the points
`(a, t)` of `Ψ` with `Δ(a) t^q = R_τ(a, t)` are counted by Stepanov's upper bound when the twisted
Frobenius preserves `Ψ`, and by Bézout otherwise. The twisted orbit counts of the Galois group
turn these upper bounds into the lower bound.

## Main results

* `Polynomial.Bivariate.exists_card_ge_of_monic`: the lower bound `#C(𝔽_q) ≥ q - c √q`, with `c`
  depending only on the degree `m`, for every finite field.
* `Polynomial.Bivariate.fiber_twisted_count`, `Polynomial.Bivariate.global_twisted_count`: the
  counting identities over the fibres.
* `Polynomial.Bivariate.card_le_of_twisted_points`: the stable/unstable dichotomy for one factor
  of the resolvent and one twist.
* `Polynomial.Bivariate.le_of_twisted_counts`: the inequality bookkeeping.
-/

@[expose] public section

open Polynomial Finset
open scoped Polynomial.Bivariate Nat

namespace Polynomial.Bivariate

/-- **The bookkeeping.** Let `sᵢ ≤ eᵢ q + U` (`i ∈ I`), with `∑ sᵢ = M · n` and `q - D ≤ n`,
`∑ eᵢ = M`, `∑ fᵢ eᵢ = M` and `0 ≤ fᵢ ≤ μ`. Then `∑ fᵢ sᵢ ≥ M q - μ (#I U + M D)`. -/
theorem le_of_twisted_counts {ι : Type*} (I : Finset ι) (s e f : ι → ℝ) {q U M n D μ : ℝ}
    (hs : ∀ i ∈ I, s i ≤ e i * q + U) (hf : ∀ i ∈ I, 0 ≤ f i ∧ f i ≤ μ)
    (hsum : ∑ i ∈ I, s i = M * n) (hn : q - D ≤ n) (he : ∑ i ∈ I, e i = M)
    (hfe : ∑ i ∈ I, f i * e i = M) (hU : 0 ≤ U) (_hq : 0 ≤ q) (hM : 0 ≤ M) (hμ : 0 ≤ μ) :
    M * q - μ * (I.card * U + M * D) ≤ ∑ i ∈ I, f i * s i := by
  set t : ι → ℝ := fun i => e i * q + U - s i
  have ht0 : ∀ i ∈ I, 0 ≤ t i := fun i hi => by simp only [t]; linarith [hs i hi]
  have hsumt : ∑ i ∈ I, t i ≤ I.card * U + M * D := by
    simp only [t, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, he,
      Finset.sum_const, nsmul_eq_mul, hsum]
    nlinarith
  have hft : ∑ i ∈ I, f i * t i ≤ μ * ∑ i ∈ I, t i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hf i hi).2 (ht0 i hi)
  have hfU : 0 ≤ ∑ i ∈ I, f i * U := Finset.sum_nonneg fun i hi => mul_nonneg (hf i hi).1 hU
  have hfs : ∑ i ∈ I, f i * s i = q * M + ∑ i ∈ I, f i * U - ∑ i ∈ I, f i * t i := by
    simp only [t, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [show ∑ i ∈ I, f i * (e i * q) = q * ∑ i ∈ I, f i * e i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hfe]
    ring
  rw [hfs]
  nlinarith [mul_le_mul_of_nonneg_left hsumt hμ]

/-- **The counting identities over one fibre.** Suppose every `π ∈ S_m` is attached to exactly
one `Ψ ∈ 𝒪` (through `Z Ψ π`), and let `α ∈ S_m`. Counting, for each `Ψ` and `τ`, the `π` attached
to `Ψ` with `α π = π τ`, the totals are `m!`, and `m!` times the number of fixed points of `α`
when each `τ` is weighted by its number of fixed points. -/
theorem fiber_twisted_count {m : ℕ} {X : Type*} (𝒪 : Finset X)
    (Z : X → Equiv.Perm (Fin m) → Prop) [∀ Ψ π, Decidable (Z Ψ π)]
    (hZ : ∀ π, ∃! Ψ, Ψ ∈ 𝒪 ∧ Z Ψ π) (α : Equiv.Perm (Fin m)) :
    ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), (univ.filter fun π => Z Ψ π ∧ α * π = π * τ).card = m ! ∧
    ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), (univ.filter fun i => τ i = i).card *
      (univ.filter fun π => Z Ψ π ∧ α * π = π * τ).card =
      m ! * (univ.filter fun i => α i = i).card := by
  classical
  have hconj : ∀ π τ : Equiv.Perm (Fin m), α * π = π * τ ↔ τ = π⁻¹ * α * π := fun π τ => by
    rw [mul_assoc, eq_inv_mul_iff_mul_eq, eq_comm]
  have hone : ∀ π : Equiv.Perm (Fin m), ∑ Ψ ∈ 𝒪, (if Z Ψ π then 1 else 0 : ℕ) = 1 := by
    intro π
    obtain ⟨Ψ, ⟨hΨ, hZΨ⟩, huniq⟩ := hZ π
    rw [Finset.sum_eq_single Ψ (fun Ψ' hΨ' hne => if_neg fun h => hne (huniq Ψ' ⟨hΨ', h⟩))
      (fun h => absurd hΨ h), if_pos hZΨ]
  have key : ∀ (w : Equiv.Perm (Fin m) → ℕ),
      ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), w τ *
        (univ.filter fun π => Z Ψ π ∧ α * π = π * τ).card =
      ∑ π : Equiv.Perm (Fin m), w (π⁻¹ * α * π) := by
    intro w
    calc ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), w τ *
          (univ.filter fun π => Z Ψ π ∧ α * π = π * τ).card
        = ∑ Ψ ∈ 𝒪, ∑ π : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
            w τ * (if Z Ψ π ∧ α * π = π * τ then 1 else 0) := by
          refine Finset.sum_congr rfl fun Ψ _ => ?_
          simp only [Finset.card_filter, Finset.mul_sum]
          exact Finset.sum_comm
      _ = ∑ π : Equiv.Perm (Fin m), ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m),
            w τ * (if Z Ψ π ∧ α * π = π * τ then 1 else 0) := Finset.sum_comm
      _ = _ := ?_
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [hconj, mul_ite, mul_one, mul_zero]
    have : ∀ Ψ ∈ 𝒪, (∑ τ : Equiv.Perm (Fin m),
        if Z Ψ π ∧ τ = π⁻¹ * α * π then w τ else 0) = if Z Ψ π then w (π⁻¹ * α * π) else 0 := by
      intro Ψ _
      by_cases h : Z Ψ π <;> simp [h]
    rw [Finset.sum_congr rfl this]
    calc ∑ Ψ ∈ 𝒪, (if Z Ψ π then w (π⁻¹ * α * π) else 0)
        = w (π⁻¹ * α * π) * ∑ Ψ ∈ 𝒪, (if Z Ψ π then 1 else 0 : ℕ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun Ψ _ => by split_ifs <;> simp
      _ = w (π⁻¹ * α * π) := by rw [hone, mul_one]
  refine ⟨?_, ?_⟩
  · simpa only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      smul_eq_mul, mul_one] using key fun _ => 1
  · rw [key fun τ => (univ.filter fun i => τ i = i).card]
    simp only [GaloisResolventFactors.card_fixed_conj, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, smul_eq_mul]

/-- A monic polynomial of degree `n` over an algebraically closed field is a product of `n`
linear factors, labelled by `Fin n`. -/
theorem exists_eq_prod_X_sub_C {K : Type*} [Field K] [IsAlgClosed K] :
    ∀ (n : ℕ) {p : K[X]}, p.Monic → p.natDegree = n → ∃ b : Fin n → K, p = ∏ i, (X - C (b i)) := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    exact ⟨Fin.elim0, by rw [eq_one_of_monic_natDegree_zero hp hn]; simp⟩
  | succ n ih =>
    intro p hp hn
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p (by
      rw [degree_eq_natDegree hp.ne_zero, hn]; exact_mod_cast Nat.succ_ne_zero n)
    obtain ⟨p', hp'⟩ := dvd_iff_isRoot.mpr hr
    have hmon' : p'.Monic := by
      have := hp; rw [hp'] at this; exact (monic_X_sub_C r).of_mul_monic_left this
    have hdeg' : p'.natDegree = n := by
      have := congrArg natDegree hp'
      rw [(monic_X_sub_C r).natDegree_mul hmon', natDegree_X_sub_C, hn] at this
      omega
    obtain ⟨b, hb⟩ := ih hmon' hdeg'
    exact ⟨Fin.cons r b, by rw [Fin.prod_univ_succ, Fin.cons_zero, hp', hb]; simp⟩

variable {Ω : Type*} [Field Ω]

/-- **The fibre of the resolvent at a good point.** Let `f ∈ Ω[X][Y]` be monic of `Y`-degree `m`,
`c : Fin m → Ω`, and let `α ∈ Ω` with `Δ(α) ≠ 0`. Then the roots `b` of `f(α, Y)` are distinct,
the values `t_π = ∑ cᵢ b_{π i}` are distinct and are the roots of `Φ(α, T)`, and
`R_τ(α, t_π) = Δ(α) t_{π τ}`. -/
theorem exists_fibre_labelling [IsAlgClosed Ω] {m : ℕ} {f : Ω[X][Y]} (hf : f.Monic)
    (hm : f.natDegree = m) (c : Fin m → Ω) {α : Ω}
    (hα : (resolventDisc f fun i => C (c i)).eval α ≠ 0) :
    ∃ b : Fin m → Ω, f.map (evalRingHom α) = ∏ i, (X - C (b i)) ∧ Function.Injective b ∧
      Function.Injective (fun π : Equiv.Perm (Fin m) => ∑ i, c i * b (π i)) ∧
      (galoisResolvent f fun i => C (c i)).map (evalRingHom α) =
        ∏ π : Equiv.Perm (Fin m), (X - C (∑ i, c i * b (π i))) ∧
      ∀ τ π : Equiv.Perm (Fin m), (resolventPerm f (fun i => C (c i)) τ).evalEval α
        (∑ i, c i * b (π i)) =
          (resolventDisc f fun i => C (c i)).eval α * ∑ i, c i * b ((π * τ) i) := by
  classical
  have hmon : (f.map (evalRingHom α)).Monic := hf.map _
  obtain ⟨b, hb⟩ := exists_eq_prod_X_sub_C m hmon (by rw [hf.natDegree_map, hm])
  obtain ⟨h1, h2, h3⟩ := galoisResolvent_spec f (fun i => C (c i)) (evalRingHom α) b hb
  simp only [coe_evalRingHom, eval_C] at h1 h2 h3
  have hu : Function.Injective (fun π : Equiv.Perm (Fin m) => ∑ i, c i * b (π i)) := by
    intro π π' h
    by_contra hne
    apply hα
    rw [h2]
    refine Finset.prod_eq_zero (Finset.mem_univ π) (Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩) ?_)
    exact sub_eq_zero.mpr h
  refine ⟨b, hb, fun i j hij => ?_, hu, h1, fun τ π => ?_⟩
  · by_contra hne
    have := @hu 1 (Equiv.swap i j) (by
      simp only [Equiv.Perm.one_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hki : k = i
      · subst hki; simp [Equiv.swap_apply_left, hij]
      · by_cases hkj : k = j
        · subst hkj; simp [Equiv.swap_apply_right, hij]
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj])
    exact hne (by simpa using congrArg (· i) this.symm |>.symm)
  · have := h3 τ π
    rw [← map_evalRingHom_eval, this]

/-- **Frobenius permutes the roots of a fibre.** If a ring automorphism `fr` of `Ω` fixes `f`,
the point `α` and the `cᵢ`, it permutes the roots `b` of `f(α, Y)` by some `π_α`, and then
`fr (t_π) = t_{π_α π}`. -/
theorem exists_frobenius_perm {m : ℕ} {f : Ω[X][Y]} (fr : Ω ≃+* Ω)
    (hfr : f.map (mapRingHom (fr : Ω →+* Ω)) = f) {α : Ω} (hα : fr α = α) {b : Fin m → Ω}
    (hb : f.map (evalRingHom α) = ∏ i, (X - C (b i))) (hbinj : Function.Injective b)
    (c : Fin m → Ω) (hc : ∀ i, fr (c i) = c i) :
    ∃ πa : Equiv.Perm (Fin m), (∀ i, b (πa i) = fr (b i)) ∧
      ∀ π : Equiv.Perm (Fin m), fr (∑ i, c i * b (π i)) = ∑ i, c i * b ((πa * π) i) := by
  classical
  have hP : (f.map (evalRingHom α)).map (fr : Ω →+* Ω) = f.map (evalRingHom α) := by
    conv_rhs => rw [← hfr]
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext h <;> simp [hα]
  have hroot : ∀ i, ∃ j, b j = fr (b i) := by
    intro i
    have h0 : (f.map (evalRingHom α)).eval (fr (b i)) = 0 := by
      have h := eval_map_apply (p := f.map (evalRingHom α)) (f := (fr : Ω →+* Ω)) (b i)
      rw [hP] at h
      rw [show fr (b i) = (fr : Ω →+* Ω) (b i) from rfl, h, hb]
      simp [eval_prod, Finset.prod_eq_zero (Finset.mem_univ i)]
    rw [hb, eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨j, -, hj⟩ := h0
    exact ⟨j, (sub_eq_zero.mp (by simpa using hj)).symm⟩
  choose σ hσ using hroot
  have hinj : Function.Injective σ := fun i j h => hbinj (fr.injective (by rw [← hσ, ← hσ, h]))
  let πa := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
  refine ⟨πa, fun i => hσ i, fun π => ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hc, Equiv.Perm.mul_apply]
  exact congrArg _ (hσ (π i)).symm

open scoped Classical in
/-- **The bound for one factor and one twist.** For a finite set `S` of points of `Ψ = 0` that
are fixed by the twisted Frobenius `(a, t) ↦ (a, R(a, t) / Δ(a))`: if `Ψ` divides its twisted
composite `G`, Stepanov's bound gives `#S ≤ q + C √q`; otherwise `S` lies on `Ψ = G = 0` and
Bézout gives `#S ≤ 2 D³`. -/
theorem card_le_of_twisted_points [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] {e : ℕ}
    (fr : Ω ≃+* Ω) (hfr : ∀ x, fr x = x ^ p ^ e) {Ψ R : Ω[X][Y]} {Δ : Ω[X]}
    (hirr : Irreducible Ψ) {Dz : ℕ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ S : Finset (Ω × Ω), (∀ P ∈ S, Ψ.evalEval P.1 P.2 = 0 ∧
        (derivative Ψ).evalEval P.1 P.2 ≠ 0 ∧ P.1 ^ p ^ e = P.1 ∧
        (Polynomial.C Δ : Ω[X][Y]).evalEval P.1 P.2 ≠ 0 ∧
        (Polynomial.C Δ : Ω[X][Y]).evalEval P.1 P.2 * P.2 ^ p ^ e = R.evalEval P.1 P.2) →
      (S.card : ℝ) ≤ (p : ℝ) ^ e + C * √((p : ℝ) ^ e))
    (hΨD : ∀ j, (Ψ.coeff j).natDegree ≤ Dz) (hΨn : Ψ.natDegree ≤ Dz)
    (hGD : ∀ j, ((twistedComp (fr : Ω →+* Ω) Ψ R Δ).coeff j).natDegree ≤ Dz)
    (hGn : (twistedComp (fr : Ω →+* Ω) Ψ R Δ).natDegree ≤ Dz)
    (S : Finset (Ω × Ω))
    (hS : ∀ P ∈ S, Ψ.evalEval P.1 P.2 = 0 ∧ (derivative Ψ).evalEval P.1 P.2 ≠ 0 ∧
      fr P.1 = P.1 ∧ Δ.eval P.1 ≠ 0 ∧ R.evalEval P.1 P.2 = Δ.eval P.1 * fr P.2)
    (hG : ∀ P ∈ S, (twistedComp (fr : Ω →+* Ω) Ψ R Δ).evalEval P.1 P.2 = 0) :
    (S.card : ℝ) ≤ (if Ψ ∣ twistedComp (fr : Ω →+* Ω) Ψ R Δ then 1 else 0) * (p : ℝ) ^ e +
      (C * √((p : ℝ) ^ e) + 2 * Dz ^ 3) := by
  classical
  have hsq : 0 ≤ C * √((p : ℝ) ^ e) := mul_nonneg hC0 (Real.sqrt_nonneg _)
  split_ifs with hdvd
  · have := hC S fun P hP => by
      obtain ⟨h0, h1, h2, h3, h4⟩ := hS P hP
      refine ⟨h0, h1, by rw [← hfr]; exact h2, by simpa [evalEval_C] using h3, ?_⟩
      rw [h4, evalEval_C, hfr]
    have h2 : (0 : ℝ) ≤ 2 * Dz ^ 3 := by positivity
    linarith
  · have := card_le_of_evalEval_eq_zero_of_not_dvd hirr hdvd hΨD hGD hΨn hGn S
      fun P hP => ⟨(hS P hP).1, hG P hP⟩
    have h1 : (S.card : ℝ) ≤ 2 * Dz ^ 3 := by exact_mod_cast this
    linarith

/-- **The counting identities over all good fibres**, from `fiber_twisted_count`. -/
theorem global_twisted_count {m : ℕ} {A X : Type*} (good : Finset A) (𝒪 : Finset X)
    (Z : A → X → Equiv.Perm (Fin m) → Prop) [∀ a Ψ π, Decidable (Z a Ψ π)]
    (hZ : ∀ a ∈ good, ∀ π, ∃! Ψ, Ψ ∈ 𝒪 ∧ Z a Ψ π) (πF : A → Equiv.Perm (Fin m)) :
    ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), ((good ×ˢ univ).filter fun x : A × Equiv.Perm (Fin m) =>
        Z x.1 Ψ x.2 ∧ πF x.1 * x.2 = x.2 * τ).card = m ! * good.card ∧
    ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), (univ.filter fun i => τ i = i).card *
      ((good ×ˢ univ).filter fun x : A × Equiv.Perm (Fin m) =>
        Z x.1 Ψ x.2 ∧ πF x.1 * x.2 = x.2 * τ).card =
      m ! * ∑ a ∈ good, (univ.filter fun i => πF a i = i).card := by
  classical
  have hsplit : ∀ Ψ τ, ((good ×ˢ univ).filter fun x : A × Equiv.Perm (Fin m) =>
      Z x.1 Ψ x.2 ∧ πF x.1 * x.2 = x.2 * τ).card =
      ∑ a ∈ good, (univ.filter fun π => Z a Ψ π ∧ πF a * π = π * τ).card := by
    intro Ψ τ
    rw [Finset.card_filter, Finset.sum_product]
    simp only [Finset.card_filter]
  simp only [hsplit, Finset.mul_sum]
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_comm, Finset.sum_congr rfl fun Ψ _ => Finset.sum_comm, Finset.sum_comm]
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_comm, (fiber_twisted_count 𝒪 (Z a) (hZ a ha) (πF a)).1, mul_one]
  · rw [Finset.sum_comm, Finset.sum_congr rfl fun Ψ _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_comm]
    exact (fiber_twisted_count 𝒪 (Z a) (hZ a ha) (πF a)).2

/-- The final arithmetic of the lower bound. -/
theorem sub_mul_sqrt_le_of_twisted_counts {M m q S N I C B D s : ℝ} (hM : 0 < M) (hm : 0 ≤ m)
    (hs : 1 ≤ s) (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D) (hI : I ≤ M * M)
    (key : M * q - m * (I * (C * s + B) + M * D) ≤ M * S) (hSN : S ≤ N) :
    q - (m * M * C + m * M * B + m * D + M) * s ≤ N := by
  have hU : 0 ≤ C * s + B := by positivity
  have h2 : m * (I * (C * s + B) + M * D) ≤ m * (M * M * (C * s + B) + M * D) := by
    gcongr
  have h3 : M * (q - m * (M * (C * s + B) + D)) ≤ M * S := by nlinarith
  have h4 : q - m * (M * (C * s + B) + D) ≤ S := le_of_mul_le_mul_left h3 hM
  have h5 : m * (M * (C * s + B) + D) ≤ (m * M * C + m * M * B + m * D + M) * s := by
    have : 0 ≤ m * M * B + m * D := by positivity
    nlinarith
  linarith

universe u

/-- **The lower bound `q - c √q` for a monic absolutely irreducible plane curve.** For every
`m` there is `c` such that for every finite field `𝔽_q` and every `g ∈ 𝔽_q[X][Y]` monic of
`Y`-degree and total degree `m`, with `∂g/∂Y ≠ 0` and `g` irreducible over `𝔽̄_q`, the curve
`g = 0` has at least `q - c √q` points in `𝔽_q²`. -/
theorem exists_card_ge_of_monic (m : ℕ) :
    ∃ c : ℝ, ∀ (F : Type u) [Field F] [Fintype F] (g : F[X][Y]), g.Monic → g.natDegree = m →
      WeightedDegreeLE 1 m g → derivative g ≠ 0 →
      Irreducible (g.map (mapRingHom (algebraMap F (AlgebraicClosure F)))) →
      (Fintype.card F : ℝ) - c * √(Fintype.card F) ≤
        ({P : F × F | g.evalEval P.1 P.2 = 0}.ncard : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, fun F _ _ g hg hgm _ _ hirr => ?_⟩
    exact (hirr.not_isUnit
      (by rw [eq_one_of_monic_natDegree_zero hg hgm, Polynomial.map_one]; exact isUnit_one)).elim
  obtain ⟨D, hD⟩ := exists_natDegree_resolvent_le.{u} m m
  set M := m.factorial
  set T := D + M
  set r := D + T * D
  choose Cf hCf using fun j => exists_card_le_add_mul_sqrt.{u} j T r
  set Cmax : ℝ := ∑ j ∈ range (M + 1), |Cf j|
  set Dz : ℕ := M * (D + D) + T + M * D + M
  set B : ℝ := 2 * (Dz : ℝ) ^ 3
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hB0 : 0 ≤ B := by positivity
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  refine ⟨m * M * Cmax + m * M * B + m * D + M, fun F _ _ g hg hgm hgw hgd hirr => ?_⟩
  set q := Fintype.card F
  have hsq0 : (0 : ℝ) ≤ √(q : ℝ) := Real.sqrt_nonneg _
  have hncard0 : (0 : ℝ) ≤ ({P : F × F | g.evalEval P.1 P.2 = 0}.ncard : ℝ) := by positivity
  by_cases hq : q ≤ M ^ 2
  · -- small `q`: the left side is `≤ 0`
    have h1 : √(q : ℝ) ≤ M := by
      rw [show (M : ℝ) = √((M : ℝ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
    have h2 : (q : ℝ) = √(q : ℝ) * √(q : ℝ) := (Real.mul_self_sqrt (by positivity)).symm
    have h3 : 0 ≤ (m * M * Cmax + m * M * B + m * D : ℝ) := by positivity
    nlinarith
  push Not at hq
  -- the field `F`, its algebraic closure `Ω` and the Frobenius `fr = (·) ^ q`
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' F
  have := hchar
  have : Fact p.Prime := ⟨hp⟩
  set alg := algebraMap F (AlgebraicClosure F)
  have : CharP (AlgebraicClosure F) p := charP_of_injective_algebraMap alg.injective p
  have : PerfectRing (AlgebraicClosure F) p := PerfectField.toPerfectRing p
  set e : ℕ := (n : ℕ)
  have he : 0 < e := n.pos
  have hqe : q = p ^ e := hcard
  set fr := iterateFrobeniusEquiv (AlgebraicClosure F) p e
  have hfrx : ∀ x, fr x = x ^ p ^ e := fun x => iterateFrobeniusEquiv_def _ p e x
  have hfrφ : ∀ a : F, fr (alg a) = alg a := fun a => by
    rw [hfrx, ← map_pow, ← hqe, FiniteField.pow_card]
  -- the curve over `Ω`
  set f : (AlgebraicClosure F)[X][Y] := g.map (mapRingHom alg)
  have hf : f.Monic := hg.map _
  have hinjX : Function.Injective (mapRingHom alg) := Polynomial.map_injective _ alg.injective
  have hfm : f.natDegree = m := by rw [natDegree_map_eq_of_injective hinjX, hgm]
  have hfcoeff : ∀ j, (f.coeff j).natDegree ≤ m := fun j => by
    rw [coeff_map, coe_mapRingHom]
    exact natDegree_map_le.trans (hgm ▸ hgw.coeff_natDegree_le j)
  have hfd : derivative f ≠ 0 := by
    rw [derivative_map]; exact (Polynomial.map_ne_zero_iff hinjX).mpr hgd
  have hfsep : (f.map (algebraMap (AlgebraicClosure F)[X]
      (FractionRing (AlgebraicClosure F)[X]))).Separable := by
    have hirrK := (hf.isPrimitive.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing (AlgebraicClosure F)[X])).mp hirr
    refine (Polynomial.separable_iff_derivative_ne_zero hirrK).mpr ?_
    rw [derivative_map]
    exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective _ _)).mpr hfd
  have hfr : f.map (mapRingHom (fr : AlgebraicClosure F →+* AlgebraicClosure F)) = f := by
    simp only [f, Polynomial.map_map, mapRingHom_comp]
    congr 2
    exact RingHom.ext hfrφ
  -- the coefficients `cᵢ ∈ F` of the resolvent
  set S0 : Finset (AlgebraicClosure F)[X] := univ.image fun a : F => (C (alg a) : _)
  have hS0 : S0.card = q :=
    Finset.card_image_of_injective _ fun a b h => alg.injective (C_injective h)
  obtain ⟨c0, hc0S, hΔ0⟩ := exists_resolventDisc_ne_zero f hf hfm hfsep S0 (by rw [hS0]; exact hq)
  have hac : ∀ i, ∃ a : F, (C (alg a) : (AlgebraicClosure F)[X]) = c0 i := fun i => by
    simpa [S0] using hc0S i
  choose ac hac using hac
  set c' : Fin m → AlgebraicClosure F := fun i => alg (ac i)
  have hc0 : c0 = fun i => C (c' i) := _root_.funext fun i => (hac i).symm
  rw [hc0] at hΔ0
  have hc' : ∀ i, fr (c' i) = c' i := fun i => hfrφ _
  -- the factors of the resolvent and the degree bounds
  obtain ⟨𝒪, h𝒪, hprod, hcnt1, hcnt2⟩ :=
    exists_factors_galoisResolvent f hf hfm hirr hfsep fr hfr c' hc' hΔ0
  obtain ⟨hΦD, hΔD, hRD⟩ := hD _ f c' hf hfm hfcoeff
  set Φ := galoisResolvent f fun i => C (c' i)
  set Δ := resolventDisc f fun i => C (c' i)
  -- the good fibres
  set good : Finset F := univ.filter fun a => Δ.eval (alg a) ≠ 0
  have hgood : (q : ℝ) - D ≤ good.card := by
    have hbad : (univ.filter fun a : F => ¬ Δ.eval (alg a) ≠ 0).card ≤ D := by
      refine (Finset.card_le_card_of_injOn alg (t := Δ.roots.toFinset) (fun a ha => ?_)
        alg.injective.injOn).trans ((Multiset.toFinset_card_le _).trans
          ((card_roots' _).trans hΔD))
      have ha' := (Finset.mem_filter.mp ha).2
      push Not at ha'
      exact Multiset.mem_toFinset.mpr ((mem_roots hΔ0).mpr ha')
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset F))
      (fun a => Δ.eval (alg a) ≠ 0)
    rw [Finset.card_univ] at this
    have h' : (q : ℝ) = good.card + (univ.filter fun a : F => ¬ Δ.eval (alg a) ≠ 0).card := by
      exact_mod_cast this.symm
    have h'' : ((univ.filter fun a : F => ¬ Δ.eval (alg a) ≠ 0).card : ℝ) ≤ D := by
      exact_mod_cast hbad
    linarith
  -- the labelled fibres and the Frobenius permutations
  have hfib : ∀ a ∈ good, ∃ b : Fin m → AlgebraicClosure F, ∃ πa : Equiv.Perm (Fin m),
      f.map (evalRingHom (alg a)) = ∏ i, (X - C (b i)) ∧ Function.Injective b ∧
      Function.Injective (fun π : Equiv.Perm (Fin m) => ∑ i, c' i * b (π i)) ∧
      Φ.map (evalRingHom (alg a)) = ∏ π : Equiv.Perm (Fin m), (X - C (∑ i, c' i * b (π i))) ∧
      (∀ τ π : Equiv.Perm (Fin m), (resolventPerm f (fun i => C (c' i)) τ).evalEval (alg a)
        (∑ i, c' i * b (π i)) = Δ.eval (alg a) * ∑ i, c' i * b ((π * τ) i)) ∧
      (∀ i, b (πa i) = fr (b i)) ∧
      ∀ π : Equiv.Perm (Fin m), fr (∑ i, c' i * b (π i)) = ∑ i, c' i * b ((πa * π) i) := by
    intro a ha
    obtain ⟨b, hb, hbinj, hu, hΦa, hRa⟩ :=
      exists_fibre_labelling hf hfm c' (Finset.mem_filter.mp ha).2
    obtain ⟨πa, h1, h2⟩ := exists_frobenius_perm fr hfr (hfrφ a) hb hbinj c' hc'
    exact ⟨b, πa, hb, hbinj, hu, hΦa, hRa, h1, h2⟩
  choose! bF πF hbF using hfib
  set u : F → Equiv.Perm (Fin m) → AlgebraicClosure F := fun a π => ∑ i, c' i * bF a (π i)
  set Z : F → (AlgebraicClosure F)[X][Y] → Equiv.Perm (Fin m) → Prop :=
    fun a Ψ π => Ψ.evalEval (alg a) (u a π) = 0
  have hZ : ∀ a ∈ good, ∀ π, ∃! Ψ, Ψ ∈ 𝒪 ∧ Z a Ψ π := fun a ha π =>
    (existsUnique_factor_root hprod (hbF a ha).2.2.1 (hbF a ha).2.2.2.1 π).1
  have hsimple : ∀ a ∈ good, ∀ π, ∀ Ψ ∈ 𝒪, Z a Ψ π →
      (derivative Ψ).evalEval (alg a) (u a π) ≠ 0 := fun a ha π =>
    (existsUnique_factor_root hprod (hbF a ha).2.2.1 (hbF a ha).2.2.2.1 π).2
  -- degree bounds for the factors and the twists
  have hΦmon : Φ.Monic := galoisResolvent_monic _ _
  have hΦdeg : Φ.natDegree = M := by
    obtain ⟨b, hb⟩ := exists_eq_prod_X_sub_C m (hf.map (evalRingHom (0 : AlgebraicClosure F)))
      (by rw [hf.natDegree_map, hfm])
    have h := (galoisResolvent_spec f (fun i => C (c' i)) (evalRingHom 0) b hb).1
    rw [← hΦmon.natDegree_map (evalRingHom 0)]
    show (Φ.map _).natDegree = M
    rw [h, natDegree_prod_of_monic _ _ fun π _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, smul_eq_mul, mul_one, M]
  have hΦw : WeightedDegreeLE 1 T Φ := fun j hj => by
    have hjM : j ≤ M := hΦdeg ▸ le_natDegree_of_ne_zero hj
    have := hΦD j
    simp only [T]; omega
  have h𝒪deg : ∀ Ψ ∈ 𝒪, Ψ.natDegree ≤ M ∧ WeightedDegreeLE 1 T Ψ := by
    intro Ψ hΨ
    have hdvd : Ψ ∣ Φ := hprod ▸ Finset.dvd_prod_of_mem _ hΨ
    exact ⟨hΦdeg ▸ natDegree_le_of_dvd hdvd hΦmon.ne_zero,
      WeightedDegreeLE.of_dvd hΦmon.ne_zero hdvd hΦw⟩
  have h𝒪w : ∀ Ψ ∈ 𝒪, WeightedDegreeLE T (T * Ψ.natDegree) Ψ := by
    intro Ψ hΨ j hj
    have hj' : j ≤ Ψ.natDegree := le_natDegree_of_ne_zero hj
    rcases hj'.lt_or_eq with hlt | heq
    · have h1 := (h𝒪deg Ψ hΨ).2.coeff_natDegree_le j
      have : T * j + T ≤ T * Ψ.natDegree := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    · subst heq
      rw [(h𝒪 Ψ hΨ).1.coeff_natDegree, natDegree_one, zero_add]
  have hRw : ∀ τ, WeightedDegreeLE T r (resolventPerm f (fun i => C (c' i)) τ) := by
    intro τ j hj
    have hj' : j ≤ D := (le_natDegree_of_ne_zero hj).trans (hRD τ).1
    exact Nat.add_le_add ((hRD τ).2 j) (Nat.mul_le_mul_left T hj')
  have hΔw : WeightedDegreeLE T r (C Δ : (AlgebraicClosure F)[X][Y]) :=
    WeightedDegreeLE.C (hΔD.trans (Nat.le_add_right _ _))
  -- the point sets and their bounds
  set G : (AlgebraicClosure F)[X][Y] → Equiv.Perm (Fin m) → (AlgebraicClosure F)[X][Y] :=
    fun Ψ τ => twistedComp (fr : AlgebraicClosure F →+* AlgebraicClosure F) Ψ
      (resolventPerm f (fun i => C (c' i)) τ) Δ
  set Fset : (AlgebraicClosure F)[X][Y] → Equiv.Perm (Fin m) → Finset (F × Equiv.Perm (Fin m)) :=
    fun Ψ τ => (good ×ˢ univ).filter fun x => Z x.1 Ψ x.2 ∧ πF x.1 * x.2 = x.2 * τ
  have hq' : (q : ℝ) = (p : ℝ) ^ e := by rw [hqe]; push_cast; ring
  have hbound : ∀ Ψ ∈ 𝒪, ∀ τ, ((Fset Ψ τ).card : ℝ) ≤
      (if Ψ ∣ G Ψ τ then 1 else 0) * (q : ℝ) + (Cmax * √(q : ℝ) + B) := by
    intro Ψ hΨ τ
    set Sset := (Fset Ψ τ).image fun x => (alg x.1, u x.1 x.2)
    have hcard : Sset.card = (Fset Ψ τ).card := by
      refine Finset.card_image_of_injOn fun x hx y hy hxy => ?_
      have hx' := (Finset.mem_filter.mp hx).1
      have hy' := (Finset.mem_filter.mp hy).1
      simp only [Prod.mk.injEq] at hxy
      have h1 : x.1 = y.1 := alg.injective hxy.1
      have hxg : x.1 ∈ good := (Finset.mem_product.mp hx').1
      have h2 : x.2 = y.2 := (hbF x.1 hxg).2.2.1 (by
        have := hxy.2; simp only [u] at this; rw [h1] at this ⊢; exact this)
      exact Prod.ext h1 h2
    -- the points of `Sset` satisfy the hypotheses of the one-factor bound
    have hS' : ∀ P ∈ Sset, Ψ.evalEval P.1 P.2 = 0 ∧ (derivative Ψ).evalEval P.1 P.2 ≠ 0 ∧
        fr P.1 = P.1 ∧ Δ.eval P.1 ≠ 0 ∧ (resolventPerm f (fun i => C (c' i)) τ).evalEval P.1 P.2 =
          Δ.eval P.1 * fr P.2 := fun P hP => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨hx1, hx2, hx3⟩ := Finset.mem_filter.mp hx
      have hxg : x.1 ∈ good := (Finset.mem_product.mp hx1).1
      refine ⟨hx2, hsimple x.1 hxg x.2 Ψ hΨ hx2, hfrφ x.1, (Finset.mem_filter.mp hxg).2, ?_⟩
      simp only [u]
      rw [(hbF x.1 hxg).2.2.2.2.1 τ x.2, (hbF x.1 hxg).2.2.2.2.2.2 x.2, hx3]
    rw [← hcard, hq']
    refine card_le_of_twisted_points p fr hfrx (h𝒪 Ψ hΨ).2 hCmax0 (fun S hS => ?_)
      (fun j => ((h𝒪deg Ψ hΨ).2.coeff_natDegree_le j).trans (by simp only [Dz]; omega))
      ((h𝒪deg Ψ hΨ).1.trans (by simp only [Dz]; omega)) (fun j => ?_) ?_ Sset hS'
      (fun P hP => ?_)
    · -- Stepanov's bound for the factor `Ψ`
      by_cases hd : derivative Ψ = 0
      · have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem fun P hP =>
          (hS P hP).2.1 (by rw [hd]; simp)
        rw [hS0, Finset.card_empty, Nat.cast_zero]
        positivity
      · have h := hCf Ψ.natDegree (AlgebraicClosure F) p e he Ψ
          (resolventPerm f (fun i => C (c' i)) τ) (C Δ) (h𝒪 Ψ hΨ).1 (h𝒪 Ψ hΨ).2 hd rfl
          (h𝒪w Ψ hΨ) (hRw τ) hΔw S hS
        have hCle : Cf Ψ.natDegree ≤ Cmax :=
          (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cf j|)
            (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le (h𝒪deg Ψ hΨ).1)))
        nlinarith [Real.sqrt_nonneg ((p : ℝ) ^ e)]
    · -- the coefficients of the twisted composite
      have hw0 := weightedDegreeLE_zero_twistedComp (fr : AlgebraicClosure F →+* AlgebraicClosure F)
        (Ψ := Ψ) (R := resolventPerm f (fun i => C (c' i)) τ) (Δ := Δ) (DΨ := T) (DR := D)
        (DΔ := D) (fun j _ => by simpa using (h𝒪deg Ψ hΨ).2.coeff_natDegree_le j)
        (fun j _ => by simpa using (hRD τ).2 j) hΔD
      refine (hw0.coeff_natDegree_le j).trans ?_
      have : Ψ.natDegree * (D + D) ≤ M * (D + D) := Nat.mul_le_mul_right _ (h𝒪deg Ψ hΨ).1
      simp only [Dz]; omega
    · refine (natDegree_twistedComp_le _ _ _ _).trans ?_
      have : Ψ.natDegree * (resolventPerm f (fun i => C (c' i)) τ).natDegree ≤ M * D :=
        Nat.mul_le_mul (h𝒪deg Ψ hΨ).1 (hRD τ).1
      simp only [Dz]; omega
    · obtain ⟨h0, -, h2, -, h4⟩ := hS' P hP
      rw [evalEval_twistedComp _ _ _ _ h2 h4, h0, map_zero, mul_zero]
  -- the fixed points of the Frobenius permutations are the `F`-points of `g`
  have hfix : ∀ a ∈ good, (univ.filter fun i => πF a i = i).card =
      (univ.filter fun y : F => g.evalEval a y = 0).card := by
    intro a ha
    obtain ⟨hb, hbinj, -, -, -, hπ1, -⟩ := hbF a ha
    have hroot : ∀ x, f.evalEval (alg a) x = ∏ i, (x - bF a i) := fun x => by
      rw [← map_evalRingHom_eval, hb, eval_prod]; simp
    have halg : ∀ y : F, f.evalEval (alg a) (alg y) = alg (g.evalEval a y) := fun y =>
      map_mapRingHom_evalEval alg g a y
    have himg : (univ.filter fun i => πF a i = i).image (bF a) =
        (univ.filter fun y : F => g.evalEval a y = 0).image alg := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hfixi : fr (bF a i) = bF a i := by rw [← hπ1, hi]
        obtain ⟨y, hy⟩ := FiniteField.exists_algebraMap_eq_of_pow_card_eq (F := F)
          (x := bF a i) (by
            have h := hfrx (bF a i)
            rw [hfixi, ← hqe] at h
            exact h.symm)
        refine ⟨y, alg.injective ?_, hy⟩
        rw [map_zero, ← halg, hy, hroot]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
      · rintro ⟨y, hy, rfl⟩
        have h0 : ∏ i, (alg y - bF a i) = 0 := by rw [← hroot, halg, hy, map_zero]
        obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h0
        have hi' : alg y = bF a i := sub_eq_zero.mp hi
        refine ⟨i, hbinj ?_, hi'.symm⟩
        rw [hπ1, ← hi', hfrφ]
    rw [← Finset.card_image_of_injective _ hbinj, himg,
      Finset.card_image_of_injective _ alg.injective]
  -- the `F`-points over the good fibres
  have hpoints : ∑ a ∈ good, (univ.filter fun y : F => g.evalEval a y = 0).card ≤
      {P : F × F | g.evalEval P.1 P.2 = 0}.ncard := by
    rw [← Finset.card_sigma]
    have := Finset.card_le_card_of_injOn (fun x : Σ _ : F, F => (x.1, x.2))
      (s := good.sigma fun a => univ.filter fun y : F => g.evalEval a y = 0)
      (t := univ.filter fun P : F × F => g.evalEval P.1 P.2 = 0)
      (fun x hx => by
        obtain ⟨-, h⟩ := Finset.mem_sigma.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩)
      (fun x _ y _ h => by
        simp only [Prod.mk.injEq] at h
        exact Sigma.ext h.1 (heq_of_eq h.2))
    refine this.trans (le_of_eq ?_)
    rw [← Set.ncard_coe_finset]
    congr 1
    ext P
    simp
  -- the number of factors
  have h𝒪card : 𝒪.card ≤ M := by
    calc 𝒪.card = ∑ Ψ ∈ 𝒪, 1 := by simp
      _ ≤ ∑ Ψ ∈ 𝒪, Ψ.natDegree := Finset.sum_le_sum fun Ψ hΨ =>
          (h𝒪 Ψ hΨ).1.natDegree_pos_of_not_isUnit (h𝒪 Ψ hΨ).2.not_isUnit
      _ = Φ.natDegree := by
          rw [← hprod, natDegree_prod_of_monic _ _ fun Ψ hΨ => (h𝒪 Ψ hΨ).1]
      _ = M := hΦdeg
  -- the bookkeeping
  obtain ⟨hsum1, hsum2⟩ := global_twisted_count good 𝒪 Z hZ πF
  set I := 𝒪 ×ˢ (univ : Finset (Equiv.Perm (Fin m)))
  set sF : (AlgebraicClosure F)[X][Y] × Equiv.Perm (Fin m) → ℝ :=
    fun x => ((Fset x.1 x.2).card : ℝ)
  set eF : (AlgebraicClosure F)[X][Y] × Equiv.Perm (Fin m) → ℝ :=
    fun x => if x.1 ∣ G x.1 x.2 then 1 else 0
  set fF : (AlgebraicClosure F)[X][Y] × Equiv.Perm (Fin m) → ℝ :=
    fun x => ((univ.filter fun i => x.2 i = i).card : ℝ)
  have hU : 0 ≤ Cmax * √(q : ℝ) + B := by positivity
  have hs : ∀ x ∈ I, sF x ≤ eF x * q + (Cmax * √(q : ℝ) + B) := fun x hx =>
    hbound x.1 (Finset.mem_product.mp hx).1 x.2
  have hfF : ∀ x ∈ I, 0 ≤ fF x ∧ fF x ≤ m := fun x _ => ⟨by positivity, by
    have := Finset.card_filter_le (univ : Finset (Fin m)) fun i => x.2 i = i
    simp only [Finset.card_univ, Fintype.card_fin] at this
    simp only [fF]
    exact_mod_cast this⟩
  have hsumI : ∑ x ∈ I, sF x = M * good.card := by
    rw [Finset.sum_product]
    simp only [sF]
    exact_mod_cast hsum1
  have heI : ∑ x ∈ I, eF x = M := by
    rw [Finset.sum_product]
    simp only [eF, Finset.sum_boole]
    exact_mod_cast hcnt1
  have hfeI : ∑ x ∈ I, fF x * eF x = M := by
    rw [Finset.sum_product]
    simp only [fF, eF, mul_ite, mul_one, mul_zero]
    simp only [← Finset.sum_filter]
    exact_mod_cast hcnt2
  have hfsI : ∑ x ∈ I, fF x * sF x =
      M * ∑ a ∈ good, ((univ.filter fun y : F => g.evalEval a y = 0).card : ℝ) := by
    rw [Finset.sum_product]
    have h := congrArg (Nat.cast : ℕ → ℝ) hsum2
    push_cast at h
    rw [Finset.sum_congr rfl fun a ha => (congrArg (Nat.cast : ℕ → ℝ) (hfix a ha)).symm]
    exact h
  have key := le_of_twisted_counts I sF eF fF hs hfF hsumI hgood heI hfeI hU (by positivity)
    (by positivity) (by positivity)
  rw [hfsI] at key
  have hpts : ∑ a ∈ good, ((univ.filter fun y : F => g.evalEval a y = 0).card : ℝ) ≤
      ({P : F × F | g.evalEval P.1 P.2 = 0}.ncard : ℝ) := by exact_mod_cast hpoints
  have hIcard : (I.card : ℝ) ≤ M * M := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    exact_mod_cast Nat.mul_le_mul_right _ h𝒪card
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hsq1 : (1 : ℝ) ≤ √(q : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast Fintype.card_pos
  exact sub_mul_sqrt_le_of_twisted_counts hMpos (by positivity) hsq1 hCmax0 hB0 (by positivity)
    hIcard key hpts

end Polynomial.Bivariate
