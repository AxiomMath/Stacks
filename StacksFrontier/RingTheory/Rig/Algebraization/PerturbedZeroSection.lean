module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.RingTheory.Rig.PrincipalLiftUniform

/-!
# Perturbing the fibre coordinates of a completed normal bundle

Let `a ∈ A`, let `B` and `C` be Noetherian `A`-algebras which are `a`-adically complete, and let
`β : B → C`, `s : C → B` be `A`-algebra maps with `s ∘ β = id`, and let `T₁, …, T_N ∈ C` with
`ker s ⊆ (T₁, …, T_N)`. Suppose moreover that every point `τ` of `{τ ∈ Bᴺ : aᶜ τ = E τ}`, for a
matrix `E` with `E² = aᶜ E`, gives an `A`-algebra map `ev τ : C → B` with `ev τ ∘ β = id` and
`ev τ (Tᵢ) = τᵢ`, depending continuously on `τ`. Then there is an `n` such that whenever
`t₁, …, t_N ∈ C` are congruent to `T₁, …, T_N` modulo `aⁿ` and satisfy an exact relation
`aᶜ t = E₀ t` with `E₀ ≡ β(E)` modulo `aⁿ`, the quotient `C / (t₁, …, t_N)` is isomorphic to `B`
as an `A`-algebra.

## Main results

* `Rig.exists_algEquiv_quotient_of_perturbed_zeroSection`: the isomorphism `B ≃ C / (t)`.

## References

* [Stacks Project, Tag 0315](https://stacks.math.columbia.edu/tag/0315)
-/

@[expose] public noncomputable section

namespace Rig

universe u v w

section Aux

variable {B : Type*} [CommRing B]

/-- A matrix maps vectors with entries in an ideal to vectors with entries in that ideal. -/
private theorem mulVec_mem_of_forall_mem {N : ℕ} (J : Ideal B) (M : Matrix (Fin N) (Fin N) B)
    {v : Fin N → B} (hv : ∀ i, v i ∈ J) (i : Fin N) : (M.mulVec v) i ∈ J := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ ↦ J.mul_mem_left _ (hv j)

/-- Multiplying by `bᵖ` with `p > 0` moves an element of `(b)ᵐ` into `(b)ᵐ⁺¹`. -/
private theorem pow_mul_mem_pow_succ (b x : B) {m p : ℕ} (hp : 0 < p)
    (hx : x ∈ Ideal.span {b} ^ m) : b ^ p * x ∈ Ideal.span {b} ^ (m + 1) := by
  refine Ideal.pow_le_pow_right (by lia : m + 1 ≤ m + p) ?_
  rw [pow_add, mul_comm (b ^ p)]
  exact Ideal.mul_mem_mul hx (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self b) p)

/-- Congruence modulo `Iᵐ • ⊤` is membership of the difference in `Iᵐ`. -/
private theorem smodEq_pow_smul_top_iff {I : Ideal B} {m : ℕ} {x y : B} :
    x ≡ y [SMOD I ^ m • (⊤ : Ideal B)] ↔ x - y ∈ I ^ m := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

/-- In an `I`-adically separated ring an element lying in every power of `I` vanishes. -/
private theorem eq_zero_of_forall_mem_pow (I : Ideal B) [IsHausdorff I B] {x : B}
    (hx : ∀ m : ℕ, x ∈ I ^ m) : x = 0 :=
  IsHausdorff.haus ‹_› x fun m ↦ smodEq_pow_smul_top_iff.2 (by simpa using hx m)

/-- A sequence of vectors whose consecutive differences lie in `I ^ k` has a limit in an
`I`-adically precomplete ring. -/
private theorem exists_limit_of_sub_mem_pow {ι : Type*} (I : Ideal B) [IsPrecomplete I B]
    (f : ℕ → ι → B) (h : ∀ k i, f (k + 1) i - f k i ∈ I ^ k) :
    ∃ L : ι → B, ∀ k i, L i - f k i ∈ I ^ k := by
  have hcauchy : ∀ m n, m ≤ n → ∀ i, f n i - f m i ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      intro i
      rw [← sub_add_sub_cancel _ (f n i)]
      exact add_mem (Ideal.pow_le_pow_right hmn (h n i)) (ih i)
  choose L hL using fun i ↦ IsPrecomplete.prec (I := I) inferInstance (f := fun k ↦ f k i)
    fun {m n} hmn ↦ (smodEq_pow_smul_top_iff.2 (hcauchy m n hmn i)).symm
  exact ⟨L, fun k i ↦ smodEq_pow_smul_top_iff.1 (hL i k).symm⟩

/-- A vector `z` with `z = bᵖ δ z` for some `p > 0` has all its entries in every power of `(b)`. -/
private theorem forall_mem_pow_of_eq_pow_mul_sum {N : ℕ} (b : B) {p : ℕ} (hp : 0 < p)
    (z : Fin N → B) (δ : Matrix (Fin N) (Fin N) B)
    (hz : ∀ i, z i = b ^ p * ∑ j, δ i j * z j) (m : ℕ) (i : Fin N) :
    z i ∈ Ideal.span {b} ^ m := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
    rw [hz i]
    exact pow_mul_mem_pow_succ _ _ hp (Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (ih j))

/-- Let `E² = r E`, and let `F` assign to each `τ` with `r τ = E τ` a vector depending
continuously on `τ` for the `b`-adic filtration. If `B` is `b`-adically complete and `p > 0`, then
`τ = -bᵖ E (F τ)` has a solution with `r τ = E τ`. -/
private theorem exists_eq_neg_pow_smul_mulVec_of_continuous {N : ℕ} (b r : B)
    [IsAdicComplete (Ideal.span {b}) B] {p : ℕ} (hp : 0 < p) (E : Matrix (Fin N) (Fin N) B)
    (hE : E * E = r • E) (F : (τ : Fin N → B) → r • τ = E.mulVec τ → Fin N → B)
    (hF : ∀ τ h τ' h' (m : ℕ), (∀ i, τ i - τ' i ∈ Ideal.span {b} ^ m) →
      ∀ i, F τ h i - F τ' h' i ∈ Ideal.span {b} ^ m) :
    ∃ τ h, τ = -(b ^ p) • E.mulVec (F τ h) := by
  set I := Ideal.span {b}
  let Bun := {τ : Fin N → B // r • τ = E.mulVec τ}
  let Φ : Bun → Bun := fun τ ↦ ⟨-(b ^ p) • E.mulVec (F τ.1 τ.2), by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hE, Matrix.smul_mulVec, smul_comm]⟩
  have hΦ : ∀ (τ τ' : Bun) (m : ℕ), (∀ i, τ.1 i - τ'.1 i ∈ I ^ m) →
      ∀ i, (Φ τ).1 i - (Φ τ').1 i ∈ I ^ (m + 1) := by
    intro τ τ' m hm i
    have hsub : (Φ τ).1 i - (Φ τ').1 i =
        -(b ^ p * (E.mulVec (F τ.1 τ.2 - F τ'.1 τ'.2)) i) := by
      rw [Matrix.mulVec_sub, Pi.sub_apply]
      show -(b ^ p) * _ - -(b ^ p) * _ = _
      ring
    rw [hsub]
    exact neg_mem (pow_mul_mem_pow_succ _ _ hp
      (mulVec_mem_of_forall_mem _ E (hF τ.1 τ.2 τ'.1 τ'.2 m hm) i))
  let seq : ℕ → Bun := fun k ↦ Φ^[k] ⟨0, by simp⟩
  have hseq : ∀ k, seq (k + 1) = Φ (seq k) := fun k ↦ Function.iterate_succ_apply' _ _ _
  have hstep : ∀ k i, (seq (k + 1)).1 i - (seq k).1 i ∈ I ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      have h := hΦ (seq (k + 1)) (seq k) k ih i
      rwa [← hseq (k + 1), ← hseq k] at h
  obtain ⟨τs, hd⟩ : ∃ L : Fin N → B, ∀ k i, L i - (seq k).1 i ∈ I ^ k :=
    exists_limit_of_sub_mem_pow I (fun k ↦ (seq k).1) hstep
  have hτ : r • τs = E.mulVec τs := by
    funext i
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_mem_pow I fun k ↦ ?_
    have hk := congrFun (seq k).2 i
    have h : (r • τs) i - (E.mulVec τs) i =
        r * (τs - (seq k).1) i - (E.mulVec (τs - (seq k).1)) i := by
      simp only [Matrix.mulVec_sub, Pi.sub_apply]
      rw [← hk]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [h]
    exact sub_mem (Ideal.mul_mem_left _ _ (hd k i)) (mulVec_mem_of_forall_mem _ E (hd k) i)
  have hfix : (Φ ⟨τs, hτ⟩).1 = τs := by
    funext i
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_mem_pow I fun k ↦ ?_
    have h₂ : τs i - (seq (k + 1)).1 i ∈ I ^ (k + 1) := hd (k + 1) i
    rw [hseq k, ← neg_mem_iff, neg_sub] at h₂
    rw [← sub_add_sub_cancel _ ((Φ (seq k)).1 i)]
    exact add_mem (Ideal.pow_le_pow_right (by lia) (hΦ ⟨τs, hτ⟩ (seq k) k (hd k) i))
      (Ideal.pow_le_pow_right (by lia) h₂)
  exact ⟨τs, hτ, hfix.symm⟩

private theorem eq_zero_of_eq_pow_mul_of_mulVec_eq_zero {N c k : ℕ} (b : B)
    [IsHausdorff (Ideal.span {b}) B] (hk : Disjoint (torsionIdeal B b) (Ideal.span {b} ^ k))
    (E δ : Matrix (Fin N) (Fin N) B) (y w : Fin N → B) (hyw : ∀ i, y i = b ^ (k + 1) * w i)
    (hw : E.mulVec w = 0)
    (hrel : ∀ i, b ^ c * y i = ∑ j, (E i j + b ^ (c + (k + 1)) * δ i j) * y j) (i : Fin N) :
    y i = 0 := by
  have hEy : ∀ i, ∑ j, E i j * y j = 0 := fun i ↦ by
    have h := congrFun (congrArg E.mulVec (funext hyw : y = b ^ (k + 1) • w)) i
    rwa [Matrix.mulVec_smul, hw, smul_zero] at h
  have hz : ∀ i, b ^ c * y i = b ^ (k + 1) * ∑ j, δ i j * (b ^ c * y j) := fun i ↦ by
    rw [hrel i, Finset.mul_sum]
    simp only [add_mul, Finset.sum_add_distrib, hEy i, zero_add]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have h₀ : b ^ c * y i = 0 := eq_zero_of_forall_mem_pow (Ideal.span {b}) fun m ↦
    forall_mem_pow_of_eq_pow_mul_sum b (by lia) (fun i ↦ b ^ c * y i) δ hz m i
  refine Submodule.disjoint_def.mp hk _ ((mem_torsionIdeal_iff B b _).mpr ⟨c, h₀⟩) ?_
  rw [hyw i]
  exact Ideal.pow_le_pow_right (by lia)
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _))

/-- In a quotient of an `x`-adically complete ring, the image of `x` lies in the Jacobson
radical. -/
private theorem mk_mem_jacobson_bot_of_isAdicComplete {C : Type*} [CommRing C] (x : C)
    [IsAdicComplete (Ideal.span {x}) C] (K : Ideal C) :
    Ideal.Quotient.mk K x ∈ Ideal.jacobson ⊥ := by
  rw [Ideal.mem_jacobson_bot]
  intro q
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_mul, ← map_one (Ideal.Quotient.mk K), ← map_add]
  exact (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot (I := Ideal.span {x})
    (Ideal.mem_span_singleton_self x)) q).map _

end Aux

private theorem map_eq_zero_of_perturbed {A : Type u} [CommRing A] (a : A)
    {B : Type v} [CommRing B] [Algebra A B] [IsHausdorff (Ideal.span {algebraMap A B a}) B]
    {C : Type w} [CommRing C] [Algebra A C] {N c k : ℕ}
    (hk : Disjoint (torsionIdeal B (algebraMap A B a)) (Ideal.span {algebraMap A B a} ^ k))
    (β : B →ₐ[A] C) (u : C →ₐ[A] B) (hu : ∀ b, u (β b) = b) (T t H : Fin N → C)
    (hH : ∀ i, T i = t i - algebraMap A C a ^ (c + k + 1) * H i)
    (E : Matrix (Fin N) (Fin N) B) (hE : E * E = algebraMap A B a ^ c • E)
    (hT : ∀ i, u (T i) = (-(algebraMap A B a ^ (k + 1)) • E.mulVec fun j => u (H j)) i)
    (E0 : Matrix (Fin N) (Fin N) C)
    (hE0 : ∀ i j, E0 i j - β (E i j) ∈ Ideal.span {algebraMap A C a} ^ (c + (k + 1)))
    (hrel : algebraMap A C a ^ c • t = E0.mulVec t) (i : Fin N) : u (t i) = 0 := by
  set α := algebraMap A B a
  set αC := algebraMap A C a
  have huα : u αC = α := u.commutes a
  set v : Fin N → B := fun i ↦ u (H i) with hv
  set w : Fin N → B := α ^ c • v - E.mulVec v with hw
  have hyw : ∀ i, u (t i) = α ^ (k + 1) * w i := by
    intro i
    have h : t i = T i + αC ^ (c + k + 1) * H i := by rw [hH i]; ring
    rw [h, map_add, map_mul, map_pow, huα, hT]
    simp only [hw, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hv]
    ring
  have hEw : E.mulVec w = 0 := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hE, Matrix.smul_mulVec,
      sub_self]
  have hD : ∀ i j, ∃ d : B, u (E0 i j) = E i j + α ^ (c + (k + 1)) * d := by
    intro i j
    have h := hE0 i j
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
    obtain ⟨e, he⟩ := h
    refine ⟨u e, ?_⟩
    have h := congrArg u he
    rw [map_mul, map_sub, map_pow, huα, hu] at h
    linear_combination -1 * h
  choose δ hδ using hD
  refine eq_zero_of_eq_pow_mul_of_mulVec_eq_zero (c := c) α hk E δ (fun i ↦ u (t i)) w hyw hEw
    (fun i ↦ ?_) i
  have h := congrArg u (congrFun hrel i)
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, map_mul, map_pow, map_sum,
    huα, hδ] using h

private theorem surjective_mkₐ_comp_of_ker_le {A : Type u} [CommRing A] (a : A)
    {B : Type v} [CommRing B] [Algebra A B] [IsAdicComplete (Ideal.span {algebraMap A B a}) B]
    {C : Type w} [CommRing C] [Algebra A C] [IsNoetherianRing C]
    [IsAdicComplete (Ideal.span {algebraMap A C a}) C] {N n : ℕ}
    (β : B →ₐ[A] C) (s : C →ₐ[A] B) (hs : ∀ b, s (β b) = b) (T t H : Fin N → C)
    (hker : RingHom.ker s ≤ Ideal.span (Set.range T))
    (hH : ∀ i, T i = t i - algebraMap A C a ^ (n + 1) * H i) :
    Function.Surjective ((Ideal.Quotient.mkₐ A (Ideal.span (Set.range t))).comp β) := by
  set α := algebraMap A B a
  set αC := algebraMap A C a
  set I := Ideal.span {α}
  set K := Ideal.span (Set.range t)
  set φ : B →ₐ[A] C ⧸ K := (Ideal.Quotient.mkₐ A K).comp β
  have hφα : (φ : B →+* C ⧸ K) α = Ideal.Quotient.mk K αC := by
    show Ideal.Quotient.mk K (β (algebraMap A B a)) = _
    rw [β.commutes]
  have hjac : I.map (φ : B →+* C ⧸ K) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, hφα]
    exact mk_mem_jacobson_bot_of_isAdicComplete αC K
  have : IsHausdorff (I.map (φ : B →+* C ⧸ K)) (C ⧸ K) := IsHausdorff.of_le_jacobson _ _ hjac
  have hmod : Function.Surjective
      ((Ideal.Quotient.mk (I.map (φ : B →+* C ⧸ K))).comp (φ : B →+* C ⧸ K)) := by
    intro q
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨s y, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq]
    have hy : y - β (s y) ∈ Ideal.span (Set.range T) :=
      hker (by rw [RingHom.mem_ker, map_sub, hs, sub_self])
    obtain ⟨d, hdT⟩ := Ideal.mem_span_range_iff_exists_fun.mp hy
    set r : C := -(αC ^ n * ∑ i, d i * H i) with hr
    have hsum : ∑ i, d i * T i = ∑ i, d i * t i + αC * r := by
      have e : ∀ i, d i * T i = d i * t i - αC * (αC ^ n * (d i * H i)) := fun i ↦ by
        rw [hH i]
        ring
      rw [Finset.sum_congr rfl fun i _ ↦ e i, Finset.sum_sub_distrib, hr, ← Finset.mul_sum,
        ← Finset.mul_sum, mul_neg, sub_eq_add_neg]
    have hmem : y - β (s y) - αC * r ∈ K := by
      rw [← hdT, hsum, add_sub_cancel_right]
      exact Ideal.sum_mem K fun i _ ↦ Ideal.mul_mem_left K (d i) (Ideal.subset_span ⟨i, rfl⟩)
    have e₁ : Ideal.Quotient.mk K (y - β (s y)) =
        Ideal.Quotient.mk K αC * Ideal.Quotient.mk K r := by
      rw [← map_mul]
      exact Ideal.Quotient.eq.mpr hmem
    have e₂ : (φ : B →+* C ⧸ K) (s y) - Ideal.Quotient.mk K y =
        -(Ideal.Quotient.mk K (y - β (s y))) := by
      rw [map_sub, neg_sub]
      rfl
    rw [e₂, e₁, ← hφα]
    exact neg_mem (Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self α)))
  exact surjective_of_mk_map_comp_surjective (I := I) (φ : B →+* C ⧸ K) hmod

/-- Let `B`, `C` be Noetherian `a`-adically complete `A`-algebras, `β : B → C` and `s : C → B`
`A`-algebra maps with `s ∘ β = id`, and `T₁, …, T_N ∈ C` with `ker s ⊆ (T₁, …, T_N)`. Let
`E` be an `N × N` matrix over `B` with `E² = aᶜ E`, and suppose that each point `τ` of
`{τ ∈ Bᴺ : aᶜ τ = E τ}` gives an `A`-algebra map `ev τ : C → B` with `ev τ ∘ β = id`,
`ev τ (Tᵢ) = τᵢ`, and `ev τ ≡ ev τ'` modulo `aⁿ` whenever `τ ≡ τ'` modulo `aⁿ`.

Then there is an `n` such that for all `t₁, …, t_N ∈ C` with `tᵢ ≡ Tᵢ` modulo `aⁿ` and every
matrix `E₀` over `C` with `E₀ ≡ β(E)` modulo `aⁿ` and `aᶜ t = E₀ t`, the quotient
`C / (t₁, …, t_N)` is isomorphic to `B` as an `A`-algebra. -/
theorem exists_algEquiv_quotient_of_perturbed_zeroSection
    {A : Type u} [CommRing A] (a : A)
    {B : Type v} [CommRing B] [Algebra A B] [IsNoetherianRing B]
    [IsAdicComplete (Ideal.span {algebraMap A B a}) B]
    {C : Type w} [CommRing C] [Algebra A C] [IsNoetherianRing C]
    [IsAdicComplete (Ideal.span {algebraMap A C a}) C]
    {N c : ℕ} (β : B →ₐ[A] C) (s : C →ₐ[A] B) (hs : ∀ b, s (β b) = b)
    (T : Fin N → C) (hker : RingHom.ker s ≤ Ideal.span (Set.range T))
    (E : Matrix (Fin N) (Fin N) B) (hE : E * E = algebraMap A B (a ^ c) • E)
    (ev : (τ : Fin N → B) → algebraMap A B (a ^ c) • τ = E.mulVec τ → (C →ₐ[A] B))
    (hevβ : ∀ τ h b, ev τ h (β b) = b)
    (hevT : ∀ τ h i, ev τ h (T i) = τ i)
    (hcong : ∀ τ h τ' h' (n : ℕ), (∀ i, τ i - τ' i ∈ Ideal.span {algebraMap A B a} ^ n) →
      ∀ y, ev τ h y - ev τ' h' y ∈ Ideal.span {algebraMap A B a} ^ n) :
    ∃ n : ℕ, ∀ (t : Fin N → C) (E0 : Matrix (Fin N) (Fin N) C),
      (∀ i, t i - T i ∈ Ideal.span {algebraMap A C a} ^ n) →
      (∀ i j, E0 i j - β (E i j) ∈ Ideal.span {algebraMap A C a} ^ n) →
      algebraMap A C (a ^ c) • t = E0.mulVec t →
      Nonempty (B ≃ₐ[A] C ⧸ Ideal.span (Set.range t)) := by
  obtain ⟨k0, hk0⟩ := exists_disjoint_torsionIdeal_pow_span_singleton (algebraMap A B a)
  refine ⟨c + (k0 + 1), fun t E0 ht hE0 hrel ↦ ?_⟩
  have hH : ∀ i, ∃ h : C, T i = t i - algebraMap A C a ^ (c + k0 + 1) * h := fun i ↦ by
    have h := ht i
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
    obtain ⟨h, hh⟩ := h
    exact ⟨h, by linear_combination hh⟩
  choose H hH using hH
  obtain ⟨τs, hτ, hfix⟩ : ∃ τ h,
      τ = -(algebraMap A B a ^ (k0 + 1)) • E.mulVec fun i ↦ ev τ h (H i) :=
    exists_eq_neg_pow_smul_mulVec_of_continuous (algebraMap A B a) (algebraMap A B (a ^ c))
      (by lia) E hE (fun τ h i ↦ ev τ h (H i)) fun τ h τ' h' m hm i ↦ hcong τ h τ' h' m hm (H i)
  set K := Ideal.span (Set.range t)
  set u := ev τs hτ
  have hKu : K ≤ RingHom.ker u := Ideal.span_le.mpr <| Set.range_subset_iff.mpr fun i ↦
    map_eq_zero_of_perturbed a hk0 β u (hevβ τs hτ) T t H hH E (by rw [hE, map_pow])
      (fun i ↦ (hevT τs hτ i).trans (congrFun hfix i)) E0 hE0 (by rwa [← map_pow]) i
  let φ : B →ₐ[A] C ⧸ K := (Ideal.Quotient.mkₐ A K).comp β
  have hleft : Function.LeftInverse (Ideal.Quotient.liftₐ K u hKu) φ := hevβ τs hτ
  exact ⟨AlgEquiv.ofBijective φ
    ⟨hleft.injective, surjective_mkₐ_comp_of_ker_le a β s hs T t H hker hH⟩⟩

end Rig
