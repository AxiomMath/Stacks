module

public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Polynomial.Tower
public import StacksFrontier.AlgebraicGeometry.Groupoids.CechGroupoid

/-!
# A counterexample to Tag 04LP as printed

Tag 04LP asserts that for a groupoid scheme `(U, R, s, t, c)` over `S` with `U = Spec k`, `k` a
field, and any two points `r, r'` of `R`, there are a field extension `k'/k`, points `r₁, r₂` of
`R ×_{s, Spec k} Spec k'` and an automorphism `φ` of `R ×_{s, Spec k} Spec k'` over `Spec k'`
with `φ(r₁) = r₂`, `pr₀(r₁) = r` and `pr₀(r₂) = r'`.  This file proves that statement false.

## Main definitions

* `Stacks.Groupoids.GroupoidOnFieldHomogeneousStatement`: the statement of Tag 04LP as printed.
* `Stacks.Groupoids.CoarseGroupoid.groupoid`: the coarse groupoid of `Spec ℚ(T)` over `Spec ℚ`,
  whose arrow scheme is `Spec ℚ(T) ×_{Spec ℚ} Spec ℚ(T)`.

## Main results

* `Stacks.Groupoids.not_groupoidOnFieldHomogeneousStatement`: the statement of Tag 04LP as
  printed is false.
* `Stacks.Groupoids.CoarseGroupoid.not_exists_iso_self_mapping`: for the coarse groupoid of
  `Spec ℚ(T)`, the point `t = s` cannot be moved to a point over `s = t²` by an automorphism of
  any base change along the source map.
* `Stacks.Groupoids.CoarseGroupoid.false_of_mem`: the ring-theoretic core.

## Implementation notes

Write `A = K ⊗_ℚ ℚ(T)` for a field `K` of characteristic zero, `u = 1 ⊗ T`, and let `c ∈ K` be
transcendental over `ℚ`.  For the coarse groupoid with `k = ℚ(T)` and an extension `K` of `k`,
the base change `R ×_{s, Spec k} Spec K` is `Spec A`, the projection to `R` is dual to
`a ⊗ b ↦ γ(b) ⊗ a` (with `γ : k → K` and `c = γ(T)`), the point `t = s` pulls back to primes
containing `u - c`, and the point `s = t²` pulls back to primes containing `c - u²`.

The core `false_of_mem` shows that no injective `K`-algebra endomorphism `f` of `A` and prime
`P` satisfy `u - c ∈ P` and `c - f(u)² ∈ P`.  Evaluation at `u = c` gives a value `d` of `f(u)`
with `d² = c`.  Both `W = f(u)` and `W - 1` are units, and every element of `A` times a nonzero
element of `ℚ[u]` is a polynomial in `u` over `K`; a unit of that shape divides a nonzero
rational polynomial, so its monic part has coefficients algebraic over `ℚ`.  Comparing the two
expressions for `W` and `W - 1` shows that either `W` is a constant, which contradicts
injectivity, or `d` is a quotient of polynomials in `c` with coefficients algebraic over `ℚ`,
and then `d² = c` contradicts transcendence of `c` for degree reasons.

The arithmetic heart of the same obstruction, stated for fractional linear maps, is
`Stacks.Groupoids.linearFractional_sq_ne_of_transcendental`.

## References

* [Stacks Project, Tag 0233](https://stacks.math.columbia.edu/tag/0233)
* [Stacks Project, Tag 02YF](https://stacks.math.columbia.edu/tag/02YF)
* [Stacks Project, Tag 04LP](https://stacks.math.columbia.edu/tag/04LP)
-/

@[expose] public section

open Polynomial TensorProduct

namespace Stacks.Groupoids.CoarseGroupoid

/-- The variable `T` of the rational function field `ℚ(T)`. -/
noncomputable abbrev varT : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) X

theorem aeval_varT (p : ℚ[X]) : aeval varT p = algebraMap ℚ[X] (RatFunc ℚ) p := by
  rw [Polynomial.aeval_algebraMap_apply, aeval_X_left_apply]

/-- The variable of `ℚ(T)` is transcendental over `ℚ`. -/
theorem transcendental_varT : Transcendental ℚ varT := by
  rw [transcendental_iff_injective]
  intro p q h
  rw [aeval_varT, aeval_varT] at h
  exact IsFractionRing.injective ℚ[X] (RatFunc ℚ) h

variable (K : Type*) [Field K] [CharZero K]

/-- The coordinate `u = 1 ⊗ T` of `K ⊗_ℚ ℚ(T)`. -/
noncomputable abbrev coordU : K ⊗[ℚ] RatFunc ℚ := (1 : K) ⊗ₜ[ℚ] varT

/-- The element `1 ⊗ s(T)` of `K ⊗_ℚ ℚ(T)` for a polynomial `s` over `ℚ`. -/
noncomputable abbrev polyD (s : ℚ[X]) : K ⊗[ℚ] RatFunc ℚ :=
  (1 : K) ⊗ₜ[ℚ] algebraMap ℚ[X] (RatFunc ℚ) s

variable {K}

theorem polyD_mul (s s' : ℚ[X]) : polyD K (s * s') = polyD K s * polyD K s' := by
  simp [polyD, Algebra.TensorProduct.tmul_mul_tmul]

theorem isUnit_tmul {b : RatFunc ℚ} (hb : b ≠ 0) : IsUnit ((1 : K) ⊗ₜ[ℚ] b) :=
  (isUnit_iff_ne_zero.mpr hb).map (Algebra.TensorProduct.includeRight (R := ℚ) (A := K))

theorem isUnit_polyD {s : ℚ[X]} (hs : s ≠ 0) : IsUnit (polyD K s) :=
  isUnit_tmul ((map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr hs)

theorem aeval_coordU_map (s : ℚ[X]) :
    aeval (coordU K) (s.map (algebraMap ℚ K)) = polyD K s := by
  rw [aeval_map_algebraMap,
    show coordU K = Algebra.TensorProduct.includeRight (R := ℚ) (A := K) varT from rfl,
    aeval_algHom_apply, aeval_varT]
  rfl

/-- Evaluation `K ⊗_ℚ ℚ(T) → K` at an element `e` of `K` transcendental over `ℚ`. -/
noncomputable def evalAt (e : K) (he : Transcendental ℚ e) : K ⊗[ℚ] RatFunc ℚ →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K)
    (IsFractionRing.liftAlgHom (K := RatFunc ℚ) (transcendental_iff_injective.mp he))
    (fun _ _ => Commute.all _ _)

theorem evalAt_coordU (e : K) (he : Transcendental ℚ e) : evalAt e he (coordU K) = e := by
  simp [evalAt, IsFractionRing.liftAlgHom_apply]

theorem evalAt_aeval (e : K) (he : Transcendental ℚ e) (g : K[X]) :
    evalAt e he (aeval (coordU K) g) = g.eval e := by
  have := aeval_algHom_apply (evalAt e he) (coordU K) g
  rw [evalAt_coordU] at this
  rw [← this, coe_aeval_eq_eval]

theorem transcendental_add_algebraMap {c : K} (hc : Transcendental ℚ c) (q : ℚ) :
    Transcendental ℚ (c + algebraMap ℚ K q) := by
  intro h
  apply hc
  simpa using h.sub (isAlgebraic_algebraMap q)

/-- Polynomials over `K` in `u` are determined by their value in `K ⊗_ℚ ℚ(T)`. -/
theorem aeval_coordU_injective {c : K} (hc : Transcendental ℚ c) :
    Function.Injective (aeval (R := K) (coordU K)) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinj : Function.Injective (fun q : ℚ => c + algebraMap ℚ K q) :=
    (add_right_injective c).comp (algebraMap ℚ K).injective
  refine Set.infinite_of_injective_forall_mem hinj (fun q => ?_)
  have := congrArg (evalAt _ (transcendental_add_algebraMap hc q)) hg
  rw [evalAt_aeval, map_zero] at this
  exact this

/-- Every element of `K ⊗_ℚ ℚ(T)`, multiplied by a suitable nonzero element of `ℚ[u]`, is a
polynomial in `u` over `K`. -/
theorem exists_mul_polyD_eq_aeval (a : K ⊗[ℚ] RatFunc ℚ) :
    ∃ (g : K[X]) (s : ℚ[X]), s ≠ 0 ∧ a * polyD K s = aeval (coordU K) g := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul x b =>
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := ℚ[X]) b
    refine ⟨C x * p.map (algebraMap ℚ K), q, nonZeroDivisors.ne_zero hq, ?_⟩
    have hq' : algebraMap ℚ[X] (RatFunc ℚ) q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
        (nonZeroDivisors.ne_zero hq)
    rw [map_mul, aeval_C, aeval_coordU_map]
    simp [polyD, Algebra.TensorProduct.tmul_mul_tmul, div_mul_cancel₀ _ hq',
      Algebra.TensorProduct.algebraMap_apply]
  | add a b ha hb =>
    obtain ⟨g₁, s₁, hs₁, h₁⟩ := ha
    obtain ⟨g₂, s₂, hs₂, h₂⟩ := hb
    refine ⟨g₁ * s₂.map (algebraMap ℚ K) + g₂ * s₁.map (algebraMap ℚ K), s₁ * s₂,
      mul_ne_zero hs₁ hs₂, ?_⟩
    rw [map_add, map_mul, map_mul, ← h₁, ← h₂, aeval_coordU_map, aeval_coordU_map, polyD_mul]
    ring

/-- A unit of `K ⊗_ℚ ℚ(T)` which is a polynomial in `u` over a nonzero element of `ℚ[u]` has
numerator dividing a nonzero rational polynomial. -/
theorem exists_dvd_map_of_isUnit {c : K} (hc : Transcendental ℚ c)
    {a : K ⊗[ℚ] RatFunc ℚ} (ha : IsUnit a) {g : K[X]} {s : ℚ[X]} (hs : s ≠ 0)
    (h : a * polyD K s = aeval (coordU K) g) :
    ∃ h' : ℚ[X], h' ≠ 0 ∧ g ∣ h'.map (algebraMap ℚ K) := by
  obtain ⟨g', s', hs', h'⟩ := exists_mul_polyD_eq_aeval (↑ha.unit⁻¹ : K ⊗[ℚ] RatFunc ℚ)
  refine ⟨s * s', mul_ne_zero hs hs', g', aeval_coordU_injective hc ?_⟩
  rw [map_mul (aeval (coordU K)) g g', ← h, ← h', aeval_coordU_map, polyD_mul]
  linear_combination (-(polyD K s * polyD K s')) * ha.mul_val_inv

variable (K) in
/-- Polynomials over `K` all of whose coefficients are algebraic over `ℚ`. -/
noncomputable abbrev algCoeffs : Subring K[X] :=
  liftsRing (algebraMap (algebraicClosure ℚ K) K)

theorem mem_algCoeffs_iff {P : K[X]} :
    P ∈ algCoeffs K ↔ ∀ n, P.coeff n ∈ algebraicClosure ℚ K := by
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts]
  refine forall_congr' fun n => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.2

theorem C_mem_algCoeffs {x : K} (hx : x ∈ algebraicClosure ℚ K) : C x ∈ algCoeffs K := by
  rw [mem_algCoeffs_iff]
  intro n
  rw [coeff_C]
  split_ifs
  · exact hx
  · exact zero_mem _

theorem X_mem_algCoeffs : (X : K[X]) ∈ algCoeffs K := by
  rw [mem_algCoeffs_iff]
  intro n
  rw [coeff_X]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem map_mem_algCoeffs (s : ℚ[X]) : s.map (algebraMap ℚ K) ∈ algCoeffs K := by
  rw [mem_algCoeffs_iff]
  intro n
  rw [coeff_map]
  exact IntermediateField.algebraMap_mem _ _

/-- A monic factor over `K` of a nonzero polynomial over `ℚ` has coefficients algebraic
over `ℚ`. -/
theorem mem_algCoeffs_of_dvd {g : K[X]} (hg : g.Monic) {h : ℚ[X]} (hh : h ≠ 0)
    (hd : g ∣ h.map (algebraMap ℚ K)) : g ∈ algCoeffs K := by
  have hgΩ : (g.map (algebraMap K (AlgebraicClosure K))).Monic := hg.map _
  have hroot : ∀ α ∈ (g.map (algebraMap K (AlgebraicClosure K))).roots,
      α ∈ algebraicClosure ℚ (AlgebraicClosure K) := by
    intro α hα
    rw [mem_algebraicClosure_iff]
    refine ⟨h, hh, ?_⟩
    rw [mem_roots hgΩ.ne_zero] at hα
    have hdΩ : g.map (algebraMap K (AlgebraicClosure K)) ∣
        h.map (algebraMap ℚ (AlgebraicClosure K)) := by
      have := Polynomial.map_dvd (algebraMap K (AlgebraicClosure K)) hd
      rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
    rw [aeval_def, eval₂_eq_eval_map]
    exact hα.dvd hdΩ
  have hprod : ((g.map (algebraMap K (AlgebraicClosure K))).roots.map fun a => X - C a).prod =
      g.map (algebraMap K (AlgebraicClosure K)) :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hgΩ IsAlgClosed.card_roots_eq_natDegree
  have hmem : g.map (algebraMap K (AlgebraicClosure K)) ∈ algCoeffs (AlgebraicClosure K) := by
    rw [← hprod]
    refine Subring.multiset_prod_mem _ _ fun p hp => ?_
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp hp
    exact sub_mem X_mem_algCoeffs (C_mem_algCoeffs (hroot α hα))
  rw [mem_algCoeffs_iff] at hmem ⊢
  intro n
  have := hmem n
  rw [coeff_map, mem_algebraicClosure_iff] at this
  rw [mem_algebraicClosure_iff]
  exact (isAlgebraic_algebraMap_iff (algebraMap K (AlgebraicClosure K)).injective).mp this

/-- A polynomial with coefficients algebraic over `ℚ` vanishing at an element transcendental over
`ℚ` is zero. -/
theorem eq_zero_of_mem_algCoeffs {c : K} (hc : Transcendental ℚ c) {P : K[X]}
    (hP : P ∈ algCoeffs K) (h : P.eval c = 0) : P = 0 := by
  rw [← lifts_iff_liftsRing, mem_lifts] at hP
  obtain ⟨Q, rfl⟩ := hP
  have hQ : aeval c Q = 0 := by
    rw [aeval_def, eval₂_eq_eval_map]
    exact h
  rw [transcendental_iff.mp hc.algebraicClosure Q hQ, Polynomial.map_zero]

/-- Modulo an ideal containing `u - c`, every element of `K ⊗_ℚ ℚ(T)` is congruent to its value
under evaluation at `c`. -/
theorem sub_algebraMap_evalAt_mem {c : K} (hc : Transcendental ℚ c)
    {P : Ideal (K ⊗[ℚ] RatFunc ℚ)} (h₁ : coordU K - algebraMap K _ c ∈ P)
    (a : K ⊗[ℚ] RatFunc ℚ) : a - algebraMap K _ (evalAt c hc a) ∈ P := by
  let F₁ : RatFunc ℚ →+* (K ⊗[ℚ] RatFunc ℚ) ⧸ P := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := RatFunc ℚ)).toRingHom
  let F₂ : RatFunc ℚ →+* (K ⊗[ℚ] RatFunc ℚ) ⧸ P := (Ideal.Quotient.mk P).comp
    ((algebraMap K (K ⊗[ℚ] RatFunc ℚ)).comp ((evalAt c hc).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := RatFunc ℚ)).toRingHom))
  have hρ : F₁ = F₂ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X])
    apply Polynomial.ringHom_ext
    · intro q
      exact RingHom.congr_fun (RingHom.ext_rat ((F₁.comp (algebraMap ℚ[X] (RatFunc ℚ))).comp C)
        ((F₂.comp (algebraMap ℚ[X] (RatFunc ℚ))).comp C)) q
    · change Ideal.Quotient.mk P (coordU K) =
        Ideal.Quotient.mk P (algebraMap K _ (evalAt c hc (coordU K)))
      rw [evalAt_coordU]
      exact Ideal.Quotient.eq.mpr h₁
  have hb : ∀ b : RatFunc ℚ, (1 : K) ⊗ₜ[ℚ] b -
      algebraMap K (K ⊗[ℚ] RatFunc ℚ) (evalAt c hc ((1 : K) ⊗ₜ b)) ∈ P := fun b =>
    Ideal.Quotient.eq.mp (show Ideal.Quotient.mk P ((1 : K) ⊗ₜ[ℚ] b) =
      Ideal.Quotient.mk P (algebraMap K _ (evalAt c hc ((1 : K) ⊗ₜ b))) from
      RingHom.congr_fun hρ b)
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    have hx : x ⊗ₜ[ℚ] b = algebraMap K (K ⊗[ℚ] RatFunc ℚ) x * ((1 : K) ⊗ₜ[ℚ] b) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    have e : x ⊗ₜ[ℚ] b - algebraMap K _ (evalAt c hc (x ⊗ₜ b)) =
        algebraMap K _ x * ((1 : K) ⊗ₜ[ℚ] b - algebraMap K _ (evalAt c hc ((1 : K) ⊗ₜ b))) := by
      rw [hx, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, map_mul,
        mul_sub]
    rw [e]
    exact P.mul_mem_left _ (hb b)
  | add a b ha hb' =>
    rw [map_add, map_add, add_sub_add_comm]
    exact P.add_mem ha hb'

/-- The ring-theoretic core of the counterexample to Tag 04LP: no injective `K`-algebra
endomorphism `f` of `K ⊗_ℚ ℚ(T)` and proper ideal `P` satisfy `u - c ∈ P` and
`c - f(u)² ∈ P`, for `c ∈ K` transcendental over `ℚ`. -/
theorem false_of_mem {c : K} (hc : Transcendental ℚ c)
    (f : K ⊗[ℚ] RatFunc ℚ →ₐ[K] K ⊗[ℚ] RatFunc ℚ) (hf : Function.Injective f)
    (P : Ideal (K ⊗[ℚ] RatFunc ℚ)) (hP : P ≠ ⊤)
    (h₁ : coordU K - algebraMap K _ c ∈ P) (h₂ : algebraMap K _ c - f (coordU K) ^ 2 ∈ P) :
    False := by
  obtain ⟨W, hWdef⟩ : ∃ w, w = f (coordU K) := ⟨_, rfl⟩
  rw [← hWdef] at h₂
  -- The value of `W` at `u = c` is a square root of `c`.
  have hd : evalAt c hc W ^ 2 = c := by
    have h3 : algebraMap K (K ⊗[ℚ] RatFunc ℚ) (c - evalAt c hc W ^ 2) ∈ P := by
      have e : algebraMap K (K ⊗[ℚ] RatFunc ℚ) (c - evalAt c hc W ^ 2) =
          (algebraMap K _ c - W ^ 2) +
            (W - algebraMap K _ (evalAt c hc W)) * (W + algebraMap K _ (evalAt c hc W)) := by
        rw [map_sub, map_pow]; ring
      rw [e]
      exact P.add_mem h₂ (P.mul_mem_right _ (sub_algebraMap_evalAt_mem hc h₁ W))
    by_contra hne
    exact hP (Ideal.eq_top_of_isUnit_mem _ h3
      ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne))).map _))
  have hinj := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have hT : varT ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hT1 : varT - 1 ≠ 0 := by
    have : varT - 1 = algebraMap ℚ[X] (RatFunc ℚ) (X - 1) := by simp [varT]
    rw [this]
    exact (map_ne_zero_iff _ hinj).mpr (by simpa using X_sub_C_ne_zero (1 : ℚ))
  have hW : IsUnit W := by
    rw [hWdef]
    exact (isUnit_tmul hT).map f
  have hW1 : IsUnit (W - 1) := by
    have : W - 1 = f ((1 : K) ⊗ₜ[ℚ] (varT - 1)) := by
      rw [hWdef, TensorProduct.tmul_sub, map_sub, ← Algebra.TensorProduct.one_def, map_one]
    rw [this]
    exact (isUnit_tmul hT1).map f
  obtain ⟨g, s, hs, hrep⟩ := exists_mul_polyD_eq_aeval W
  obtain ⟨smap, hsmap⟩ : ∃ p : K[X], p = s.map (algebraMap ℚ K) := ⟨_, rfl⟩
  have hsm : aeval (coordU K) smap = polyD K s := by rw [hsmap, aeval_coordU_map]
  have hsL : smap ∈ algCoeffs K := by rw [hsmap]; exact map_mem_algCoeffs s
  have hs0 : smap ≠ 0 := by rw [hsmap]; exact Polynomial.map_ne_zero hs
  have hrep1 : (W - 1) * polyD K s = aeval (coordU K) (g - smap) := by
    rw [sub_mul, hrep, one_mul, map_sub, hsm]
  have hDu : IsUnit (polyD K s) := isUnit_polyD hs
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [map_zero] at hrep
    exact (hW.mul hDu).ne_zero hrep
  have hg1 : g - smap ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hrep1
    exact (hW1.mul hDu).ne_zero hrep1
  obtain ⟨h, hh, hdvd⟩ := exists_dvd_map_of_isUnit hc hW hs hrep
  obtain ⟨h', hh', hdvd'⟩ := exists_dvd_map_of_isUnit hc hW1 hs hrep1
  have hcoef : ∀ {Q : K[X]}, Q ∈ algCoeffs K → ∀ n, Q.coeff n ∈ algebraicClosure ℚ K :=
    fun hQ => mem_algCoeffs_iff.mp hQ
  -- Normalize the two numerators.
  set a₀ := g.leadingCoeff with ha₀def
  set g₀ := g * C a₀⁻¹ with hg₀def
  have ha₀ : a₀ ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have hg₀m : g₀.Monic := monic_mul_leadingCoeff_inv hg0
  have hgg₀ : g = C a₀ * g₀ := by
    rw [hg₀def, mul_left_comm, ← C_mul, mul_inv_cancel₀ ha₀, C_1, mul_one]
  have hg₀L : g₀ ∈ algCoeffs K :=
    mem_algCoeffs_of_dvd hg₀m hh (dvd_trans ⟨C a₀, by rw [hgg₀, mul_comm]⟩ hdvd)
  set b₀ := (g - smap).leadingCoeff with hb₀def
  set g₁ := (g - smap) * C b₀⁻¹ with hg₁def
  have hb₀ : b₀ ≠ 0 := leadingCoeff_ne_zero.mpr hg1
  have hgg₁ : g - smap = C b₀ * g₁ := by
    rw [hg₁def, mul_left_comm, ← C_mul, mul_inv_cancel₀ hb₀, C_1, mul_one]
  have hg₁L : g₁ ∈ algCoeffs K :=
    mem_algCoeffs_of_dvd (monic_mul_leadingCoeff_inv hg1) hh'
      (dvd_trans ⟨C b₀, by rw [hgg₁, mul_comm]⟩ hdvd')
  have heq : C a₀ * g₀ - smap = C b₀ * g₁ := by rw [← hgg₀, hgg₁]
  -- Either the leading coefficient `a₀` is algebraic over `ℚ`, or `smap` is a multiple of `g₀`.
  have key : a₀ ∈ algebraicClosure ℚ K ∨ smap = C (smap.coeff g₀.natDegree) * g₀ := by
    have hcj : a₀ - smap.coeff g₀.natDegree = b₀ * g₁.coeff g₀.natDegree := by
      have := congrArg (fun p : K[X] => p.coeff g₀.natDegree) heq
      simp only [coeff_sub, coeff_C_mul, hg₀m.coeff_natDegree, mul_one] at this
      exact this
    by_cases hg1j : g₁.coeff g₀.natDegree = 0
    · left
      rw [hg1j, mul_zero, sub_eq_zero] at hcj
      rw [hcj]
      exact hcoef hsL _
    · obtain ⟨ginv, hginv⟩ : ∃ x : K, x = (g₁.coeff g₀.natDegree)⁻¹ := ⟨_, rfl⟩
      have hmu : C b₀ = (C a₀ - C (smap.coeff g₀.natDegree)) * C ginv := by
        rw [← C_sub, ← C_mul, hcj, mul_assoc, hginv, mul_inv_cancel₀ hg1j, mul_one]
      have hQR : C a₀ * (g₀ - C ginv * g₁) =
          smap - C (smap.coeff g₀.natDegree) * C ginv * g₁ := by
        linear_combination heq + g₁ * hmu
      have hginvL : ginv ∈ algebraicClosure ℚ K := by
        rw [hginv]
        exact inv_mem (hcoef hg₁L _)
      have hQL : g₀ - C ginv * g₁ ∈ algCoeffs K :=
        sub_mem hg₀L (mul_mem (C_mem_algCoeffs hginvL) hg₁L)
      have hRL : smap - C (smap.coeff g₀.natDegree) * C ginv * g₁ ∈ algCoeffs K :=
        sub_mem hsL (mul_mem (mul_mem (C_mem_algCoeffs (hcoef hsL _))
          (C_mem_algCoeffs hginvL)) hg₁L)
      by_cases hQ : g₀ - C ginv * g₁ = 0
      · right
        have hR0 := hQR
        rw [hQ, mul_zero, eq_comm, sub_eq_zero] at hR0
        have hg₀' : g₀ = C ginv * g₁ := sub_eq_zero.mp hQ
        calc smap = C (smap.coeff g₀.natDegree) * C ginv * g₁ := hR0
          _ = C (smap.coeff g₀.natDegree) * g₀ := by rw [mul_assoc, ← hg₀']
      · left
        have hi : (g₀ - C ginv * g₁).coeff (g₀ - C ginv * g₁).natDegree ≠ 0 :=
          leadingCoeff_ne_zero.mpr hQ
        have hci : a₀ * (g₀ - C ginv * g₁).coeff (g₀ - C ginv * g₁).natDegree =
            (smap - C (smap.coeff g₀.natDegree) * C ginv * g₁).coeff
              (g₀ - C ginv * g₁).natDegree := by
          rw [← hQR, coeff_C_mul]
        have ha : a₀ = (smap - C (smap.coeff g₀.natDegree) * C ginv * g₁).coeff
            (g₀ - C ginv * g₁).natDegree /
              (g₀ - C ginv * g₁).coeff (g₀ - C ginv * g₁).natDegree := by
          rw [← hci, mul_div_cancel_right₀ _ hi]
        rw [ha]
        exact div_mem (hcoef hRL _) (hcoef hQL _)
  rcases key with hL | hβ
  · -- The value `evalAt c hc W = a₀ g₀(c) / s(c)` is a square root of `c` in `L(c)`.
    have hev : evalAt c hc W * smap.eval c = a₀ * g₀.eval c := by
      have := congrArg (evalAt c hc) hrep
      rw [map_mul, ← hsm, evalAt_aeval, evalAt_aeval, hgg₀, eval_mul, eval_C] at this
      exact this
    have hPL : C (a₀ ^ 2) * g₀ ^ 2 - X * smap ^ 2 ∈ algCoeffs K :=
      sub_mem (mul_mem (C_mem_algCoeffs (pow_mem hL 2)) (pow_mem hg₀L 2))
        (mul_mem X_mem_algCoeffs (pow_mem hsL 2))
    have hPe : (C (a₀ ^ 2) * g₀ ^ 2 - X * smap ^ 2).eval c = 0 := by
      simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      linear_combination (-(evalAt c hc W * smap.eval c + a₀ * g₀.eval c)) * hev +
        smap.eval c ^ 2 * hd
    have hP0 := sub_eq_zero.mp (eq_zero_of_mem_algCoeffs hc hPL hPe)
    have hdeg := congrArg natDegree hP0
    rw [natDegree_C_mul (pow_ne_zero 2 ha₀), natDegree_pow,
      natDegree_X_mul (pow_ne_zero 2 hs0), natDegree_pow] at hdeg
    omega
  · -- `W` is a constant, so `f` would map the non-constant `u` to a constant.
    set β := smap.coeff g₀.natDegree with hβdef
    have hDs : polyD K s = algebraMap K (K ⊗[ℚ] RatFunc ℚ) β * aeval (coordU K) g₀ := by
      rw [← hsm, hβ, map_mul, aeval_C]
    have hβ0 : β ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hDs
      exact hDu.ne_zero hDs
    have hWc : W = algebraMap K (K ⊗[ℚ] RatFunc ℚ) (a₀ / β) := by
      apply hDu.mul_right_cancel
      rw [hrep, hgg₀, map_mul, aeval_C, hDs, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hβ0]
    have hu : coordU K = algebraMap K (K ⊗[ℚ] RatFunc ℚ) (a₀ / β) :=
      hf (by rw [AlgHom.commutes, ← hWdef]; exact hWc)
    have e₁ := congrArg (evalAt c hc) hu
    have e₂ := congrArg (evalAt _ (transcendental_add_algebraMap hc 1)) hu
    rw [evalAt_coordU, AlgHom.commutes] at e₁ e₂
    rw [← e₁, map_one, add_eq_left] at e₂
    exact one_ne_zero e₂

end Stacks.Groupoids.CoarseGroupoid

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Groupoids

namespace CoarseGroupoid

/-- The morphism `Spec A ⟶ Spec R` of an `R`-algebra `A`. -/
noncomputable abbrev specAlgebraMap (R A : Type) [CommRing R] [CommRing A] [Algebra R A] :
    Spec (.of A) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- The scheme `Spec ℚ(T)` over `Spec ℚ`. -/
noncomputable def objects : Over (Spec (.of ℚ)) :=
  Over.mk (specAlgebraMap ℚ (RatFunc ℚ))

/-- The structure morphism of `Spec ℚ(T)`, as a morphism to the terminal object of schemes over
`Spec ℚ`. -/
noncomputable def toBase : objects ⟶ Over.mk (𝟙 (Spec (.of ℚ))) :=
  Over.homMk objects.hom (Category.comp_id _)

/-- The coarse groupoid of `Spec ℚ(T)` over `Spec ℚ`: its arrow scheme is
`Spec ℚ(T) ×_{Spec ℚ} Spec ℚ(T)`, with the two projections as target and source.  It is the
groupoid scheme that Tag 0233 attaches to the full equivalence relation on `Spec ℚ(T)`
(`AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation_cechPreRelation`). -/
noncomputable def groupoid : GroupoidScheme (Spec (.of ℚ)) :=
  cechGroupoid toBase

/-- The target map of the coarse groupoid, with codomain written as `Spec ℚ(T)`. -/
noncomputable def tgt : groupoid.arrows.left ⟶ Spec (.of (RatFunc ℚ)) :=
  groupoid.target.left

/-- The source map of the coarse groupoid, with codomain written as `Spec ℚ(T)`. -/
noncomputable def src : groupoid.arrows.left ⟶ Spec (.of (RatFunc ℚ)) :=
  groupoid.source.left

/-- The arrow scheme of the coarse groupoid is the fibre product of `Spec ℚ(T)` with itself over
`Spec ℚ`, with target and source as the two projections. -/
theorem isPullback_arrows :
    IsPullback tgt src (specAlgebraMap ℚ (RatFunc ℚ)) (specAlgebraMap ℚ (RatFunc ℚ)) :=
  (IsPullback.of_hasPullback toBase toBase).map (Over.forget _)

/-- The arrow scheme of the coarse groupoid is `Spec (ℚ(T) ⊗_ℚ ℚ(T))`, the left factor being the
target coordinate and the right factor the source coordinate. -/
noncomputable def arrowsIso :
    groupoid.arrows.left ≅ Spec (.of (RatFunc ℚ ⊗[ℚ] RatFunc ℚ)) :=
  isPullback_arrows.isoPullback ≪≫ pullbackSpecIso ℚ (RatFunc ℚ) (RatFunc ℚ)

theorem arrowsIso_inv_target :
    arrowsIso.inv ≫ tgt =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
  rw [arrowsIso, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_fst,
    pullbackSpecIso_inv_fst]

theorem arrowsIso_inv_source :
    arrowsIso.inv ≫ src =
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := RatFunc ℚ) (B := RatFunc ℚ)))) := by
  rw [arrowsIso, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_snd,
    pullbackSpecIso_inv_snd]

/-- The `ℚ`-algebra endomorphism `T ↦ T²` of `ℚ(T)`. -/
noncomputable def sqAlgHom : RatFunc ℚ →ₐ[ℚ] RatFunc ℚ :=
  IsFractionRing.liftAlgHom (K := RatFunc ℚ)
    (transcendental_iff_injective.mp (transcendental_varT.pow two_pos))

theorem sqAlgHom_varT : sqAlgHom varT = varT ^ 2 := by
  simp [sqAlgHom, IsFractionRing.liftAlgHom_apply]

/-- The multiplication `a ⊗ b ↦ a b` of `ℚ(T) ⊗_ℚ ℚ(T)`. -/
noncomputable def diagHom : RatFunc ℚ ⊗[ℚ] RatFunc ℚ →ₐ[ℚ] RatFunc ℚ :=
  Algebra.TensorProduct.lift (AlgHom.id ℚ _) (AlgHom.id ℚ _) fun _ _ => Commute.all _ _

/-- The map `a ⊗ b ↦ a b(T²)` of `ℚ(T) ⊗_ℚ ℚ(T)` to `ℚ(T)`. -/
noncomputable def graphHom : RatFunc ℚ ⊗[ℚ] RatFunc ℚ →ₐ[ℚ] RatFunc ℚ :=
  Algebra.TensorProduct.lift (AlgHom.id ℚ _) sqAlgHom fun _ _ => Commute.all _ _

/-- The identity arrow at the generic point: the point `t = s` of the arrow scheme. -/
noncomputable def diagPoint : groupoid.arrows.left :=
  arrowsIso.inv (⟨RingHom.ker diagHom.toRingHom, RingHom.ker_isPrime _⟩ :
    PrimeSpectrum (RatFunc ℚ ⊗[ℚ] RatFunc ℚ))

/-- The point `s = t²` of the arrow scheme. -/
noncomputable def graphPoint : groupoid.arrows.left :=
  arrowsIso.inv (⟨RingHom.ker graphHom.toRingHom, RingHom.ker_isPrime _⟩ :
    PrimeSpectrum (RatFunc ℚ ⊗[ℚ] RatFunc ℚ))

theorem hom_inv_apply {X Y : Scheme.{0}} (e : X ≅ Y) (y : Y) : e.hom (e.inv y) = y := by
  rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
  rfl

theorem inv_hom_apply {X Y : Scheme.{0}} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
  rfl

theorem inv_apply_injective {X Y : Scheme.{0}} (e : X ≅ Y) :
    Function.Injective fun y : Y => e.inv y := fun a b h => by
  simpa only [hom_inv_apply] using congrArg (fun x => e.hom x) h

/-- **The counterexample to Tag 04LP.**  For every field extension `K` of `ℚ(T)` there is no
point `r₁` of `R ×_{s, Spec ℚ(T)} Spec K` over the point `t = s` of the coarse groupoid `R`, and
no automorphism `φ` of `R ×_{s, Spec ℚ(T)} Spec K` over `Spec K`, such that `φ(r₁)` lies over
the point `s = t²`. -/
theorem not_exists_iso_self_mapping (K : Type) [Field K] [Algebra (RatFunc ℚ) K]
    (s : groupoid.arrows.left ⟶ Spec (.of (RatFunc ℚ))) (hs : s = src)
    (r₁ : ↥(pullback s (specAlgebraMap (RatFunc ℚ) K)))
    (φ : Over.mk (pullback.snd s (specAlgebraMap (RatFunc ℚ) K)) ≅
      Over.mk (pullback.snd s (specAlgebraMap (RatFunc ℚ) K)))
    (h₁ : pullback.fst s (specAlgebraMap (RatFunc ℚ) K) r₁ = diagPoint)
    (h₂ : pullback.fst s (specAlgebraMap (RatFunc ℚ) K) (φ.hom.left r₁) =
      graphPoint) : False := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc ℚ) K).injective
  have hR : IsPullback tgt s (specAlgebraMap ℚ (RatFunc ℚ))
      (specAlgebraMap ℚ (RatFunc ℚ)) := by
    rw [hs]
    exact isPullback_arrows
  have hsrc : arrowsIso.inv ≫ s = Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := RatFunc ℚ) (B := RatFunc ℚ)))) := by
    rw [hs]
    exact arrowsIso_inv_source
  have hX := (IsPullback.of_hasPullback s (specAlgebraMap (RatFunc ℚ) K)).paste_horiz hR
  have hgK : specAlgebraMap (RatFunc ℚ) K ≫ specAlgebraMap ℚ (RatFunc ℚ) =
      specAlgebraMap ℚ K := by
    simp only [specAlgebraMap, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext_rat _ _
  rw [hgK] at hX
  let ιX := hX.flip.isoPullback ≪≫ pullbackSpecIso ℚ K (RatFunc ℚ)
  have hιL : ιX.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
      pullback.snd s (specAlgebraMap (RatFunc ℚ) K) := by
    simp only [ιX, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst,
      IsPullback.isoPullback_hom_fst]
  have hιR : ιX.hom ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := RatFunc ℚ)))) =
      pullback.fst s (specAlgebraMap (RatFunc ℚ) K) ≫ tgt := by
    simp only [ιX, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_snd,
      IsPullback.isoPullback_hom_snd]
  -- The projection to the arrow scheme, as a ring map `ℚ(T) ⊗_ℚ ℚ(T) → K ⊗_ℚ ℚ(T)`.
  let γ : RatFunc ℚ →ₐ[ℚ] K := (algebraMap (RatFunc ℚ) K).toRatAlgHom
  let θ : RatFunc ℚ ⊗[ℚ] RatFunc ℚ →ₐ[ℚ] K ⊗[ℚ] RatFunc ℚ :=
    Algebra.TensorProduct.lift Algebra.TensorProduct.includeRight
      ((Algebra.TensorProduct.includeLeft (S := ℚ)).comp γ) fun _ _ => Commute.all _ _
  have hθ (a b : RatFunc ℚ) : θ (a ⊗ₜ b) = algebraMap (RatFunc ℚ) K b ⊗ₜ a := by
    simp [θ, γ, Algebra.TensorProduct.tmul_mul_tmul]
  have e₁ : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
      CommRingCat.ofHom θ.toRingHom = CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := RatFunc ℚ))) := by
    apply CommRingCat.hom_ext
    ext x
    simp [hθ]
  have e₂ : CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight
      (R := ℚ) (A := RatFunc ℚ) (B := RatFunc ℚ))) ≫ CommRingCat.ofHom θ.toRingHom =
      CommRingCat.ofHom (algebraMap (RatFunc ℚ) K) ≫
        CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := by
    apply CommRingCat.hom_ext
    ext x
    simp [hθ]
  have hfst : pullback.fst s (specAlgebraMap (RatFunc ℚ) K) =
      ιX.hom ≫ Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ arrowsIso.inv := by
    apply hR.hom_ext
    · rw [Category.assoc, Category.assoc, arrowsIso_inv_target, ← Spec.map_comp, e₁, hιR]
    · rw [Category.assoc, Category.assoc, hsrc, ← Spec.map_comp, e₂, Spec.map_comp,
        ← Category.assoc, hιL, pullback.condition]
  -- The automorphism, as a ring endomorphism of `K ⊗_ℚ ℚ(T)`.
  have hφL : φ.hom.left ≫ pullback.snd s (specAlgebraMap (RatFunc ℚ) K) =
      pullback.snd s (specAlgebraMap (RatFunc ℚ) K) := Over.w φ.hom
  obtain ⟨F, hF⟩ := Spec.map_surjective (ιX.inv ≫ φ.hom.left ≫ ιX.hom)
  obtain ⟨F', hF'⟩ := Spec.map_surjective (ιX.inv ≫ φ.inv.left ≫ ιX.hom)
  have hFF' : F ≫ F' = 𝟙 _ := by
    apply Spec.map_injective
    have hφ : φ.inv.left ≫ φ.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]
    rw [Spec.map_comp, Spec.map_id, hF, hF']
    simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hφ, Iso.inv_hom_id]
  have hFinj : Function.Injective F.hom := by
    have h' : ∀ z, F'.hom (F.hom z) = z := fun z => by
      simpa using congrArg (fun ψ => ψ.hom z) hFF'
    intro x y hxy
    rw [← h' x, hxy, h' y]
  have hFK : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ F =
      CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hF]
    simp only [Category.assoc, hιL, hφL]
    rw [← hιL, Iso.inv_hom_id_assoc]
  let fA : K ⊗[ℚ] RatFunc ℚ →ₐ[K] K ⊗[ℚ] RatFunc ℚ :=
    { toRingHom := F.hom
      commutes' := fun x => by
        have := congrArg (fun ψ => ψ.hom x) hFK
        simpa [Algebra.TensorProduct.algebraMap_apply] using this }
  -- The two points.
  have hc : Transcendental ℚ (algebraMap (RatFunc ℚ) K varT) := by
    rw [transcendental_iff_injective]
    have : aeval (algebraMap (RatFunc ℚ) K varT) = γ.comp (aeval varT) :=
      Polynomial.algHom_ext (by simp [γ])
    rw [this, AlgHom.coe_comp]
    exact (algebraMap (RatFunc ℚ) K).injective.comp
      (transcendental_iff_injective.mp transcendental_varT)
  have hp₁ : PrimeSpectrum.comap θ.toRingHom (ιX.hom r₁) =
      ⟨RingHom.ker diagHom.toRingHom, RingHom.ker_isPrime _⟩ := by
    rw [hfst, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h₁
    exact inv_apply_injective arrowsIso h₁
  have hp₂ : PrimeSpectrum.comap θ.toRingHom (PrimeSpectrum.comap F.hom (ιX.hom r₁)) =
      ⟨RingHom.ker graphHom.toRingHom, RingHom.ker_isPrime _⟩ := by
    rw [hfst, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h₂
    have hψp : ιX.hom (φ.hom.left r₁) = Spec.map F (ιX.hom r₁) := by
      rw [hF, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, inv_hom_apply]
    rw [hψp] at h₂
    exact inv_apply_injective arrowsIso h₂
  have m₁ : coordU K - algebraMap K _ (algebraMap (RatFunc ℚ) K varT) ∈
      (ιX.hom r₁).asIdeal := by
    have hmem : varT ⊗ₜ[ℚ] (1 : RatFunc ℚ) - 1 ⊗ₜ varT ∈ RingHom.ker diagHom.toRingHom := by
      simp [diagHom]
    have hker : (PrimeSpectrum.comap θ.toRingHom (ιX.hom r₁)).asIdeal =
        RingHom.ker diagHom.toRingHom := congrArg PrimeSpectrum.asIdeal hp₁
    rw [← hker] at hmem
    have hmem' : θ (varT ⊗ₜ[ℚ] (1 : RatFunc ℚ) - 1 ⊗ₜ varT) ∈ (ιX.hom r₁).asIdeal := hmem
    have e : θ (varT ⊗ₜ[ℚ] (1 : RatFunc ℚ) - 1 ⊗ₜ varT) =
        coordU K - algebraMap K _ (algebraMap (RatFunc ℚ) K varT) := by
      rw [map_sub, hθ, hθ, map_one, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
    rw [← e]
    exact hmem'
  have m₂ : algebraMap K _ (algebraMap (RatFunc ℚ) K varT) - fA (coordU K) ^ 2 ∈
      (ιX.hom r₁).asIdeal := by
    have hmem : (1 : RatFunc ℚ) ⊗ₜ[ℚ] varT - (varT ^ 2) ⊗ₜ 1 ∈ RingHom.ker graphHom.toRingHom := by
      simp [graphHom, sqAlgHom_varT]
    have hker : (PrimeSpectrum.comap θ.toRingHom
        (PrimeSpectrum.comap F.hom (ιX.hom r₁))).asIdeal =
        RingHom.ker graphHom.toRingHom := congrArg PrimeSpectrum.asIdeal hp₂
    rw [← hker] at hmem
    have hmem' : F.hom (θ ((1 : RatFunc ℚ) ⊗ₜ[ℚ] varT - (varT ^ 2) ⊗ₜ 1)) ∈
        (ιX.hom r₁).asIdeal := hmem
    have e' : θ ((1 : RatFunc ℚ) ⊗ₜ[ℚ] varT - (varT ^ 2) ⊗ₜ 1) =
        algebraMap K _ (algebraMap (RatFunc ℚ) K varT) - coordU K ^ 2 := by
      rw [map_sub, hθ, hθ, map_one, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_pow, one_pow]
    have e : F.hom (θ ((1 : RatFunc ℚ) ⊗ₜ[ℚ] varT - (varT ^ 2) ⊗ₜ 1)) =
        algebraMap K _ (algebraMap (RatFunc ℚ) K varT) - fA (coordU K) ^ 2 := by
      rw [e']
      change fA _ = _
      rw [map_sub, map_pow, AlgHom.commutes]
    rw [← e]
    exact hmem'
  exact false_of_mem hc fA hFinj (ιX.hom r₁).asIdeal (ιX.hom r₁).isPrime.ne_top m₁ m₂

end CoarseGroupoid

/-- The statement of Tag 04LP as printed, for groupoid schemes whose object scheme is the spectrum
of a field `k`: for any two points `r, r'` of the arrow scheme `R` there are a field extension
`k'/k`, points `r₁, r₂` of `R ×_{s, Spec k} Spec k'` and an automorphism `φ` of
`R ×_{s, Spec k} Spec k'` over `Spec k'` with `φ(r₁) = r₂`, `pr₀(r₁) = r` and `pr₀(r₂) = r'`. -/
def GroupoidOnFieldHomogeneousStatement : Prop :=
  ∀ (S : Scheme.{0}) (G : GroupoidScheme S) (k : Type) [Field k]
    (e : G.objects.left ≅ Spec (.of k)) (r r' : G.arrows.left),
    ∃ (k' : Type) (_ : Field k') (α : Algebra k k'),
      ∃ (r₁ r₂ : ↥(pullback (G.source.left ≫ e.hom)
          (Spec.map (CommRingCat.ofHom (@algebraMap k k' _ _ α)))))
        (φ : Over.mk (pullback.snd (G.source.left ≫ e.hom)
            (Spec.map (CommRingCat.ofHom (@algebraMap k k' _ _ α)))) ≅
          Over.mk (pullback.snd (G.source.left ≫ e.hom)
            (Spec.map (CommRingCat.ofHom (@algebraMap k k' _ _ α))))),
        φ.hom.left r₁ = r₂ ∧
          (pullback.fst (G.source.left ≫ e.hom)
            (Spec.map (CommRingCat.ofHom (@algebraMap k k' _ _ α)))) r₁ = r ∧
          (pullback.fst (G.source.left ≫ e.hom)
            (Spec.map (CommRingCat.ofHom (@algebraMap k k' _ _ α)))) r₂ = r'

/-- **Tag 04LP as printed is false**: it fails for the coarse groupoid of `Spec ℚ(T)` over
`Spec ℚ`, with `r` the point `t = s` and `r'` the point `s = t²` of its arrow scheme. -/
theorem not_groupoidOnFieldHomogeneousStatement : ¬ GroupoidOnFieldHomogeneousStatement := by
  intro H
  obtain ⟨K, _, α, r₁, r₂, φ, h₁₂, h₁, h₂⟩ := H _ CoarseGroupoid.groupoid (RatFunc ℚ)
    (Iso.refl _) CoarseGroupoid.diagPoint CoarseGroupoid.graphPoint
  subst h₁₂
  exact CoarseGroupoid.not_exists_iso_self_mapping K _ (Category.comp_id _) r₁ φ h₁ h₂

end Stacks.Groupoids

end
