module

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Ideal.NatInt
public import StacksFrontier.RingTheory.Spectrum.Prime.Polynomial

/-!
# Examples of spectra of rings
-/

/-!
# The spectrum of `ℤ[x]/(x² - 4)`

Let `R = ℤ[x]/(x² - 4)`, and write `x̄` for the image of `x` in `R`, so that
`R = ℤ[x̄]` with the single relation `x̄² = 4`. Let `φ : ℤ → R` be the structure
map.

The ideals of `R` singled out below are `(2, x̄)`, the pair `(q, x̄ - 2)` and
`(q, x̄ + 2)` for each odd prime `q`, and the two ideals `(x̄ - 2)`, `(x̄ + 2)`.

The main result classifies `Spec(R)`: an ideal of `R` is prime exactly when it is
one of those ideals. The proof splits on whether `p` contains `x̄ - 2` or `x̄ + 2`
(their product is `0`) and pulls `p` back from `ℤ` along the evaluation `x̄ ↦ 2` or
`x̄ ↦ -2`, which is surjective with kernel `(x̄ ∓ 2)`.

`R` is modelled as `AdjoinRoot (X ^ 2 - 4 : ℤ[X])`, which is definitionally
`ℤ[X] ⧸ (X ^ 2 - 4)`.
-/

@[expose] public section

open Polynomial

/-- `AdjoinRoot.lift i a h` is surjective when `i` is. -/
theorem AdjoinRoot.lift_surjective_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    {f : R[X]} {i : R →+* S} {a : S} (h : f.eval₂ i a = 0) (hi : Function.Surjective i) :
    Function.Surjective (AdjoinRoot.lift i a h) := by
  refine Function.Surjective.of_comp (g := AdjoinRoot.of f) ?_
  rw [← RingHom.coe_comp, AdjoinRoot.lift_comp_of]
  exact hi

/-- The kernel of evaluating `AdjoinRoot f` at a root `a ∈ R` of `f` is `(root f - a)`. -/
theorem AdjoinRoot.ker_lift_id {R : Type*} [CommRing R] {f : R[X]} {a : R}
    (h : f.eval₂ (RingHom.id R) a = 0) :
    RingHom.ker (AdjoinRoot.lift (RingHom.id R) a h) =
      Ideal.span {AdjoinRoot.root f - AdjoinRoot.of f a} := by
  have hc : (AdjoinRoot.lift (RingHom.id R) a h).comp (AdjoinRoot.mk f) = evalRingHom a := by
    ext <;> simp
  rw [← Ideal.map_comap_of_surjective _ AdjoinRoot.mk_surjective (RingHom.ker _),
    RingHom.comap_ker, hc, ker_evalRingHom, Ideal.map_span, Set.image_singleton, map_sub,
    AdjoinRoot.mk_X, AdjoinRoot.mk_C]

/-- The ring `R = ℤ[x]/(x² - 4)`, realised by adjoining a root of `X ^ 2 - 4`
to `ℤ`. -/
noncomputable abbrev IntXSqSubFour : Type := AdjoinRoot (X ^ 2 - 4 : ℤ[X])

namespace IntXSqSubFour

/-- The image `x̄` of `x` in `R`, that is, the adjoined root of `X ^ 2 - 4`. -/
noncomputable def xbar : IntXSqSubFour := AdjoinRoot.root (X ^ 2 - 4 : ℤ[X])

/-- The ideal `(2, x̄)` of `R`, the prime lying over `(2)`. -/
noncomputable abbrev p2 : Ideal IntXSqSubFour := Ideal.span {2, xbar}

/-- The ideal `(q, x̄ - 2)` of `R`, one of the two primes over an odd prime `q`. -/
noncomputable abbrev pMinus (q : ℕ) : Ideal IntXSqSubFour :=
  Ideal.span {(q : IntXSqSubFour), xbar - 2}

/-- The ideal `(q, x̄ + 2)` of `R`, one of the two primes over an odd prime `q`. -/
noncomputable abbrev pPlus (q : ℕ) : Ideal IntXSqSubFour :=
  Ideal.span {(q : IntXSqSubFour), xbar + 2}

/-- The generic prime `(x̄ - 2)` of `R`, lying over `(0)`. -/
noncomputable abbrev gMinus : Ideal IntXSqSubFour := Ideal.span {xbar - 2}

/-- The generic prime `(x̄ + 2)` of `R`, lying over `(0)`. -/
noncomputable abbrev gPlus : Ideal IntXSqSubFour := Ideal.span {xbar + 2}

/-! ## Auxiliary constructions and basic relations -/

/-- Evaluation `R → ℤ` sending `x̄` to `2`; it induces the isomorphism
`R ⧸ (x̄ - 2) ≅ ℤ`. -/
noncomputable def evalTwo : IntXSqSubFour →+* ℤ :=
  AdjoinRoot.lift (RingHom.id ℤ) 2 (by simp)

/-- Evaluation `R → ℤ` sending `x̄` to `-2`; it induces the isomorphism
`R ⧸ (x̄ + 2) ≅ ℤ`. -/
noncomputable def evalNegTwo : IntXSqSubFour →+* ℤ :=
  AdjoinRoot.lift (RingHom.id ℤ) (-2) (by simp)

/-- The evaluation `evalTwo` sends `x̄` to `2`. -/
@[simp] lemma evalTwo_root : evalTwo xbar = 2 := by
  simp [evalTwo, xbar, AdjoinRoot.lift_root]

/-- The evaluation `evalNegTwo` sends `x̄` to `-2`. -/
@[simp] lemma evalNegTwo_root : evalNegTwo xbar = -2 := by
  simp [evalNegTwo, xbar, AdjoinRoot.lift_root]

/-- If `y` lies in the span of `s` and a ring homomorphism `f` sends every element
of `s` into an ideal `J`, then `f y ∈ J`. -/
lemma map_mem_of_mem_span {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s : Set R)
    (J : Ideal S) (hs : ∀ g ∈ s, f g ∈ J) {y : R} (hy : y ∈ Ideal.span s) : f y ∈ J :=
  (Ideal.span_le (I := J.comap f)).mpr hs hy

/-- The defining relation `x̄ ^ 2 = 4` in `R`. -/
lemma xbar_sq : xbar ^ 2 = 4 := by
  have h : AdjoinRoot.mk (X ^ 2 - 4 : ℤ[X]) (X ^ 2 - 4) = 0 := AdjoinRoot.mk_self
  rwa [map_sub, map_pow, AdjoinRoot.mk_X, map_ofNat, sub_eq_zero, ← xbar] at h

/-- The factorization `(x̄ - 2) * (x̄ + 2) = 0` in `R`, coming from `x̄ ^ 2 = 4`. -/
lemma xbar_sub_two_mul_xbar_add_two : (xbar - 2) * (xbar + 2) = 0 := by
  linear_combination xbar_sq

section SurjectionOntoInt

variable {A : Type*} [CommRing A] {e : A →+* ℤ} (he : Function.Surjective e) {a : A}
  (hker : RingHom.ker e = Ideal.span {a})
include he hker

/-- If `e : A → ℤ` is surjective with kernel `(a)`, then `e⁻¹((n)) = (n, a)`. -/
lemma comap_span_natCast_eq_span_pair (n : ℕ) :
    (Ideal.span {(n : ℤ)}).comap e = Ideal.span {(n : A), a} := by
  rw [← map_natCast e n, ← Set.image_singleton, ← Ideal.map_span,
    Ideal.comap_map_of_surjective' _ he, hker, ← Ideal.span_insert]

/-- If `e : A → ℤ` is surjective with kernel `(a)`, then `(q, a)` is prime for prime `q`. -/
lemma isPrime_span_natCast_pair {q : ℕ} (hq : q.Prime) : (Ideal.span {(q : A), a}).IsPrime := by
  have : (Ideal.span {(q : ℤ)}).IsPrime := Ideal.isPrime_int_iff.mpr (.inr ⟨q, hq, rfl⟩)
  rw [← comap_span_natCast_eq_span_pair he hker]
  infer_instance

/-- If `e : A → ℤ` is surjective with kernel `(a)`, a prime of `A` containing `a` is `(a)` or
`(q, a)` for a prime number `q`. -/
lemma eq_span_or_eq_span_natCast_pair_of_mem {p : Ideal A} [p.IsPrime] (ha : a ∈ p) :
    p = Ideal.span {a} ∨ ∃ q : ℕ, q.Prime ∧ p = Ideal.span {(q : A), a} := by
  have hle : RingHom.ker e ≤ p := by rwa [hker, Ideal.span_singleton_le_iff_mem]
  have hp : p = (p.map e).comap e := by
    rw [Ideal.comap_map_of_surjective' _ he, sup_eq_left.mpr hle]
  rcases Ideal.isPrime_int_iff.mp (Ideal.map_isPrime_of_surjective he hle) with h | ⟨q, hq, h⟩
  · left
    rw [hp, h, ← RingHom.ker_eq_comap_bot, hker]
  · right
    exact ⟨q, hq, by rw [hp, h, comap_span_natCast_eq_span_pair he hker]⟩

end SurjectionOntoInt

/-! ## The spectrum of `R` -/

/-- `evalTwo` is surjective. -/
lemma evalTwo_surjective : Function.Surjective evalTwo := by
  rw [evalTwo]
  exact AdjoinRoot.lift_surjective_of_surjective _ Function.surjective_id

/-- `evalNegTwo` is surjective. -/
lemma evalNegTwo_surjective : Function.Surjective evalNegTwo := by
  rw [evalNegTwo]
  exact AdjoinRoot.lift_surjective_of_surjective _ Function.surjective_id

/-- The kernel of `evalTwo` (`x̄ ↦ 2`) is `gMinus = (x̄ - 2)`. -/
lemma ker_evalTwo : RingHom.ker evalTwo = gMinus := by
  rw [evalTwo, AdjoinRoot.ker_lift_id, gMinus, xbar, map_ofNat]

/-- The kernel of `evalNegTwo` (`x̄ ↦ -2`) is `gPlus = (x̄ + 2)`. -/
lemma ker_evalNegTwo : RingHom.ker evalNegTwo = gPlus := by
  rw [evalNegTwo, AdjoinRoot.ker_lift_id, gPlus, xbar, map_neg, map_ofNat, sub_neg_eq_add]

/-- **Classification of `Spec(R)` (Stacks Tag 00EY).**
An ideal `p` of `R = ℤ[x]/(x² - 4)` is prime if and only if it is one of the
listed ideals: `(2, x̄)`, or `(q, x̄ - 2)`/`(q, x̄ + 2)` for some odd prime `q`,
or one of the two generic primes `(x̄ - 2)`, `(x̄ + 2)`.

A prime contains `x̄ - 2` or `x̄ + 2`, since their product is `0`. The evaluations
`R → ℤ`, `x̄ ↦ ±2`, are surjective with kernels `(x̄ ∓ 2)`, so the primes containing
`x̄ ∓ 2` are the preimages of the primes `(0)` and `(q)` of `ℤ`; for `q = 2` both
preimages are `(2, x̄)`. -/
@[stacks 00EY]
theorem isPrime_iff (p : Ideal IntXSqSubFour) :
    p.IsPrime ↔
      (p = p2 ∨
       (∃ q : ℕ, q.Prime ∧ Odd q ∧ (p = pMinus q ∨ p = pPlus q)) ∨
       p = gMinus ∨ p = gPlus) := by
  have hkerP : RingHom.ker evalTwo = Ideal.span {xbar - 2} := by rw [ker_evalTwo, gMinus]
  have hkerM : RingHom.ker evalNegTwo = Ideal.span {xbar + 2} := by rw [ker_evalNegTwo, gPlus]
  have h2P : Ideal.span {((2 : ℕ) : IntXSqSubFour), xbar - 2} = Ideal.span {2, xbar} := by
    rw [Nat.cast_ofNat, show xbar - 2 = xbar + -1 * (2 : IntXSqSubFour) by ring,
      Ideal.span_pair_add_mul_left]
  have h2M : Ideal.span {((2 : ℕ) : IntXSqSubFour), xbar + 2} = Ideal.span {2, xbar} := by
    rw [Nat.cast_ofNat, show xbar + 2 = xbar + 1 * (2 : IntXSqSubFour) by ring,
      Ideal.span_pair_add_mul_left]
  simp only [p2, pMinus, pPlus, gMinus, gPlus]
  refine ⟨fun hp => ?_, ?_⟩
  · have h0 : (xbar - 2) * (xbar + 2) ∈ p := xbar_sub_two_mul_xbar_add_two ▸ p.zero_mem
    rcases hp.mem_or_mem h0 with h | h
    · rcases eq_span_or_eq_span_natCast_pair_of_mem evalTwo_surjective hkerP h with
        rfl | ⟨q, hq, rfl⟩
      · exact .inr (.inr (.inl rfl))
      rcases hq.eq_two_or_odd' with rfl | hodd
      · exact .inl h2P
      · exact .inr (.inl ⟨q, hq, hodd, .inl rfl⟩)
    · rcases eq_span_or_eq_span_natCast_pair_of_mem evalNegTwo_surjective hkerM h with
        rfl | ⟨q, hq, rfl⟩
      · exact .inr (.inr (.inr rfl))
      rcases hq.eq_two_or_odd' with rfl | hodd
      · exact .inl h2M
      · exact .inr (.inl ⟨q, hq, hodd, .inr rfl⟩)
  · rintro (rfl | ⟨q, hq, -, rfl | rfl⟩ | rfl | rfl)
    · exact h2P ▸ isPrime_span_natCast_pair evalTwo_surjective hkerP Nat.prime_two
    · exact isPrime_span_natCast_pair evalTwo_surjective hkerP hq
    · exact isPrime_span_natCast_pair evalNegTwo_surjective hkerM hq
    · exact hkerP ▸ RingHom.ker_isPrime evalTwo
    · exact hkerM ▸ RingHom.ker_isPrime evalNegTwo

/-! ## Distinctness of the listed primes -/

/-- An odd prime `q` does not divide `4` in `ℤ`. -/
lemma not_natCast_dvd_four_of_odd {q : ℕ} (hq : q.Prime) (hodd : Odd q) : ¬ (q : ℤ) ∣ 4 := by
  intro hdvd
  have hne : q ≠ 2 := by
    rintro rfl
    exact (by decide : ¬ Odd 2) hodd
  have hd : q ∣ 4 := by exact_mod_cast hdvd
  have hle : q ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  interval_cases q <;> simp_all (config := { decide := true })

/-- The evaluation `evalTwo` maps `pMinus q = (q, x̄ - 2)` into `(q)`. -/
lemma evalTwo_mem_span_of_mem_pMinus {q : ℕ} {y : IntXSqSubFour} (hy : y ∈ pMinus q) :
    evalTwo y ∈ Ideal.span {(q : ℤ)} :=
  map_mem_of_mem_span evalTwo _ _ (by rintro _ (rfl | rfl) <;> simp [map_ofNat]) hy

/-- The evaluation `evalNegTwo` maps `pPlus q = (q, x̄ + 2)` into `(q)`. -/
lemma evalNegTwo_mem_span_of_mem_pPlus {q : ℕ} {y : IntXSqSubFour} (hy : y ∈ pPlus q) :
    evalNegTwo y ∈ Ideal.span {(q : ℤ)} :=
  map_mem_of_mem_span evalNegTwo _ _ (by rintro _ (rfl | rfl) <;> simp [map_ofNat]) hy

/-- For an odd prime `q`, the two primes `pMinus q` and `pPlus q` over `(q)` are distinct. -/
lemma pMinus_ne_pPlus {q : ℕ} (hq : q.Prime) (hodd : Odd q) : pMinus q ≠ pPlus q := by
  intro heq
  have hmem : xbar + 2 ∈ pMinus q := by
    rw [heq]
    exact Ideal.subset_span (by simp)
  have := evalTwo_mem_span_of_mem_pMinus hmem
  rw [map_add, evalTwo_root, map_ofNat, Ideal.mem_span_singleton] at this
  exact not_natCast_dvd_four_of_odd hq hodd (by simpa using this)

/-- The two generic primes `gMinus` and `gPlus` are distinct. -/
lemma gMinus_ne_gPlus : gMinus ≠ gPlus := by
  intro heq
  have hmem : xbar + 2 ∈ gMinus := by
    rw [heq]
    exact Ideal.subset_span rfl
  rw [← ker_evalTwo, RingHom.mem_ker] at hmem
  norm_num [map_ofNat] at hmem

/-- For an odd prime `q`, the prime `p2` over `(2)` differs from `pMinus q`. -/
lemma p2_ne_pMinus {q : ℕ} (hq : q.Prime) (hodd : Odd q) : p2 ≠ pMinus q := by
  intro heq
  have hmem : (2 : IntXSqSubFour) ∈ pMinus q := by
    rw [← heq]
    exact Ideal.subset_span (by simp)
  have := evalTwo_mem_span_of_mem_pMinus hmem
  rw [map_ofNat, Ideal.mem_span_singleton] at this
  exact not_natCast_dvd_four_of_odd hq hodd (this.trans (by norm_num))

/-- For an odd prime `q`, the prime `p2` over `(2)` differs from `pPlus q`. -/
lemma p2_ne_pPlus {q : ℕ} (hq : q.Prime) (hodd : Odd q) : p2 ≠ pPlus q := by
  intro heq
  have hmem : (2 : IntXSqSubFour) ∈ pPlus q := by
    rw [← heq]
    exact Ideal.subset_span (by simp)
  have := evalNegTwo_mem_span_of_mem_pPlus hmem
  rw [map_ofNat, Ideal.mem_span_singleton] at this
  exact not_natCast_dvd_four_of_odd hq hodd (this.trans (by norm_num))

/-- Some of the ideals listed in `isPrime_iff` are distinct: for an odd prime `q`,
`pMinus q ≠ pPlus q`, `p2 ≠ pMinus q` and `p2 ≠ pPlus q`; and `gMinus ≠ gPlus`. -/
theorem listed_primes_distinct :
    (∀ q : ℕ, q.Prime → Odd q → pMinus q ≠ pPlus q) ∧
    (gMinus ≠ gPlus) ∧
    (∀ q : ℕ, q.Prime → Odd q → p2 ≠ pMinus q ∧ p2 ≠ pPlus q) :=
  ⟨fun _ hq hodd => pMinus_ne_pPlus hq hodd, gMinus_ne_gPlus,
    fun _ hq hodd => ⟨p2_ne_pMinus hq hodd, p2_ne_pPlus hq hodd⟩⟩

end IntXSqSubFour

end

@[expose] public section

open Polynomial

/-- **Stacks Tag 00EZ** (Description of `Spec(ℤ[x])`).

Every prime ideal `𝔭` of `ℤ[x]` has one of the following forms:
* `𝔭 = (0)`;
* `𝔭 = (f)` with `f` irreducible in `ℤ[x]`; this covers the nonzero primes with
  `𝔭 ∩ ℤ = (0)` and the primes `(q)` (take `f = q`) for a prime number `q`;
* `𝔭 = (q, f)` for a prime number `q` and `f` irreducible in `ℤ[x]` whose reduction modulo `q`
  is irreducible in `(ℤ/qℤ)[x]`.

The Stacks text omits the primes `(q)`, which lie over `(q)` without being of the third form. -/
@[stacks 00EZ]
theorem Polynomial.isPrime_int_trichotomy
    (𝔭 : Ideal ℤ[X]) (h𝔭 : 𝔭.IsPrime) :
    𝔭 = ⊥ ∨
    (∃ f : ℤ[X], Irreducible f ∧ 𝔭 = Ideal.span {f}) ∨
    (∃ (q : ℕ) (f : ℤ[X]), q.Prime ∧
        Irreducible f ∧
        Irreducible (f.map (Int.castRingHom (ZMod q))) ∧
        𝔭 = Ideal.span {(C (q : ℤ)), f}) := by
  by_cases h : 𝔭.comap C = ⊥
  · exact (eq_bot_or_eq_span_irreducible_of_comap_C_eq_bot 𝔭 h).imp_right Or.inl
  obtain ⟨π, hπ, hPπ⟩ := exists_prime_comap_C_eq_span 𝔭 h
  obtain ⟨q, hq, hπq⟩ : ∃ q : ℕ, q.Prime ∧ Ideal.span {(q : ℤ)} = Ideal.span {π} :=
    ⟨π.natAbs, Int.prime_iff_natAbs_prime.1 hπ, Int.span_natAbs π⟩
  have := Fact.mk hq
  have hCq : C (q : ℤ) ∈ 𝔭 := by
    rw [← Ideal.mem_comap, hPπ, ← hπq]
    exact Ideal.mem_span_singleton_self _
  rcases eq_span_C_or_eq_span_C_monic (Int.castRingHom (ZMod q)) ZMod.intCast_surjective
    (ZMod.ker_intCastRingHom q) 𝔭 hCq with hP | ⟨f, hfm, hf, hP⟩
  · exact Or.inr (Or.inl ⟨_, (prime_C_iff.2 (Nat.prime_iff_prime_int.1 hq)).irreducible, hP⟩)
  exact Or.inr (Or.inr ⟨q, f, hq, hfm.irreducible_of_irreducible_map _ _ hf, hf, hP⟩)

end

@[expose] public section

open Polynomial

namespace NodalCubicAffineOpen

noncomputable section

/-! ## Constructions used in the example

We set up the ring `R = {f ∈ ℚ[z] : f(0) = f(1)}`, the candidate generators
`A(z) = z² - z`, `B(z) = z³ - z²`, and the localized variant
`R_a = {f ∈ ℚ[z, 1/(z-a)] : f(0) = f(1)}` for `a ∈ ℚ ∖ {0, ½, 1}`. -/

/-- The ring `L a = ℚ[z, 1/(z-a)]`, modelled as the localization of `ℚ[z]`
at the element `X - C a`. -/
abbrev L (a : ℚ) : Type := Localization.Away (X - C a : Polynomial ℚ)

/-- Evaluation `f ↦ f(r)` extends from `ℚ[z]` to `L a = ℚ[z, 1/(z-a)]`
whenever `r ≠ a`. -/
def evalLift (a r : ℚ) (h : r ≠ a) : L a →+* ℚ :=
  IsLocalization.Away.lift (R := Polynomial ℚ) (S := L a)
    (g := (Polynomial.aeval r).toRingHom) (X - C a) (by
      simpa [isUnit_iff_ne_zero, sub_eq_zero] using h)

/-- `evalLift` agrees with `Polynomial.eval r` on the image of `ℚ[z]`. -/
lemma evalLift_algebraMap (a r : ℚ) (h : r ≠ a) (p : Polynomial ℚ) :
    evalLift a r h (algebraMap (Polynomial ℚ) (L a) p) = p.eval r := by
  unfold evalLift
  rw [IsLocalization.Away.lift_eq]
  simp

/-- The `ℚ`-subalgebra `R = {f ∈ ℚ[z] : f(0) = f(1)}` of `ℚ[z]`. -/
def R : Subalgebra ℚ (Polynomial ℚ) where
  carrier := {f : Polynomial ℚ | f.eval 0 = f.eval 1}
  mul_mem' := by
    intros a b ha hb
    simp only [Set.mem_ofPred_eq, eval_mul] at ha hb ⊢
    rw [ha, hb]
  add_mem' := by
    intros a b ha hb
    simp only [Set.mem_ofPred_eq, eval_add] at ha hb ⊢
    rw [ha, hb]
  algebraMap_mem' := by intro r; simp [Set.mem_ofPred_eq, algebraMap_eq, eval_C]

/-- A polynomial `f` lies in `R` if and only if `f(0) = f(1)`. -/
lemma mem_R {f : Polynomial ℚ} : f ∈ R ↔ f.eval 0 = f.eval 1 := Iff.rfl

/-- The `ℚ`-algebra homomorphism `φ : ℚ[A, B] → R` defined by
`φ(A) = z² - z` and `φ(B) = z³ - z²`. -/
def φ : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] R :=
  MvPolynomial.aeval (R := ℚ) (S₁ := R)
    (fun i : Fin 2 =>
      if i = 0 then
        ⟨X^2 - X, by simp [mem_R]⟩
      else
        ⟨X^3 - X^2, by simp [mem_R]⟩)

/-- The `ℚ`-subalgebra `R_a = {f ∈ L a : f(0) = f(1)}` of `L a`. -/
def Ra (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) : Subalgebra ℚ (L a) where
  carrier := {f : L a | evalLift a 0 ha0.symm f =
                        evalLift a 1 ha1.symm f}
  mul_mem' := by
    intros f g hf hg
    simp only [Set.mem_ofPred_eq, map_mul] at hf hg ⊢
    rw [hf, hg]
  add_mem' := by
    intros f g hf hg
    simp only [Set.mem_ofPred_eq, map_add] at hf hg ⊢
    rw [hf, hg]
  algebraMap_mem' := by
    intro q
    rw [Set.mem_ofPred_eq, IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (L a),
      evalLift_algebraMap, evalLift_algebraMap]
    simp

/-- An element `f` of `L a` lies in `R_a` if and only if `f(0) = f(1)`. -/
lemma mem_Ra {a : ℚ} {ha0 : a ≠ 0} {ha1 : a ≠ 1} {f : L a} :
    f ∈ Ra a ha0 ha1 ↔ evalLift a 0 ha0.symm f =
      evalLift a 1 ha1.symm f := Iff.rfl

/-- A polynomial whose image in `L a` lies in `R_a` lies in `R`. -/
lemma mem_R_of_algebraMap_mem_Ra {a : ℚ} {ha0 : a ≠ 0} {ha1 : a ≠ 1} {g : Polynomial ℚ}
    (hg : algebraMap (Polynomial ℚ) (L a) g ∈ Ra a ha0 ha1) : g ∈ R := by
  rw [mem_R]
  rwa [mem_Ra, evalLift_algebraMap, evalLift_algebraMap] at hg

/-- The inclusion `R → R_a` as a `ℚ`-algebra map, induced by the localization
`ℚ[z] → ℚ[z, 1/(z-a)]`. -/
def inclRToRa (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    R →ₐ[ℚ] Ra a ha0 ha1 :=
  ((IsScalarTower.toAlgHom ℚ (Polynomial ℚ) (L a)).comp R.val).codRestrict (Ra a ha0 ha1)
    fun f => by
      rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', mem_Ra, evalLift_algebraMap,
        evalLift_algebraMap, Subalgebra.coe_val]
      exact mem_R.mp f.property

/-- The image of `f ∈ R` under `inclRToRa` is the image of `f` in `L a`. -/
lemma coe_inclRToRa (a : ℚ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (f : R) :
    (inclRToRa a ha0 ha1 f : L a) = algebraMap (Polynomial ℚ) (L a) f := rfl

/-- Evaluation `ev_r : R → ℚ`, the restriction of `Polynomial.eval r` to `R`. -/
def evR (r : ℚ) : R →+* ℚ :=
  (Polynomial.evalRingHom r).comp R.val.toRingHom

/-- The ideal `𝔪_r = Ker(ev_r) ⊆ R`. -/
def mR (r : ℚ) : Ideal R := RingHom.ker (evR r)

/-- For any `r ∈ ℚ`, the ideal `𝔪_r = Ker(ev_r) ⊆ R` is prime. -/
instance mR_isPrime (r : ℚ) : (mR r).IsPrime := by
  unfold mR
  exact RingHom.ker_isPrime (evR r)

/-- The prime ideal `𝔪_r` packaged as a point of `Spec R`. -/
def mRPoint (r : ℚ) : PrimeSpectrum R := ⟨mR r, inferInstance⟩

/-- The prime ideal of the point `mRPoint r` is `𝔪_r`. -/
@[simp] lemma mRPoint_asIdeal (r : ℚ) : (mRPoint r).asIdeal = mR r := rfl

/-- An element `f ∈ R` lies in `𝔪_r` if and only if `f(r) = 0`. -/
lemma mem_mR {r : ℚ} {f : R} : f ∈ mR r ↔ (f : Polynomial ℚ).eval r = 0 := by
  simp [mR, evR]

/-- For any `r ∈ ℚ`, the ideal `𝔪_r ⊆ R` is maximal. -/
lemma mR_isMaximal (r : ℚ) : (mR r).IsMaximal := by
  unfold mR
  exact RingHom.ker_isMaximal_of_surjective (evR r) fun c => ⟨algebraMap ℚ R c, by simp [evR]⟩

/-! ## The presentation of `R` -/

/-- Every polynomial can be written as `P(z² - z) + z · Q(z² - z)`. -/
lemma exists_comp_add_X_mul_comp {S : Type*} [CommRing S] (g : S[X]) :
    ∃ P Q : S[X], g = P.comp (X ^ 2 - X) + X * Q.comp (X ^ 2 - X) := by
  induction g using Polynomial.induction_on with
  | C c => exact ⟨C c, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨P, Q, rfl⟩ := hp
    obtain ⟨P', Q', rfl⟩ := hq
    exact ⟨P + P', Q + Q', by simp only [add_comp]; ring⟩
  | monomial n c h =>
    obtain ⟨P, Q, h⟩ := h
    refine ⟨X * Q, P + Q, ?_⟩
    rw [pow_succ, ← mul_assoc, h]
    simp only [mul_comp, add_comp, X_comp]
    ring

/-- The polynomial `X² - X` is monic over any commutative ring. -/
lemma monic_X_sq_sub_X {S : Type*} [CommRing S] : (X ^ 2 - X : S[X]).Monic :=
  monic_X_pow_sub (degree_X_le.trans_lt (by norm_num))

/-- The degree of `X² - X` is two over a nontrivial commutative ring. -/
lemma natDegree_X_sq_sub_X {S : Type*} [CommRing S] [Nontrivial S] :
    (X ^ 2 - X : S[X]).natDegree = 2 := by
  compute_degree!

/-- Composing with `X² - X` doubles the degree. -/
lemma natDegree_comp_X_sq_sub_X {S : Type*} [CommRing S] [Nontrivial S] (P : S[X]) :
    (P.comp (X ^ 2 - X)).natDegree = P.natDegree * 2 := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  rw [natDegree_comp_eq_of_mul_ne_zero (by simpa [monic_X_sq_sub_X.leadingCoeff] using hP),
    natDegree_X_sq_sub_X]

/-- Composing with `X² - X` sends only the zero polynomial to zero. -/
lemma eq_zero_of_comp_X_sq_sub_X_eq_zero {S : Type*} [CommRing S] {P : S[X]}
    (h : P.comp (X ^ 2 - X) = 0) : P = 0 := by
  nontriviality S
  have := coeff_comp_degree_mul_degree (p := P)
    ((natDegree_X_sq_sub_X (S := S)).trans_ne two_ne_zero)
  rw [h, coeff_zero, monic_X_sq_sub_X.leadingCoeff, one_pow, mul_one] at this
  exact leadingCoeff_eq_zero.mp this.symm

/-- The decomposition `P(z² - z) + z · Q(z² - z)` is unique: comparing the parity of the
degrees of the two summands. -/
lemma eq_zero_of_comp_add_X_mul_comp {S : Type*} [CommRing S] {P Q : S[X]}
    (h : P.comp (X ^ 2 - X) + X * Q.comp (X ^ 2 - X) = 0) : P = 0 ∧ Q = 0 := by
  nontriviality S
  by_cases hQ : Q = 0
  · subst hQ
    exact ⟨eq_zero_of_comp_X_sq_sub_X_eq_zero (by simpa using h), rfl⟩
  exfalso
  have hQ' : Q.comp (X ^ 2 - X) ≠ 0 := fun h' => hQ (eq_zero_of_comp_X_sq_sub_X_eq_zero h')
  have h1 := congrArg natDegree (eq_neg_of_add_eq_zero_right h)
  rw [natDegree_X_mul hQ', natDegree_neg, natDegree_comp_X_sq_sub_X,
    natDegree_comp_X_sq_sub_X] at h1
  omega

/-- The map `φ` sends `A` to `z² - z`. -/
lemma coe_φ_X_zero : (φ (MvPolynomial.X 0) : Polynomial ℚ) = X ^ 2 - X := by
  simp [φ]

/-- The map `φ` sends `B` to `z³ - z²`. -/
lemma coe_φ_X_one : (φ (MvPolynomial.X 1) : Polynomial ℚ) = X ^ 3 - X ^ 2 := by
  simp [φ]

/-- The map `φ` sends a polynomial `P(A)` in `A` alone to `P(z² - z)`. -/
lemma coe_φ_aeval (P : Polynomial ℚ) :
    (φ (aeval (MvPolynomial.X 0) P) : Polynomial ℚ) = P.comp (X ^ 2 - X) := by
  rw [← Subalgebra.coe_val, ← AlgHom.comp_apply, ← aeval_algHom_apply, AlgHom.comp_apply,
    Subalgebra.coe_val, coe_φ_X_zero, comp_eq_aeval]

/-- The map `φ : ℚ[A, B] → R` is surjective. -/
theorem φ_surjective : Function.Surjective φ := by
  intro f
  obtain ⟨P, Q, hPQ⟩ := exists_comp_add_X_mul_comp (f : Polynomial ℚ)
  have hQ : Q.coeff 0 = 0 := by
    have hf := mem_R.mp f.property
    rw [hPQ] at hf
    simpa [eval_comp, coeff_zero_eq_eval_zero] using hf
  refine ⟨aeval (MvPolynomial.X 0) P + MvPolynomial.X 1 * aeval (MvPolynomial.X 0) Q.divX,
    Subtype.ext ?_⟩
  rw [hPQ]
  conv_rhs => rw [← divX_mul_X_add Q, hQ]
  simp only [map_add, map_mul, Subalgebra.coe_add, Subalgebra.coe_mul, coe_φ_aeval, coe_φ_X_one,
    map_zero, add_zero, mul_comp, X_comp]
  ring

/-- The relation `A³ - B² + A·B`. -/
abbrev relF : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2 + MvPolynomial.X 0 * MvPolynomial.X 1

/-- Modulo `A³ - B² + A·B`, every polynomial is congruent to `P(A) + B · Q(A)`. -/
lemma exists_mk_eq (p : MvPolynomial (Fin 2) ℚ) :
    ∃ P Q : Polynomial ℚ, Ideal.Quotient.mkₐ ℚ (Ideal.span {relF}) p =
      Ideal.Quotient.mkₐ ℚ (Ideal.span {relF})
        (aeval (MvPolynomial.X 0) P + MvPolynomial.X 1 * aeval (MvPolynomial.X 0) Q) := by
  set π := Ideal.Quotient.mkₐ ℚ (Ideal.span {relF})
  have hF : π (MvPolynomial.X 0) ^ 3 - π (MvPolynomial.X 1) ^ 2 +
      π (MvPolynomial.X 0) * π (MvPolynomial.X 1) = 0 := by
    have : π relF = 0 := by
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    simpa [relF] using this
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, by simp [← MvPolynomial.algebraMap_eq]⟩
  | add p q hp hq =>
    obtain ⟨P, Q, hp⟩ := hp
    obtain ⟨P', Q', hq⟩ := hq
    refine ⟨P + P', Q + Q', ?_⟩
    simp only [map_add, map_mul, ← aeval_algHom_apply] at hp hq ⊢
    rw [hp, hq]
    ring
  | mul_X p i hp =>
    obtain ⟨P, Q, hp⟩ := hp
    fin_cases i
    · refine ⟨P * X, Q * X, ?_⟩
      simp only [map_add, map_mul, ← aeval_algHom_apply] at hp ⊢
      rw [hp]
      simp only [Fin.zero_eta, aeval_X]
      ring
    · refine ⟨X ^ 3 * Q, P + X * Q, ?_⟩
      simp only [map_add, map_mul, ← aeval_algHom_apply] at hp ⊢
      rw [hp]
      simp only [Fin.mk_one, map_pow, aeval_X]
      linear_combination (-(aeval (π (MvPolynomial.X 0))) Q) * hF

/-- The relation `A³ - B² + A·B` lies in the kernel of `φ`. -/
lemma relF_mem_ker : relF ∈ RingHom.ker φ := by
  rw [RingHom.mem_ker, ← Subtype.coe_inj]
  simp only [map_add, map_sub, map_mul, map_pow,
    Subalgebra.coe_add, Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_pow, coe_φ_X_zero,
    coe_φ_X_one, ZeroMemClass.coe_zero]
  ring

/-- The kernel of `φ : ℚ[A, B] → R` is the principal ideal generated by
`A³ - B² + A·B`. -/
theorem ker_φ :
    RingHom.ker φ =
      Ideal.span ({(MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)^3 -
                   MvPolynomial.X 1 ^ 2 +
                   MvPolynomial.X 0 * MvPolynomial.X 1} :
                   Set (MvPolynomial (Fin 2) ℚ)) := by
  refine le_antisymm (fun p hp => ?_)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr relF_mem_ker))
  obtain ⟨P, Q, h⟩ := exists_mk_eq p
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at h
  have hsub := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr relF_mem_ker) h
  have hr := (RingHom.ker φ).sub_mem hp hsub
  rw [sub_sub_cancel, RingHom.mem_ker, ← Subtype.coe_inj] at hr
  simp only [map_add, map_mul, Subalgebra.coe_add,
    Subalgebra.coe_mul, coe_φ_aeval, coe_φ_X_one, ZeroMemClass.coe_zero] at hr
  obtain ⟨rfl, hQ⟩ := eq_zero_of_comp_add_X_mul_comp (P := P) (Q := X * Q)
    (by rw [← hr, mul_comp, X_comp]; ring)
  obtain rfl : Q = 0 := by simpa using hQ
  simpa using h

/-- The isomorphism `ℚ[A, B] / (A³ - B² + A·B) ≃ₐ[ℚ] R` induced by `φ`. -/
@[stacks 00F1 "`R ≅ ℚ[A, B]/(A³ - B² + AB)`"]
def quotientSpanAlgEquiv :
    (MvPolynomial (Fin 2) ℚ ⧸ Ideal.span {((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ 3 -
      MvPolynomial.X 1 ^ 2 + MvPolynomial.X 0 * MvPolynomial.X 1)}) ≃ₐ[ℚ] R :=
  (Ideal.quotientEquivAlgOfEq ℚ ker_φ.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective φ_surjective)

/-- The isomorphism `quotientSpanAlgEquiv` sends the class of `p` to `φ p`. -/
@[simp]
theorem quotientSpanAlgEquiv_mk (p : MvPolynomial (Fin 2) ℚ) :
    quotientSpanAlgEquiv (Ideal.Quotient.mk _ p) = φ p := by
  simp [quotientSpanAlgEquiv]

/-! ## The spectrum of `R_a` -/

/-- `z` is integral over `R`: it is a root of `T² - T - (z² - z)`. -/
lemma isIntegral_X : IsIntegral R (X : Polynomial ℚ) := by
  refine ⟨X ^ 2 - X - C ⟨X ^ 2 - X, by simp [mem_R]⟩, ?_, ?_⟩
  · monicity!
  · simp

/-- The polynomial ring `ℚ[z]` is integral over `R`. -/
instance : Algebra.IsIntegral R (Polynomial ℚ) := ⟨fun p => by
  induction p using Polynomial.induction_on with
  | C c =>
    simpa using isIntegral_algebraMap (R := R) (A := Polynomial ℚ) (x := ⟨C c, by simp [mem_R]⟩)
  | add p q hp hq => exact hp.add hq
  | monomial n c h =>
    rw [pow_succ, ← mul_assoc]
    exact h.mul isIntegral_X⟩

/-- The polynomial `(z - a)(z - (1 - a))` lies in `𝔪_a ⊆ R`. -/
private lemma mk_X_sub_C_mul_mem_mR (a : ℚ) :
    (⟨(X - C a) * (X - C (1 - a)), by simp [mem_R, mul_comm, ← mul_neg]⟩ : R) ∈ mR a := by
  simp [mem_mR]

section Spec

variable {a : ℚ} {ha0 : a ≠ 0} {ha1 : a ≠ 1}

/-- An element `f ∈ R` lies in the pullback of a prime `Q` of `R_a` along `inclRToRa` if and
only if its image in `R_a` lies in `Q`. -/
lemma mem_comap_inclRToRa {Q : PrimeSpectrum (Ra a ha0 ha1)} {f : R} :
    f ∈ (PrimeSpectrum.comap (inclRToRa a ha0 ha1).toRingHom Q).asIdeal ↔
      inclRToRa a ha0 ha1 f ∈ Q.asIdeal := by
  simp

/-- An element of `𝔪_a` is divisible by `z - a`. -/
lemma X_sub_C_dvd_of_mem_mR {s : R} (hs : s ∈ mR a) : X - C a ∣ (s : Polynomial ℚ) :=
  dvd_iff_isRoot.mpr (IsRoot.def.mpr (mem_mR.mp hs))

/-- If `s ∈ 𝔪_a`, every element of `R_a` becomes an element of `R` after multiplication by a
power of `s`. -/
lemma exists_pow_mul_eq {s : R} (hs : s ∈ mR a) (y : Ra a ha0 ha1) :
    ∃ (k : ℕ) (x : R), inclRToRa a ha0 ha1 s ^ k * y = inclRToRa a ha0 ha1 x := by
  obtain ⟨t, ht⟩ := X_sub_C_dvd_of_mem_mR hs
  obtain ⟨n, g, hg⟩ := IsLocalization.Away.surj (X - C a) (y : L a)
  have h : algebraMap (Polynomial ℚ) (L a) (t ^ n * g) =
      ((inclRToRa a ha0 ha1 s ^ n * y : Ra a ha0 ha1) : L a) := by
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_inclRToRa, ht, map_mul, map_mul, map_pow,
      ← hg, mul_pow]
    ring
  have hmem : t ^ n * g ∈ R :=
    mem_R_of_algebraMap_mem_Ra (h ▸ (inclRToRa a ha0 ha1 s ^ n * y).property)
  exact ⟨n, ⟨_, hmem⟩, Subtype.ext (by rw [coe_inclRToRa, h])⟩

/-- `𝔪_a` is not in the image of `Spec R_a → Spec R`: `(z² - z)² (a² - a)` lies in
`𝔪_a R_a`. -/
lemma comap_ne_mRPoint (Q : PrimeSpectrum (Ra a ha0 ha1)) :
    PrimeSpectrum.comap (inclRToRa a ha0 ha1).toRingHom Q ≠ mRPoint a := by
  intro hQ
  set A : Polynomial ℚ := X ^ 2 - X
  have hA : ∀ r : ℚ, r = 0 ∨ r = 1 → A.eval r = 0 := by rintro r (rfl | rfl) <;> simp [A]
  let ι := algebraMap (Polynomial ℚ) (L a)
  let E : L a := ι A * (ι (C (a ^ 2 - a)) *
    IsLocalization.Away.invSelf (S := L a) (X - C a : Polynomial ℚ) + ι X)
  have hE : E ∈ Ra a ha0 ha1 := by
    simp [mem_Ra, E, ι, evalLift_algebraMap, hA]
  let y : R := ⟨A * (X - C a), by simp [mem_R, hA]⟩
  let z : R := ⟨C (a ^ 2 - a) * A ^ 2 + A ^ 2 * (X - C a) * X, by simp [mem_R, hA]⟩
  have hyz : inclRToRa a ha0 ha1 y * ⟨E, hE⟩ = inclRToRa a ha0 ha1 z := by
    refine Subtype.ext ?_
    simp only [Subalgebra.coe_mul, coe_inclRToRa, y, z, E, map_mul, map_add, map_pow]
    linear_combination (ι (C (a ^ 2 - a)) * ι A ^ 2) *
      IsLocalization.Away.mul_invSelf (S := L a) (X - C a)
  have hy : inclRToRa a ha0 ha1 y ∈ Q.asIdeal := by
    rw [← mem_comap_inclRToRa, hQ, mRPoint_asIdeal, mem_mR]
    simp [y]
  have hz : z ∈ (PrimeSpectrum.comap (inclRToRa a ha0 ha1).toRingHom Q).asIdeal := by
    rw [mem_comap_inclRToRa, ← hyz]
    exact Q.asIdeal.mul_mem_right _ hy
  rw [hQ, mRPoint_asIdeal, mem_mR] at hz
  have ha : a ^ 2 - a ≠ 0 := by
    rw [sq, ← mul_sub_one]
    exact mul_ne_zero ha0 (sub_ne_zero.mpr ha1)
  simp [z, A, ha] at hz

/-- A point of `Spec R` containing `𝔪_a` is `𝔪_a`, since `𝔪_a` is maximal. -/
private lemma eq_mRPoint_of_forall_mem {P : PrimeSpectrum R} (h : ∀ s ∈ mR a, s ∈ P.asIdeal) :
    P = mRPoint a :=
  PrimeSpectrum.ext ((mR_isMaximal a).eq_of_le P.isPrime.ne_top h).symm

/-- Every point of `Spec R_a` avoids some element of `𝔪_a`. -/
lemma exists_mem_mR_notMem (Q : PrimeSpectrum (Ra a ha0 ha1)) :
    ∃ s ∈ mR a, inclRToRa a ha0 ha1 s ∉ Q.asIdeal := by
  by_contra! h
  exact comap_ne_mRPoint Q (eq_mRPoint_of_forall_mem fun s hs => mem_comap_inclRToRa.mpr (h s hs))

/-- Every point of `Spec R` other than `𝔪_a` comes from `Spec R_a`: lie over it in `ℚ[z]`,
which is integral over `R`, and pass to the localization `ℚ[z, 1/(z-a)]`. -/
lemma exists_comap_eq {p : PrimeSpectrum R} (hp : p ≠ mRPoint a) :
    ∃ Q : PrimeSpectrum (Ra a ha0 ha1),
      PrimeSpectrum.comap (inclRToRa a ha0 ha1).toRingHom Q = p := by
  obtain ⟨Q', -, hQ', hQ'p⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal
    (⊥ : Ideal (Polynomial ℚ)) (Ideal.comap_bot_le_of_injective _ Subtype.val_injective)
  have hdisj : Disjoint (Submonoid.powers (X - C a) : Set (Polynomial ℚ)) Q' := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨n, rfl⟩ hn
    refine hp (eq_mRPoint_of_forall_mem fun s hs => ?_)
    obtain ⟨t, ht⟩ := X_sub_C_dvd_of_mem_mR hs
    rw [← hQ'p, Ideal.mem_comap]
    simpa [ht] using Q'.mul_mem_right t (hQ'.mem_of_pow_mem n hn)
  obtain ⟨Q'', hQ''⟩ : (⟨Q', hQ'⟩ : PrimeSpectrum (Polynomial ℚ)) ∈
      Set.range (PrimeSpectrum.comap (algebraMap (Polynomial ℚ) (L a))) := by
    rw [PrimeSpectrum.localization_comap_range (L a) (Submonoid.powers (X - C a))]
    exact hdisj
  refine ⟨PrimeSpectrum.comap (Ra a ha0 ha1).val.toRingHom Q'', PrimeSpectrum.ext ?_⟩
  have h : Ideal.comap (algebraMap (Polynomial ℚ) (L a)) Q''.asIdeal = Q' := by
    rw [← PrimeSpectrum.comap_asIdeal]
    exact congrArg PrimeSpectrum.asIdeal hQ''
  rw [← hQ'p, ← h]
  ext f
  simp [coe_inclRToRa, IsScalarTower.algebraMap_apply R (Polynomial ℚ) (L a)]

/-- Two points of `Spec R_a` over the same point of `Spec R` coincide. -/
lemma mem_of_comap_eq {Q₁ Q₂ : PrimeSpectrum (Ra a ha0 ha1)}
    (h : PrimeSpectrum.comap (inclRToRa a ha0 ha1).toRingHom Q₁ =
      PrimeSpectrum.comap (inclRToRa a ha0 ha1).toRingHom Q₂)
    {y : Ra a ha0 ha1} (hy : y ∈ Q₁.asIdeal) : y ∈ Q₂.asIdeal := by
  obtain ⟨s, hs, hsQ⟩ := exists_mem_mR_notMem Q₁
  rw [← mem_comap_inclRToRa, h, mem_comap_inclRToRa] at hsQ
  obtain ⟨k, x, hx⟩ := exists_pow_mul_eq hs y
  have hxQ : x ∈ (PrimeSpectrum.comap (inclRToRa a ha0 ha1).toRingHom Q₁).asIdeal := by
    rw [mem_comap_inclRToRa, ← hx]
    exact Q₁.asIdeal.mul_mem_left _ hy
  rw [h, mem_comap_inclRToRa, ← hx] at hxQ
  exact (Q₂.isPrime.mem_or_mem hxQ).resolve_left fun h' => hsQ (Q₂.isPrime.mem_of_pow_mem k h')

/-- The image of a basic open `D(y) ⊆ Spec R_a` is open in `Spec R`: near the image of a point
avoiding `s ∈ 𝔪_a` it contains `D(x s)`, where `s^k y = x`. -/
lemma isOpen_image_basicOpen (y : Ra a ha0 ha1) :
    IsOpen (PrimeSpectrum.comap (inclRToRa a ha0 ha1).toRingHom ''
      (PrimeSpectrum.basicOpen y : Set (PrimeSpectrum (Ra a ha0 ha1)))) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨Q, hQy, rfl⟩
  obtain ⟨s, hs, hsQ⟩ := exists_mem_mR_notMem Q
  obtain ⟨k, x, hx⟩ := exists_pow_mul_eq hs y
  have hxs : inclRToRa a ha0 ha1 (x * s) = inclRToRa a ha0 ha1 s ^ (k + 1) * y := by
    rw [map_mul, ← hx]
    ring
  refine ⟨PrimeSpectrum.basicOpen (x * s), ?_, PrimeSpectrum.isOpen_basicOpen, ?_⟩
  · intro p hp
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hp
    have hsp : s ∉ p.asIdeal := fun h => hp (p.asIdeal.mul_mem_left x h)
    obtain ⟨Q', rfl⟩ := exists_comap_eq (ha0 := ha0) (ha1 := ha1) (p := p) fun h =>
      hsp (by rwa [h, mRPoint_asIdeal])
    refine ⟨Q', (PrimeSpectrum.mem_basicOpen _ _).mpr fun hyQ => hp ?_, rfl⟩
    rw [mem_comap_inclRToRa, hxs]
    exact Q'.asIdeal.mul_mem_left _ hyQ
  · rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, mem_comap_inclRToRa, hxs]
    intro h
    rcases Q.isPrime.mem_or_mem h with h | h
    · exact hsQ (Q.isPrime.mem_of_pow_mem _ h)
    · exact (PrimeSpectrum.mem_basicOpen _ _).mp hQy h

/-- The inclusion `R ↪ R_a` induces an open embedding
`θ : Spec R_a → Spec R`. -/
@[stacks 00F1 "`θ : Spec R_a → Spec R` is an open embedding"]
theorem isOpenEmbedding_comap_inclRToRa (a : ℚ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    Topology.IsOpenEmbedding
      (PrimeSpectrum.comap (inclRToRa a ha0 ha1).toRingHom) := by
  refine .of_continuous_injective_isOpenMap (PrimeSpectrum.continuous_comap _)
    (fun Q₁ Q₂ h => PrimeSpectrum.ext (Ideal.ext fun y =>
      ⟨mem_of_comap_eq h, mem_of_comap_eq h.symm⟩)) ?_
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.isOpenMap_iff]
  rintro _ ⟨y, rfl⟩
  exact isOpen_image_basicOpen y

/-- The image of `θ : Spec R_a → Spec R` is exactly the complement of the
closed point `𝔪_a` in `Spec R`. -/
@[stacks 00F1 "the image of `θ` is `Spec R ∖ {𝔪_a}`"]
theorem range_comap_inclRToRa (a : ℚ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    Set.range (PrimeSpectrum.comap (inclRToRa a ha0 ha1).toRingHom) =
      {p : PrimeSpectrum R | p ≠ mRPoint a} := by
  ext p
  refine ⟨?_, exists_comap_eq⟩
  rintro ⟨Q, rfl⟩
  exact comap_ne_mRPoint Q

/-- An irreducible polynomial dividing `z - b` and `z - c` forces `b = c`. -/
lemma eq_of_dvd_X_sub_C {K : Type*} [Field K] {p : K[X]} (hp : Irreducible p) {b c : K}
    (hb : p ∣ X - C b) (hc : p ∣ X - C c) : b = c := by
  by_contra hbc
  have hu : p ∣ C (c - b) := by simpa [C_sub] using dvd_sub hb hc
  exact hp.not_isUnit (isUnit_of_dvd_unit hu (isUnit_C.mpr (sub_ne_zero.mpr (Ne.symm hbc)).isUnit))

/-- An irreducible polynomial `p` not dividing `z - a` gives a point of `Spec R`, namely
`pℚ[z] ∩ R`, different from `𝔪_a`. -/
lemma comap_span_ne_mRPoint (ha0 : a ≠ 0) (ha1 : a ≠ 1) {p : Polynomial ℚ}
    (hp : Irreducible p) (hpa : ¬ p ∣ X - C a) :
    (⟨Ideal.comap R.val (Ideal.span {p}),
      ((Ideal.span_singleton_prime hp.ne_zero).mpr hp.prime).comap _⟩ : PrimeSpectrum R) ≠
      mRPoint a := by
  intro h
  have h' : Ideal.comap R.val (Ideal.span {p}) = mR a := by
    simpa using congrArg PrimeSpectrum.asIdeal h
  have hmem : ∀ f : R, f ∈ mR a → p ∣ (f : Polynomial ℚ) := fun f hf => by
    rwa [← h', Ideal.mem_comap, Ideal.mem_span_singleton] at hf
  have h1 := hmem _ (mk_X_sub_C_mul_mem_mR a)
  have h2 := hmem ⟨(X - C a) * ((X - C 0) * (X - C 1)), by simp [mem_R]⟩ (by simp [mem_mR])
  have h1 := (hp.prime.dvd_or_dvd h1).resolve_left hpa
  rcases (hp.prime.dvd_or_dvd ((hp.prime.dvd_or_dvd h2).resolve_left hpa)).symm with h2 | h2
  · exact ha0 (by linarith [eq_of_dvd_X_sub_C hp h1 h2])
  · exact ha1 (by linarith [eq_of_dvd_X_sub_C hp h1 h2])

end Spec

/-- **Headline.** The image of `θ : Spec R_a → Spec R` is **not** the basic
open `D(f)` of any element `f ∈ R`. Hence `Spec R_a ⊂ Spec R` is an affine
open which is not standard / principal. -/
@[stacks 00F1]
theorem range_comap_inclRToRa_ne_basicOpen (a : ℚ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha12 : a ≠ 1 / 2) (f : R) :
    Set.range (PrimeSpectrum.comap (inclRToRa a ha0 ha1).toRingHom) ≠
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  intro hf
  rw [range_comap_inclRToRa a ha0 ha1] at hf
  have hmem : ∀ p : PrimeSpectrum R, p ≠ mRPoint a ↔ f ∉ p.asIdeal := fun p => by
    simpa using congrArg (p ∈ ·) hf
  have hfa : (f : Polynomial ℚ).IsRoot a := by
    have := (hmem (mRPoint a)).not
    rw [not_not, not_not, mRPoint_asIdeal, mem_mR, iff_true_left rfl] at this
    exact IsRoot.def.mpr this
  have hf0 : (f : Polynomial ℚ) ≠ 0 := by
    have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ≠ mRPoint a := by
      intro h
      have hu := mk_X_sub_C_mul_mem_mR a
      have h' : (⊥ : Ideal R) = mR a := by simpa using congrArg PrimeSpectrum.asIdeal h
      rw [← h', Ideal.mem_bot, ← Subtype.coe_inj, ZeroMemClass.coe_zero] at hu
      exact ((monic_X_sub_C a).mul (monic_X_sub_C (1 - a))).ne_zero hu
    simpa using (hmem _).mp hbot
  have hfg := pow_mul_divByMonic_rootMultiplicity_eq (f : Polynomial ℚ) a
  set g := (f : Polynomial ℚ) /ₘ (X - C a) ^ rootMultiplicity a f
  have hga : g.eval a ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero a hf0
  by_cases hg : IsUnit g
  · obtain ⟨r, hr, hrg⟩ := Polynomial.isUnit_iff.mp hg
    have hn := (rootMultiplicity_pos hf0).mpr hfa
    have h01 := mem_R.mp f.property
    rw [← hfg, ← hrg] at h01
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, zero_sub] at h01
    have h := congrArg abs (mul_right_cancel₀ hr.ne_zero h01)
    rw [abs_pow, abs_pow, pow_left_inj₀ (abs_nonneg _) (abs_nonneg _) hn.ne', abs_eq_abs] at h
    rcases h with h | h
    · linarith
    · exact ha12 (by linarith)
  · obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor hg
      fun h => hga (by simp [h])
    have hpa : ¬ p ∣ X - C a := fun h =>
      hga ((dvd_iff_isRoot.mp ((hp.dvd_symm (irreducible_X_sub_C a) h).trans hpg)))
    refine (hmem _).mp (comap_span_ne_mRPoint ha0 ha1 hp hpa) ?_
    rw [Ideal.mem_comap, Subalgebra.coe_val, Ideal.mem_span_singleton, ← hfg]
    exact hpg.mul_left _

/-- `R_a` is **not** a localization of `R`: there is no submonoid `S ⊆ R`
for which `R_a` becomes the localization `S⁻¹ R` via `inclRToRa`. -/
@[stacks 00F1 "`R_a` is not a localization of `R`"]
theorem not_exists_isLocalization (a : ℚ)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha12 : a ≠ 1 / 2) :
    let _ : Algebra R (Ra a ha0 ha1) := (inclRToRa a ha0 ha1).toAlgebra
    ¬ ∃ (S : Submonoid R), IsLocalization S (Ra a ha0 ha1) := by
  rintro _ ⟨S, hS⟩
  have hrange := @PrimeSpectrum.localization_comap_range R (Ra a ha0 ha1) _ _
    (inclRToRa a ha0 ha1).toAlgebra S hS
  rw [RingHom.algebraMap_toAlgebra, range_comap_inclRToRa a ha0 ha1] at hrange
  have key : ∀ p : PrimeSpectrum R, p ≠ mRPoint a ↔ Disjoint (S : Set R) p.asIdeal := by
    intro p
    have := Set.ext_iff.mp hrange p
    rwa [Set.mem_ofPred_eq, Set.mem_ofPred_eq] at this
  obtain ⟨s, hsS, hsm⟩ := Set.not_disjoint_iff.mp fun h => (key (mRPoint a)).mpr (by simpa) rfl
  refine range_comap_inclRToRa_ne_basicOpen a ha0 ha1 ha12 s
    ((range_comap_inclRToRa a ha0 ha1).trans (Set.ext fun p => ?_))
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, Set.mem_ofPred_eq]
  refine ⟨fun h hs => Set.disjoint_left.mp ((key p).mp h) hsS hs, fun h hp => h ?_⟩
  simpa [hp] using hsm

end

end NodalCubicAffineOpen

end
