module

public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialPolynomial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Hilbert polynomials are determined by finitely many values

A function `f : ℤ → ℤ` has *backward-difference degree at most `n`*
(`IsDifferenceBounded n f`) when its `n`-th iterated backward difference
`d ↦ f d - f (d - 1)` is constant. Two such functions which agree at `n + 1` consecutive
integers agree everywhere (`eq_of_isDifferenceBounded`), and every one of them agrees at *every*
integer with a rational polynomial (`exists_polynomial_of_isDifferenceBounded`).

The Hilbert polynomial `d ↦ χ(ℙⁿ_k, ℱ(d))` of a coherent sheaf on `ℙⁿ_k` has
backward-difference degree at most `n`, over every field `k`
(`AlgebraicGeometry.isDifferenceBounded_hilbertPolynomial`). Hence it is a polynomial in `d` at
every integer, which is [Stacks, Tag 08AC] as the source states it
(`AlgebraicGeometry.exists_polynomial_eval_eq_hilbertPolynomial`). Consequently Hilbert functions
of coherent sheaves on `ℙⁿ`, possibly over two different fields, agree everywhere as soon as they
agree at `d = 0, …, n` (`AlgebraicGeometry.hilbertPolynomial_eq_of_forall_le`).

## Main definitions

* `IsDifferenceBounded n f`: the `n`-th backward difference of `f` is constant.

## Main results

* `eq_of_isDifferenceBounded`: functions of backward-difference degree at most `n` agreeing at
  `a, a + 1, …, a + n` are equal.
* `exists_polynomial_of_isDifferenceBounded`: a function of backward-difference degree at most
  `n` agrees at every integer with a rational polynomial.
* `AlgebraicGeometry.isDifferenceBounded_hilbertPolynomial`: the Hilbert polynomial on `ℙⁿ_k` has
  backward-difference degree at most `n`, for any field `k`.
* `AlgebraicGeometry.exists_polynomial_eval_eq_hilbertPolynomial`: **[Stacks, Tag 08AC]** —
  `d ↦ χ(ℙⁿ_k, ℱ(d))` is given by a rational polynomial at every integer `d`.
* `AlgebraicGeometry.hilbertPolynomial_eq_of_forall_le`: two Hilbert polynomials on `ℙⁿ` agreeing
  at `0, …, n` are equal.

## Implementation notes

The degree bound is the induction of the proof of [Stacks, Tag 08AC], tracked with the
dimension: on `ℙ⁰_k` the twists are trivial (`AlgebraicGeometry.projectiveTwistZeroIso`), so the
Hilbert polynomial is constant; on `ℙ^{m+1}_k` over an infinite field its first difference is a
Hilbert polynomial on `ℙᵐ_k` (`AlgebraicGeometry.exists_coherent_hilbertPolynomial_sub_eq`). A
general field is reduced to the infinite field `RatFunc k`, which does not change the Hilbert
polynomial (`AlgebraicGeometry.hilbertPolynomial_pullback_fieldExtension`).

From the degree bound the polynomial itself is produced by induction on the order of the
difference: a constant function is a constant polynomial, and a function whose first difference
is already known to be a polynomial is integrated by `Polynomial.exists_antidifference`, the
every-integer form of [Stacks, Tag 00JZ] the source's proof appeals to. This is why the tag in
its stated form — a polynomial identity at *every* `d`, not only for `d` large — is proved here
rather than in `StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialPolynomial`,
whose `AlgebraicGeometry.isNumericalPolynomial_hilbertPolynomial'` only gives the weaker
`IsNumericalPolynomial` reading ([Stacks, Tag 00JX]): the degree bound that feeds the induction
is proved in this file, downstream of that one.

## References

* [Stacks Project, Tag 08AC](https://stacks.math.columbia.edu/tag/08AC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/-- `IsDifferenceBounded n f` says that the `n`-th iterated backward difference of
`f : ℤ → ℤ` is constant, the backward difference of `f` being `d ↦ f d - f (d - 1)`. For a
function given by a polynomial this says that the polynomial has degree at most `n`. -/
def IsDifferenceBounded : ℕ → (ℤ → ℤ) → Prop
  | 0, f => ∃ c, ∀ d, f d = c
  | n + 1, f => IsDifferenceBounded n (fun d => f d - f (d - 1))

theorem isDifferenceBounded_zero_iff (f : ℤ → ℤ) :
    IsDifferenceBounded 0 f ↔ ∃ c, ∀ d, f d = c :=
  Iff.rfl

/-- A function has backward-difference degree at most `n + 1` if and only if its backward
difference `d ↦ f d - f (d - 1)` has backward-difference degree at most `n`. -/
theorem isDifferenceBounded_succ_iff (n : ℕ) (f : ℤ → ℤ) :
    IsDifferenceBounded (n + 1) f ↔ IsDifferenceBounded n (fun d => f d - f (d - 1)) :=
  Iff.rfl

/-- A function on `ℤ` with `g (k + 1) = g k` for all `k` is constant. -/
private theorem apply_eq_apply_zero_of_forall_add_one {α : Type*} (g : ℤ → α)
    (hg : ∀ k, g (k + 1) = g k) (k : ℤ) : g k = g 0 := by
  induction k using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [hg, ih]
  | pred k ih =>
    have := hg (-(k : ℤ) - 1)
    rw [sub_add_cancel] at this
    rw [← this, ih]

/-- A function whose backward difference vanishes identically is constant: its value anywhere
is its value at a given point. -/
theorem eq_of_forall_sub_sub_one_eq_zero {h : ℤ → ℤ} (hh : ∀ d, h d - h (d - 1) = 0) (a d : ℤ) :
    h d = h a := by
  have := apply_eq_apply_zero_of_forall_add_one (fun k => h (a + k)) (fun k => by
    have := hh (a + (k + 1))
    rw [show a + (k + 1) - 1 = a + k by ring] at this
    simpa [sub_eq_zero] using this) (d - a)
  simpa using this

/-- **Finite determination.** Two functions `ℤ → ℤ` whose `n`-th backward differences are
constant agree everywhere as soon as they agree at the `n + 1` consecutive integers
`a, a + 1, …, a + n`. -/
theorem eq_of_isDifferenceBounded {n : ℕ} {f g : ℤ → ℤ} (hf : IsDifferenceBounded n f)
    (hg : IsDifferenceBounded n g) (a : ℤ) (h : ∀ i : ℕ, i ≤ n → f (a + i) = g (a + i)) :
    f = g := by
  induction n generalizing f g a with
  | zero =>
    obtain ⟨c, hc⟩ := hf
    obtain ⟨c', hc'⟩ := hg
    have hcc : c = c' := by
      have := h 0 le_rfl
      rwa [hc, hc'] at this
    funext d
    rw [hc, hc', hcc]
  | succ n ih =>
    have hdiff : (fun d => f d - f (d - 1)) = (fun d => g d - g (d - 1)) := by
      refine ih hf hg (a + 1) fun i hi => ?_
      have h1 := h (i + 1) (by omega)
      have h0 := h i (by omega)
      push_cast at h1
      rw [show a + 1 + (i : ℤ) - 1 = a + i by ring, show a + 1 + (i : ℤ) = a + (i + 1) by ring,
        h1, h0]
    have hconst : ∀ d, (f d - g d) - (f (d - 1) - g (d - 1)) = 0 := by
      intro d
      have := congrFun hdiff d
      linarith
    funext d
    have := eq_of_forall_sub_sub_one_eq_zero (h := fun d => f d - g d) hconst a d
    have ha := h 0 (Nat.zero_le _)
    simp only [Nat.cast_zero, add_zero] at ha this
    linarith

/-- **A function on `ℤ` with constant `m`-th backward difference is a rational polynomial.** The
agreement is at *every* integer, not merely at large ones. -/
theorem exists_polynomial_of_isDifferenceBounded :
    ∀ (m : ℕ) (f : ℤ → ℤ), IsDifferenceBounded m f →
      ∃ P : Polynomial ℚ, ∀ d : ℤ, (f d : ℚ) = P.eval (d : ℚ)
  | 0, f, ⟨c, hc⟩ => ⟨Polynomial.C (c : ℚ), fun d => by simp [hc d]⟩
  | m + 1, f, h => by
    obtain ⟨Q, hQ⟩ := exists_polynomial_of_isDifferenceBounded m _ h
    obtain ⟨P₀, -, hP₀zero, hP₀⟩ := Polynomial.exists_antidifference
      (Q.comp (Polynomial.X + 1)).natDegree (Q.comp (Polynomial.X + 1)) le_rfl
    have step : ∀ k : ℤ, (f (k + 1) : ℚ) - P₀.eval ((k + 1 : ℤ) : ℚ) =
        (f k : ℚ) - P₀.eval (k : ℚ) := by
      intro k
      have h1 := hQ (k + 1)
      have h2 := hP₀ (k : ℚ)
      simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_one] at h2
      have e : ((k + 1 : ℤ) : ℚ) = (k : ℚ) + 1 := by push_cast; ring
      simp only [add_sub_cancel_right, Int.cast_sub] at h1
      rw [e]
      push_cast at h1
      linarith
    have key := apply_eq_apply_zero_of_forall_add_one
      (fun k : ℤ => (f k : ℚ) - P₀.eval (k : ℚ)) step
    refine ⟨P₀ + Polynomial.C (f 0 : ℚ), fun d => ?_⟩
    have := key d
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    simp only [Int.cast_zero, hP₀zero] at this
    linarith

namespace AlgebraicGeometry

attribute [local instance] isCoherent_projectiveTwist

/-- **The Hilbert polynomial on `ℙⁿ_k` has degree at most `n`, over an infinite field.** Its
`n`-th backward difference is constant. -/
theorem isDifferenceBounded_hilbertPolynomial_of_infinite (k : Type u) [Field k] [Infinite k]
    (n : ℕ) (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] :
    IsDifferenceBounded n (hilbertPolynomial k n F) := by
  suffices h : ∀ (m : ℕ) (G : (projectiveSpaceOverRing m (.of k)).Modules) (hG : G.IsCoherent),
      IsDifferenceBounded m (@hilbertPolynomial k _ m G hG) from h n F ‹_›
  intro m
  induction m with
  | zero =>
    intro G hG
    refine ⟨eulerCharacteristic k (projectiveSpaceOverRing 0 (.of k) ↘ Spec (.of k)) G,
      fun d => ?_⟩
    rw [hilbertPolynomial_eq_eulerCharacteristic]
    exact eulerCharacteristic_eq_of_iso k _ (projectiveTwistZeroIso k G d)
  | succ p ih =>
    intro G hG
    obtain ⟨H, hH, hd⟩ := exists_coherent_hilbertPolynomial_sub_eq k p G hG
    rw [isDifferenceBounded_succ_iff]
    have hfun : (fun d => @hilbertPolynomial k _ (p + 1) G hG d -
        @hilbertPolynomial k _ (p + 1) G hG (d - 1)) = @hilbertPolynomial k _ p H hH :=
      funext hd
    rw [hfun]
    exact ih H hH

/-- **The Hilbert polynomial on `ℙⁿ_k` has degree at most `n`, over every field.** For a field
`k` and a coherent sheaf `ℱ` on `ℙⁿ_k`, the `n`-th backward difference of `d ↦ χ(ℙⁿ_k, ℱ(d))` is
constant. -/
@[ega "III 2.5.3" "(i), special case"]
theorem isDifferenceBounded_hilbertPolynomial (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] :
    IsDifferenceBounded n (hilbertPolynomial k n F) := by
  have : Infinite (RatFunc k) := infinite_ratFunc k
  have : IsLocallyNoetherian (projectiveSpaceOverRing n (CommRingCat.of (RatFunc k))) :=
    projectiveSpaceOver_isLocallyNoetherian n (Spec (CommRingCat.of (RatFunc k)))
  have hFK : ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj F).IsCoherent :=
    isCoherent_pullback (projectiveSpaceFieldExtensionMap k (RatFunc k) n) F
  have := hFK
  have hfun : hilbertPolynomial (RatFunc k) n
      ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj F) =
      hilbertPolynomial k n F :=
    funext (hilbertPolynomial_pullback_fieldExtension k (RatFunc k) n F hFK)
  rw [← hfun]
  exact isDifferenceBounded_hilbertPolynomial_of_infinite (RatFunc k) n _

/-- **[Stacks, Tag 08AC].** Let `k` be a field, let `n ≥ 0` and let `ℱ` be a coherent sheaf on
`ℙⁿ_k`. Then the function `d ↦ χ(ℙⁿ_k, ℱ(d))` is a polynomial: there is a `P ∈ ℚ[X]` with
`χ(ℙⁿ_k, ℱ(d)) = P(d)` for **every** `d ∈ ℤ`. **No hypothesis.**

The `n`-th backward difference of the Hilbert polynomial is constant
(`AlgebraicGeometry.isDifferenceBounded_hilbertPolynomial`, the source's induction on `n`), and a
function on `ℤ` with a constant iterated backward difference is a polynomial at every integer
(`exists_polynomial_of_isDifferenceBounded`, the every-integer form of [Stacks, Tag 00JZ] the
source's proof ends with).

The weaker eventual reading of "is a polynomial", [Stacks, Tag 00JX]'s `IsNumericalPolynomial`,
is `AlgebraicGeometry.isNumericalPolynomial_hilbertPolynomial'`. -/
@[stacks 08AC]
theorem exists_polynomial_eval_eq_hilbertPolynomial (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] :
    ∃ P : Polynomial ℚ, ∀ d : ℤ, (hilbertPolynomial k n F d : ℚ) = P.eval (d : ℚ) :=
  exists_polynomial_of_isDifferenceBounded n _ (isDifferenceBounded_hilbertPolynomial k n F)

/-- **Hilbert polynomials on `ℙⁿ` are determined by their values at `0, …, n`.** For coherent
sheaves `ℱ` on `ℙⁿ_k` and `𝒢` on `ℙⁿ_K`, over possibly different fields `k` and `K`, if
`χ(ℙⁿ_k, ℱ(i)) = χ(ℙⁿ_K, 𝒢(i))` for `i = 0, …, n` then the two Hilbert polynomials are equal. -/
theorem hilbertPolynomial_eq_of_forall_le (k K : Type u) [Field k] [Field K] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent]
    (G : (projectiveSpaceOverRing n (.of K)).Modules) [G.IsCoherent]
    (h : ∀ i : ℕ, i ≤ n → hilbertPolynomial k n F i = hilbertPolynomial K n G i) :
    hilbertPolynomial k n F = hilbertPolynomial K n G :=
  eq_of_isDifferenceBounded (isDifferenceBounded_hilbertPolynomial k n F)
    (isDifferenceBounded_hilbertPolynomial K n G) 0 fun i hi => by
      simpa using h i hi

end AlgebraicGeometry

end
