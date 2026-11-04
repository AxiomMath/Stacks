module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Perfect
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Ring

/-!
# Absolutely weakly normal algebras over a prime field

An algebra over the prime field `𝐅_p` is absolutely weakly normal exactly when its Frobenius
endomorphism is bijective, that is, exactly when it is a perfect ring.

## Main results

* `isAbsolutelyWeaklyNormalRing_iff_perfectRing` characterizes absolutely weakly normal
  `𝐅_p`-algebras as perfect rings.

## Implementation notes

An `𝐅_p`-algebra is represented by an `Algebra (ZMod p) A` instance. Perfectness is expressed
by Mathlib's `PerfectRing A p`, whose Frobenius condition includes both injectivity and
surjectivity.

## References

* [Stacks Project, Tag 0EVV](https://stacks.math.columbia.edu/tag/0EVV)
-/

@[expose] public section

/-- In a monoid, an element is determined on all powers `n ≥ 2` by its square and its cube. -/
private theorem pow_eq_of_sq_cube_eq {A : Type*} [Monoid A] {a b : A}
    (h2 : a ^ 2 = b ^ 2) (h3 : a ^ 3 = b ^ 3) {n : ℕ} (hn : 2 ≤ n) :
    a ^ n = b ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain rfl | rfl | hn4 : n = 2 ∨ n = 3 ∨ 4 ≤ n := by lia
    · exact h2
    · exact h3
    calc
      a ^ n = a ^ (n - 2) * a ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hn]
      _ = b ^ (n - 2) * b ^ 2 := by rw [ih (n - 2) (by lia) (by lia), h2]
      _ = b ^ n := by rw [← pow_add, Nat.sub_add_cancel hn]

/-- Every odd number at least `5` is a nonnegative combination `2 * n + 3 * m` of `2` and
`3`. -/
private theorem exists_two_mul_add_three_mul {p : ℕ}
    (hpodd : p % 2 = 1) (hp5 : 5 ≤ p) : ∃ n m : ℕ, p = 2 * n + 3 * m :=
  ⟨(p - 3) / 2, 1, by lia⟩

/-- An algebra over `𝐅_p`, for `p` prime, is absolutely weakly normal if and only if its
Frobenius endomorphism is bijective. -/
@[stacks 0EVV]
lemma isAbsolutelyWeaklyNormalRing_iff_perfectRing
    (p : ℕ) (hp : p.Prime) (A : Type*) [CommRing A] [Algebra (ZMod p) A] :
    IsAbsolutelyWeaklyNormalRing A ↔ PerfectRing A p := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · refine ⟨fun _ => ⟨⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩⟩,
      fun _ => ⟨(isSeminormalRing_iff A).2 fun _ _ _ => ?_, fun _ _ _ _ _ => ?_⟩⟩ <;>
    exact ⟨0, ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP A p := (Algebra.charP_iff (ZMod p) A p).mp (ZMod.charP p)
  refine ⟨fun hweak => ?_, fun hperf => ?_⟩
  · have : IsReduced A := seminormalRing_isReduced hweak.isSeminormalRing
    refine PerfectRing.ofSurjective A p fun x => ?_
    obtain ⟨a, ha, -⟩ := hweak.existsUnique_of_prime_pow_mul_eq_pow hp (x := x) (y := 0)
      (by simp [hp.ne_zero])
    exact ⟨a, ha.1.symm⟩
  have hF : Function.Bijective (fun x : A => x ^ p) := hperf.bijective_frobenius
  refine ⟨(isSeminormalRing_iff A).2 fun x y hxy => ?_, fun q hq x y hxy => ?_⟩
  · have hp2 := hp.two_le
    obtain ⟨n, m, hnm⟩ : ∃ n m : ℕ, p = 2 * n + 3 * m := ⟨p / 2 - p % 2, p % 2, by lia⟩
    obtain ⟨a, ha : a ^ p = x⟩ := hF.2 x
    obtain ⟨b, hb : b ^ p = y⟩ := hF.2 y
    have key (k : ℕ) : ((a ^ n * b ^ m) ^ k) ^ p = (a ^ p) ^ (k * n) * (b ^ p) ^ (k * m) := by
      ring
    have hc2 : (a ^ n * b ^ m) ^ 2 = x := hF.1 <| show _ ^ p = x ^ p by
      rw [key, ha, hb, pow_mul y, ← hxy, ← pow_mul, ← pow_add, hnm]
    have hc3 : (a ^ n * b ^ m) ^ 3 = y := hF.1 <| show _ ^ p = y ^ p by
      rw [key, ha, hb, pow_mul x, hxy, ← pow_mul, ← pow_add, hnm]
    exact ⟨a ^ n * b ^ m, ⟨hc2.symm, hc3.symm⟩, fun c hc => hF.1 <|
      pow_eq_of_sq_cube_eq (hc.1.symm.trans hc2.symm) (hc.2.symm.trans hc3.symm) hp2⟩
  by_cases hqp : q = p
  · subst q
    have hy : y = 0 := hF.1 <| show y ^ p = 0 ^ p by rw [← hxy]; simp [hp.ne_zero]
    obtain ⟨a, ha : a ^ p = x⟩ := hF.2 x
    exact ⟨a, ⟨ha.symm, by simp [hy]⟩, fun b hb => hF.1 (hb.1.symm.trans ha.symm)⟩
  have hqZ : (q : ZMod p) ≠ 0 := fun hz =>
    hqp ((hq.dvd_iff_eq hp.ne_one).mp ((CharP.cast_eq_zero_iff (ZMod p) p q).mp hz))
  have huq : IsUnit (q : A) := by
    simpa using (isUnit_iff_ne_zero.mpr hqZ).map (algebraMap (ZMod p) A)
  refine ⟨↑huq.unit⁻¹ * y, ⟨?_, ?_⟩, fun b hb => ?_⟩
  · rw [mul_pow, ← hxy, ← mul_assoc, ← mul_pow, huq.val_inv_mul, one_pow, one_mul]
  · rw [← mul_assoc, huq.mul_val_inv, one_mul]
  · rw [hb.2, ← mul_assoc, huq.val_inv_mul, one_mul]
