module

public import StacksFrontier.NumberTheory.TraceFormula.CommutativeExampleCongruence

/-!
# The commutative example of an abstract trace formula

Fix an integer `q ≥ 1` and an extension of profinite groups `1 → G → Γ → Ẑ → 1` with
`G = Ẑ^{(q)} = ∏_{ℓ ∤ q} ℤ_ℓ`, `F ↦ 1` and `F x F⁻¹ = u x` for a unit `u ∈ (Ẑ^{(q)})^*`
([Stacks, Tag 03VQ]). If `Γ` has an abstract trace formula with integer `q` and sets `S_d`
([Stacks, Section 03VO]), then, just using the trivial modules `ℤ/m`,

* `q^n - (qu)^n ≡ ∑_{d ∣ n} d #S_d` in `ℤ/m` for all `m` prime to `q`, that is, in
  `Ẑ^{(q)} = lim_{(m,q)=1} ℤ/m`;
* hence `qu = a ∈ ℤ`, namely `a = q - #S_1`;
* and `|a| ≤ q`, with `|a| < q` exactly when `u ≠ 1`, exactly when some `S_d` is nonempty.

**Correction.** The source states `|a| < q` unconditionally. This fails for `u = 1`: then `Γ` is
`Ẑ^{(q)} × Ẑ`, which has an abstract trace formula with all `S_d` empty (both sides of the trace
formula vanish, `F` acting identically on the two terms of the Koszul complex computing
`LH₀(Ẑ^{(q)}, M)`), and `a = q`. For `q = 1` it fails for every `Γ` with an abstract trace formula,
as then `a = u ∈ ℤ ∩ Ẑ^* = {±1}` and `a = -1` is excluded. What holds is the statement above.

* In the special case `a = 1` the sets `S_d` have the cardinalities `#S_1 = q - 1` and
  `#S_2 = ((q² - 1) - (q - 1))/2`, those of the closed points of `G_{m, F_q}` of degree `1`
  and `2`.

## Main results

* `Stacks.TraceFormula.commutativeExample_congruence`: the congruence, as an identity in
  `Ẑ^{(q)}` and as an identity of integers.
* `Stacks.TraceFormula.commutativeExample_integrality`: `qu = a ∈ ℤ` with `a = q - #S_1`,
  `|a| ≤ q`, and `|a| < q ↔ u ≠ 1 ↔ ∃ d ≥ 1, S_d ≠ ∅`.
* `Stacks.TraceFormula.commutativeExample_card_eq_of_eq_one`: the cardinalities of `S_1` and
  `S_2` when `a = 1`.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
* [Stacks Project, Section 03VO](https://stacks.math.columbia.edu/tag/03VO)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.TraceFormula

variable {q : ℕ} {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {deg : Γ →* Multiplicative ProfiniteIntegers}
  {hdeg : Continuous deg} {hsurj : Function.Surjective deg}
  (e : Multiplicative (RestrictedProfiniteIntegers q) ≃ₜ* deg.ker) {F : Γ}
  (hF : deg F = Multiplicative.ofAdd 1) (u : (RestrictedProfiniteIntegers q)ˣ)
  (hconj : ∀ x : RestrictedProfiniteIntegers q, F * (e (Multiplicative.ofAdd x) : Γ) * F⁻¹ =
    e (Multiplicative.ofAdd ((u : RestrictedProfiniteIntegers q) * x)))
  (T : AbstractTraceFormula Γ deg hdeg hsurj) (hTq : T.q = q)
include hF hconj hTq

/-- **Stacks Project, Tag 03VQ: the congruence.** If the extension
`1 → Ẑ^{(q)} → Γ → Ẑ → 1` with `F x F⁻¹ = u x` has an abstract trace formula with integer `q`,
then `q^n - (qu)^n ≡ ∑_{d ∣ n} d #S_d` in `ℤ/m` for every `m` prime to `q`: as an identity in
`Ẑ^{(q)} = lim_{(m,q)=1} ℤ/m`, and, `qu` being the integer `a = q - #S_1`, as the identity
`q^n - a^n = ∑_{d ∣ n} d #S_d` of integers. -/
@[stacks 03VQ "q^n - (qu)^n ≡ ∑_{d ∣ n} d #S_d in ℤ/m for all m prime to q, derived from the \
abstract trace formula on the trivial modules ℤ/m"]
public theorem commutativeExample_congruence (n : ℕ) (hn : 0 < n) :
    (q : RestrictedProfiniteIntegers q) ^ n - ((q : RestrictedProfiniteIntegers q) * u) ^ n =
        (pointCountSum (fun d => Fintype.card (T.S d)) n : RestrictedProfiniteIntegers q) ∧
      (q : ℤ) ^ n - ((q : ℤ) - Fintype.card (T.S 1)) ^ n =
        pointCountSum (fun d => Fintype.card (T.S d)) n := by
  have h := isTrivialModuleCongruence_of_abstractTraceFormula e hF u hconj T hTq
  refine ⟨?_, ?_⟩
  · rw [pow_eq_intCast h hn]
    push_cast
    ring
  · have hq : 1 ≤ q := hTq ▸ T.one_le_q
    have := traceParameter_pow hq h hn
    rw [traceParameter] at this
    linarith

/-- **Stacks Project, Tag 03VQ (corrected).** If the extension `1 → Ẑ^{(q)} → Γ → Ẑ → 1` with
`F x F⁻¹ = u x` has an abstract trace formula with integer `q` and sets `S_d`, then `qu = a ∈ ℤ`
with `a = q - #S_1`, and `|a| ≤ q`; moreover `|a| < q` exactly when `u ≠ 1`, exactly when some
`S_d` (`d ≥ 1`) is nonempty. The source's unconditional `|a| < q` fails for `u = 1`. -/
@[stacks 03VQ "corrected: qu = a ∈ ℤ with |a| ≤ q, and |a| < q iff u ≠ 1 iff some S_d is \
nonempty; the source's unconditional |a| < q fails for u = 1, where Γ = Ẑ^(q) × Ẑ has an abstract \
trace formula with all S_d empty"]
public theorem commutativeExample_integrality :
    ∃ a : ℤ, (q : RestrictedProfiniteIntegers q) * u = (a : RestrictedProfiniteIntegers q) ∧
      a = q - Fintype.card (T.S 1) ∧ |a| ≤ q ∧
      (|a| < q ↔ u ≠ 1) ∧ (|a| < q ↔ ∃ d : ℕ, 0 < d ∧ Nonempty (T.S d)) := by
  have h := isTrivialModuleCongruence_of_abstractTraceFormula e hF u hconj T hTq
  have hq : 1 ≤ q := hTq ▸ T.one_le_q
  set a := traceParameter q (fun d => Fintype.card (T.S d))
  have ha : (q : RestrictedProfiniteIntegers q) * u = (a : RestrictedProfiniteIntegers q) :=
    eq_intCast_traceParameter h
  have hlow := neg_lt_traceParameter hq h
  have hup : a ≤ q := traceParameter_le
  have hlt : |a| < q ↔ a ≠ q := by
    rw [abs_lt]
    exact ⟨fun h' => h'.2.ne, fun h₃ => ⟨hlow, hup.lt_of_ne h₃⟩⟩
  have hu : a = q ↔ u = 1 := by
    refine ⟨fun haq => ?_, fun hu1 => ?_⟩
    · rw [haq, Int.cast_natCast] at ha
      exact Units.ext ((isUnit_natCast_restrictedProfiniteIntegers q).mul_left_cancel
        (ha.trans (mul_one _).symm))
    · rw [hu1, Units.val_one, mul_one] at ha
      exact (intCast_injective hq (by rw [← ha, Int.cast_natCast])).symm
  have hS : a = q ↔ ¬ ∃ d : ℕ, 0 < d ∧ Nonempty (T.S d) := by
    rw [traceParameter_eq_iff hq h]
    simp only [not_exists, not_and, not_nonempty_iff, Fintype.card_eq_zero_iff]
  refine ⟨a, ha, rfl, abs_le.2 ⟨hlow.le, hup⟩, ?_, ?_⟩
  · rw [hlt, Ne, hu]
  · rw [hlt, Ne, hS, not_not]

/-- **Stacks Project, Tag 03VQ: the special case `a = 1`.** If `qu = 1`, the sets `S_1` and
`S_2` have `q - 1` and `((q² - 1) - (q - 1))/2` elements, the numbers of closed points of
`G_{m, F_q}` of degree `1` and `2`. -/
@[stacks 03VQ "the special case a = 1: #S₁ = q - 1 and #S₂ = ((q² - 1) - (q - 1))/2"]
public theorem commutativeExample_card_eq_of_eq_one
    (h1 : (q : RestrictedProfiniteIntegers q) * u = 1) :
    Fintype.card (T.S 1) = q - 1 ∧ Fintype.card (T.S 2) = ((q ^ 2 - 1) - (q - 1)) / 2 := by
  have h := isTrivialModuleCongruence_of_abstractTraceFormula e hF u hconj T hTq
  have hq : 1 ≤ q := hTq ▸ T.one_le_q
  have ha : traceParameter q (fun d => Fintype.card (T.S d)) = 1 := by
    refine intCast_injective hq ?_
    rw [← eq_intCast_traceParameter h, h1, Int.cast_one]
  have p1 := traceParameter_pow hq h (n := 1) one_pos
  have p2 := traceParameter_pow hq h (n := 2) two_pos
  rw [ha] at p1 p2
  have hd2 : pointCountSum (fun d => Fintype.card (T.S d)) 2 =
      Fintype.card (T.S 1) + 2 * Fintype.card (T.S 2) := by
    rw [pointCountSum, show Nat.divisors 2 = {1, 2} from rfl]
    simp
  rw [pointCountSum_one] at p1
  rw [hd2] at p2
  push_cast at p1 p2
  have hS1 : Fintype.card (T.S 1) = q - 1 := by lia
  refine ⟨hS1, ?_⟩
  have hS2 : 2 * Fintype.card (T.S 2) = (q ^ 2 - 1) - (q - 1) := by
    have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    zify [hq, hq2, show q - 1 ≤ q ^ 2 - 1 by
      have : q ≤ q ^ 2 := by nlinarith
      lia]
    nlinarith
  lia

end Stacks.TraceFormula

end
