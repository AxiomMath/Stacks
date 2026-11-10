module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.FiniteStage
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.UniversalProperty

/-! # Mapping out of a one-variable divided power extension

Let `A` be a strictly graded-commutative algebra with divided powers `γ` on its positive even
part, and let `d > 0`. Adjoining one homogeneous variable of degree `d` to `A` produces the odd
variable extension `A⟨T⟩` of Tag 09PH when `d` is odd, and the even variable algebra of Tag 09PI
when `d` is even. This file proves that a homomorphism out of either extension is determined by,
and may be prescribed by, its restriction to `A` together with the image of the variable.

Both statements are for a *ring* homomorphism `A →+* D` rather than an algebra homomorphism, and
the `R`-algebra structures on `A` and on `D` are unrelated: they serve only to express the two
gradings. This is what makes the results usable at a subring of a graded divided power algebra,
whose `R`-algebra structure is supplied abstractly and need not restrict the ambient one.

## Main results

* `DividedPowers.TateResolution.DividedPowerStructure.dpow_odd_mul_odd_eq_zero` — in any graded
  divided power algebra, a product of an odd element with an odd homogeneous element has
  vanishing divided powers above the first.
* `DividedPowers.TateResolution.DividedPowerStructure.dpow_add_odd_mul` — the divided powers of
  `x + y * t`, for `x` positive even, `y` odd and `t` odd homogeneous, are
  `γₙ(x) + γₙ₋₁(x) * (y * t)`.
* `DividedPowers.TateResolution.existsUnique_oddVariableExtension_ringHom` and
  `DividedPowers.TateResolution.existsUnique_evenVariableAlgebra_ringHom` — the mapping property
  of the two one-variable extensions, for ring homomorphisms.
* `DividedPowers.TateResolution.oddVariableExtension_ringHom_dpow` — such a map out of an odd
  variable extension is automatically compatible with divided powers.

## Implementation notes

The divided power formula on the odd side is proved for an arbitrary graded divided power
algebra, not just for the odd variable extension; this is what lets a prescribed map be
checked against the target's own divided powers.

## References

* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
* [Stacks Project, Tag 09PI](https://stacks.math.columbia.edu/tag/09PI)
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

universe u v w z

namespace DividedPowerStructure

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

/-- Positive divided powers of zero vanish. -/
public theorem dpow_zero_eq_zero (γ : DividedPowerStructure 𝒜) {n : ℕ} (hn : n ≠ 0) :
    γ.dpow n (0 : A) = 0 := by
  have h := γ.dpow_mul_even (n := n) hn (x := 0) (y := 0)
    (Submodule.zero_mem _) (Submodule.zero_mem _)
  rwa [zero_mul, zero_pow hn, zero_mul] at h

omit [IsStrictlyGradedComm 𝒜] in
/-- A product of an element of the odd part with an odd homogeneous element is positive even. -/
public theorem oddPart_mul_odd_mem_positiveEvenPart {q : ℕ} {y t : A}
    (hy : y ∈ oddPart 𝒜) (ht : t ∈ 𝒜 (2 * q + 1)) :
    y * t ∈ positiveEvenPart 𝒜 := by
  induction hy using Submodule.iSup_induction' with
  | mem e y hy =>
      refine Submodule.mem_iSup_of_mem (e + q) ?_
      have hm : y * t ∈ 𝒜 (2 * e + 1 + (2 * q + 1)) := SetLike.GradedMul.mul_mem hy ht
      have hdeg : 2 * e + 1 + (2 * q + 1) = 2 * (e + q + 1) := by omega
      rwa [hdeg] at hm
  | zero => simp
  | add y y' _ _ ih ih' => rw [add_mul]; exact Submodule.add_mem _ ih ih'

omit [GradedAlgebra 𝒜] in
/-- An odd homogeneous element commutes with the odd part up to a sign. -/
private theorem odd_mul_oddPart {q : ℕ} {y t : A} (ht : t ∈ 𝒜 (2 * q + 1))
    (hy : y ∈ oddPart 𝒜) : t * y = -(y * t) := by
  induction hy using Submodule.iSup_induction' with
  | mem e y hy =>
      have h := IsStrictlyGradedComm.graded_comm (𝒜 := 𝒜) ht hy
      have hodd : Odd ((2 * q + 1) * (2 * e + 1)) := ⟨2 * q * e + q + e, by ring⟩
      rw [h, hodd.neg_one_pow, neg_smul, one_smul]
  | zero => simp
  | add a b _ _ iha ihb => rw [mul_add, add_mul, iha, ihb, neg_add]

omit [GradedAlgebra 𝒜] in
/-- An odd homogeneous element squares to zero. -/
private theorem odd_mul_self_eq_zero {q : ℕ} {t : A} (ht : t ∈ 𝒜 (2 * q + 1)) : t * t = 0 := by
  rw [← pow_two]
  exact IsStrictlyGradedComm.odd_sq_zero (𝒜 := 𝒜) (d := q) ht

/-- In a graded divided power algebra the divided powers above the first of a product of an
element of the odd part with an odd homogeneous element vanish. -/
public theorem dpow_odd_mul_odd_eq_zero (γ : DividedPowerStructure 𝒜) {n q : ℕ} {y t : A}
    (hn : 1 < n) (hy : y ∈ oddPart 𝒜) (ht : t ∈ 𝒜 (2 * q + 1)) :
    γ.dpow n (y * t) = 0 := by
  classical
  have key : ∀ y ∈ oddPart 𝒜, ∀ m : ℕ, 1 < m → γ.dpow m (y * t) = 0 := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem e y hy => exact fun m hm => γ.dpow_mul_odd hm hy ht
    | zero => exact fun m hm => by rw [zero_mul]; exact γ.dpow_zero_eq_zero (by omega)
    | add y y' hy hy' ih ih' =>
        intro m hm
        have hmem : y * t ∈ positiveEvenPart 𝒜 :=
          oddPart_mul_odd_mem_positiveEvenPart (q := q) hy ht
        have hmem' : y' * t ∈ positiveEvenPart 𝒜 :=
          oddPart_mul_odd_mem_positiveEvenPart (q := q) hy' ht
        rw [add_mul, γ.dpow_add hmem hmem']
        refine Finset.sum_eq_zero fun ij hij => ?_
        rw [Finset.mem_antidiagonal] at hij
        rcases Nat.lt_or_ge ij.1 2 with h1 | h1
        · rcases Nat.lt_or_ge ij.2 2 with h2 | h2
          · have hij1 : ij.1 = 1 := by omega
            have hij2 : ij.2 = 1 := by omega
            rw [hij1, hij2, γ.dpow_one hmem, γ.dpow_one hmem']
            rw [mul_assoc, ← mul_assoc t y' t, odd_mul_oddPart ht hy', neg_mul, mul_assoc,
              odd_mul_self_eq_zero ht, mul_zero, neg_zero, mul_zero]
          · rw [ih' ij.2 h2, mul_zero]
        · rw [ih ij.1 h1, zero_mul]
  exact key y hy n hn

/-- The divided powers of `x + y * t`, for `x` in the positive even part, `y` in the odd part
and `t` odd homogeneous. This is the formula defining the divided powers on an odd variable
extension, here in an arbitrary graded divided power algebra. -/
public theorem dpow_add_odd_mul (γ : DividedPowerStructure 𝒜) {n q : ℕ} {x y t : A}
    (hn : n ≠ 0) (hx : x ∈ positiveEvenPart 𝒜) (hy : y ∈ oddPart 𝒜)
    (ht : t ∈ 𝒜 (2 * q + 1)) :
    γ.dpow n (x + y * t) = γ.dpow n x + γ.dpow (n - 1) x * (y * t) := by
  classical
  have hmem : y * t ∈ positiveEvenPart 𝒜 :=
    oddPart_mul_odd_mem_positiveEvenPart (q := q) hy ht
  rw [γ.dpow_add hx hmem]
  have hsub : ({(n, 0), (n - 1, 1)} : Finset (ℕ × ℕ)) ⊆ Finset.antidiagonal n := by
    intro ij hij
    simp only [Finset.mem_insert, Finset.mem_singleton] at hij
    rcases hij with rfl | rfl <;> rw [Finset.mem_antidiagonal] <;> omega
  have hvanish : ∀ ij ∈ Finset.antidiagonal n,
      ij ∉ ({(n, 0), (n - 1, 1)} : Finset (ℕ × ℕ)) →
      γ.dpow ij.1 x * γ.dpow ij.2 (y * t) = 0 := by
    intro ij hij hnot
    rw [Finset.mem_antidiagonal] at hij
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    have h2 : 2 ≤ ij.2 := by
      by_contra hlt
      have hcases : ij.2 = 0 ∨ ij.2 = 1 := by omega
      rcases hcases with hv | hv
      · exact hnot.1 (Prod.ext (by omega) hv)
      · exact hnot.2 (Prod.ext (by omega) hv)
    rw [γ.dpow_odd_mul_odd_eq_zero (by omega) hy ht, mul_zero]
  rw [← Finset.sum_subset hsub hvanish, Finset.sum_insert (by simp),
    Finset.sum_singleton, γ.dpow_zero hmem, γ.dpow_one hmem, mul_one]

end DividedPowerStructure

section RingHomImages

variable {R : Type u} {B : Type v} {D : Type z} [CommRing R] [Ring B] [Algebra R B]
  [Ring D] [Algebra R D] (ℬ : ℕ → Submodule R B) (𝒟 : ℕ → Submodule R D)

/-- Scalar multiplication by a power of `-1` is multiplication by that power of `-1`.

This is the Koszul sign of the signed Leibniz rule read on either side:
`DividedPowers.TateResolution.IsDifferentialGradedAlgebra` writes it as the scalar action of
`(-1 : R) ^ k`, while `DividedPowers.TateResolution.eq_zero_of_twisted_graded_leibniz` writes it
in the target ring, which needs no algebra structure. -/
public theorem neg_one_pow_smul (k : ℕ) (z : D) :
    ((-1 : R) ^ k) • z = (-1 : D) ^ k * z := by
  rw [Algebra.smul_def, map_pow, map_neg, map_one]

end RingHomImages

section OddLift

open OddVariableExtension

attribute [local implicit_reducible] TwistedModule

variable {R : Type u} {B : Type v} {D : Type z} [CommRing R] [Ring B] [Algebra R B]
  [Ring D] [Algebra R D]
  (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
  (β : DividedPowerStructure ℬ)
  (𝒟 : ℕ → Submodule R D) [GradedAlgebra 𝒟] [IsStrictlyGradedComm 𝒟]
  (δ : DividedPowerStructure 𝒟)

omit [IsStrictlyGradedComm ℬ] in
/-- The two coefficients of a positive even element of an odd variable extension are
respectively positive even and odd. -/
private theorem coefficients_mem_of_mem_positiveEvenPart {d : ℕ} (hodd : Odd d)
    {x : OddVariableExtension ℬ d} (hx : x ∈ positiveEvenPart (grade ℬ d)) :
    x.fst ∈ positiveEvenPart ℬ ∧ (show B from x.snd) ∈ oddPart ℬ := by
  obtain ⟨q, hq⟩ := hodd
  induction hx using Submodule.iSup_induction' with
  | mem k x hx =>
      rw [mem_grade_iff] at hx
      obtain ⟨h1, h2⟩ := hx
      refine ⟨Submodule.mem_iSup_of_mem k h1, ?_⟩
      split_ifs at h2 with hle
      · refine Submodule.mem_iSup_of_mem (k - q) ?_
        have hdeg : 2 * (k - q) + 1 = 2 * (k + 1) - d := by omega
        rw [hdeg]
        exact h2
      · have hz : (show B from x.snd) = 0 := by simpa using h2
        rw [hz]
        exact Submodule.zero_mem _
  | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  | add x y _ _ ih ih' =>
      exact ⟨Submodule.add_mem _ ih.1 ih'.1, Submodule.add_mem _ ih.2 ih'.2⟩

omit [IsStrictlyGradedComm ℬ] in
/-- The mapping property of the odd variable extension of Tag 09PH, for ring homomorphisms. A
ring homomorphism out of `B⟨T⟩` which preserves degrees is determined by, and may be prescribed
by, its restriction to `B` together with the image of `T`. -/
@[stacks 09PH "mapping property"]
public theorem existsUnique_oddVariableExtension_ringHom
    (h : B →+* D) (hgrade : ∀ (m : ℕ) (b : B), b ∈ ℬ m → h b ∈ 𝒟 m)
    (d : ℕ) (hodd : Odd d) (t : D) (ht : t ∈ 𝒟 d) :
    ∃! g : OddVariableExtension ℬ d →+* D,
      (∀ b : B, g (inclusion ℬ d b) = h b) ∧
      g (generator ℬ d) = t ∧
      (∀ (m : ℕ) (x : OddVariableExtension ℬ d), x ∈ grade ℬ d m → g x ∈ 𝒟 m) := by
  classical
  have hqex : ∃ q, d = 2 * q + 1 := hodd
  obtain ⟨q, hq⟩ := hqex
  have htq : t ∈ 𝒟 (2 * q + 1) := by rw [← hq]; exact ht
  -- The twisting rule: `T` commutes past a coefficient by the grading sign.
  have hcomm : ∀ b : B, t * h b = h (signRingEquiv ℬ d b) * t := by
    intro b
    conv_lhs => rw [← DirectSum.sum_support_decompose ℬ b]
    conv_rhs => rw [← DirectSum.sum_support_decompose ℬ b]
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hmem : ((DirectSum.decompose ℬ b m : ℬ m) : B) ∈ ℬ m :=
      (DirectSum.decompose ℬ b m).property
    rw [signRingEquiv_of_mem ℬ d m hmem, neg_one_pow_smul, map_mul, map_pow, map_neg, map_one,
      IsStrictlyGradedComm.graded_comm (𝒜 := 𝒟) ht (hgrade m _ hmem), neg_one_pow_smul,
      mul_assoc]
  have hkill : ∀ b b' : B, h b * t * (h b' * t) = 0 := by
    intro b b'
    have e : h b * t * (h b' * t) = h b * (t * h b') * t := by
      simp only [mul_assoc]
    rw [e, hcomm, show h b * (h (signRingEquiv ℬ d b') * t) * t =
      h b * h (signRingEquiv ℬ d b') * (t * t) by simp only [mul_assoc],
      DividedPowerStructure.odd_mul_self_eq_zero htq, mul_zero]
  refine ⟨{ toFun := fun x => h x.fst + h (show B from x.snd) * t
            map_one' := by
              change h (1 : B) + h (0 : B) * t = 1
              simp
            map_zero' := by
              change h (0 : B) + h (0 : B) * t = 0
              simp
            map_add' := fun x y => by
              change h (x.fst + y.fst) + h ((show B from x.snd) + (show B from y.snd)) * t =
                (h x.fst + h (show B from x.snd) * t) + (h y.fst + h (show B from y.snd) * t)
              rw [map_add, map_add, add_mul]
              abel
            map_mul' := fun x y => by
              have e1 : h (show B from x.snd) * t * h y.fst =
                  h (show B from x.snd) * h (signRingEquiv ℬ d y.fst) * t := by
                rw [mul_assoc, hcomm, ← mul_assoc]
              have hR : (h x.fst + h (show B from x.snd) * t) *
                    (h y.fst + h (show B from y.snd) * t) =
                  h x.fst * h y.fst + h x.fst * (h (show B from y.snd) * t) +
                    h (show B from x.snd) * h (signRingEquiv ℬ d y.fst) * t := by
                have expand : (h x.fst + h (show B from x.snd) * t) *
                    (h y.fst + h (show B from y.snd) * t) =
                    h x.fst * h y.fst + h x.fst * (h (show B from y.snd) * t) +
                      h (show B from x.snd) * t * h y.fst +
                      h (show B from x.snd) * t * (h (show B from y.snd) * t) := by
                  noncomm_ring
                rw [expand, e1, hkill, add_zero]
              change h (x.fst * y.fst) +
                  h (x.fst * (show B from y.snd) +
                    (show B from x.snd) * signRingEquiv ℬ d y.fst) * t = _
              rw [hR, map_add, map_mul, map_mul, map_mul]
              noncomm_ring }, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro b
    change h b + h (0 : B) * t = h b
    simp
  · change h (0 : B) + h (1 : B) * t = t
    simp
  · intro m x hx
    rw [mem_grade_iff] at hx
    obtain ⟨h1, h2⟩ := hx
    change h x.fst + h (show B from x.snd) * t ∈ 𝒟 m
    refine Submodule.add_mem _ (hgrade m _ h1) ?_
    split_ifs at h2 with hle
    · have hmul : h (show B from x.snd) * t ∈ 𝒟 (m - d + d) :=
        SetLike.GradedMul.mul_mem (hgrade (m - d) _ h2) ht
      rwa [Nat.sub_add_cancel hle] at hmul
    · have hz : (show B from x.snd) = 0 := by simpa using h2
      rw [hz, map_zero, zero_mul]
      exact Submodule.zero_mem _
  · intro g hg
    ext x
    conv_lhs => rw [← inclusion_fst_add_inclusion_snd_mul_generator ℬ d x]
    rw [map_add, map_mul, hg.1, hg.1, hg.2.1]
    rfl


/-- A degree-preserving ring homomorphism out of an odd variable extension which restricts to a
divided-power compatible map on the coefficients is itself compatible with divided powers. -/
@[stacks 09PH "mapping property"]
public theorem oddVariableExtension_ringHom_dpow
    (h : B →+* D) (hgrade : ∀ (m : ℕ) (b : B), b ∈ ℬ m → h b ∈ 𝒟 m)
    (hdpow : ∀ (n : ℕ) (b : B), b ∈ positiveEvenPart ℬ → δ.dpow n (h b) = h (β.dpow n b))
    (d : ℕ) (hd : 0 < d) (hodd : Odd d) (t : D) (ht : t ∈ 𝒟 d)
    (g : OddVariableExtension ℬ d →+* D)
    (hg1 : ∀ b : B, g (inclusion ℬ d b) = h b) (hg2 : g (generator ℬ d) = t)
    (n : ℕ) (x : OddVariableExtension ℬ d) (hx : x ∈ positiveEvenPart (grade ℬ d)) :
    δ.dpow n (g x) = g ((oddVariableDividedPowerStructure ℬ β d hd hodd).dpow n x) := by
  classical
  have hqex : ∃ q, d = 2 * q + 1 := hodd
  obtain ⟨q, hq⟩ := hqex
  have htq : t ∈ 𝒟 (2 * q + 1) := by rw [← hq]; exact ht
  have hgval : ∀ y : OddVariableExtension ℬ d,
      g y = h y.fst + h (show B from y.snd) * t := by
    intro y
    conv_lhs => rw [← inclusion_fst_add_inclusion_snd_mul_generator ℬ d y]
    rw [map_add, map_mul, hg1, hg1, hg2]
  obtain ⟨hfst, hsnd⟩ := coefficients_mem_of_mem_positiveEvenPart ℬ (d := d) ⟨q, hq⟩ hx
  have hhfst : h x.fst ∈ positiveEvenPart 𝒟 :=
    ringHom_mem_positiveEvenPart ℬ 𝒟 h hgrade hfst
  have hhsnd : h (show B from x.snd) ∈ oddPart 𝒟 :=
    ringHom_mem_oddPart ℬ 𝒟 h hgrade hsnd
  have hgx : h x.fst + h (show B from x.snd) * t ∈ positiveEvenPart 𝒟 :=
    Submodule.add_mem _ hhfst
      (DividedPowerStructure.oddPart_mul_odd_mem_positiveEvenPart (q := q) hhsnd htq)
  by_cases hn : n = 0
  · subst n
    rw [hgval x, δ.dpow_zero hgx,
      (oddVariableDividedPowerStructure ℬ β d hd hodd).dpow_zero hx, map_one]
  · have hform := oddVariableDividedPowerStructure_dpow ℬ β d hd hodd n hn
      x.fst (show B from x.snd) hfst hsnd
    rw [inclusion_fst_add_inclusion_snd_mul_generator ℬ d x] at hform
    rw [hgval x, hform, map_add, map_mul, hg1, hg1, hg2,
      DividedPowerStructure.dpow_add_odd_mul δ hn hhfst hhsnd htq,
      hdpow n x.fst hfst, map_mul, hdpow (n - 1) x.fst hfst, mul_assoc]

end OddLift

section EvenLift

open EvenVariableAlgebra

variable {R : Type u} {B : Type v} {D : Type z} [CommRing R] [Ring B] [Algebra R B]
  [Ring D] [Algebra R D]
  (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
  (𝒟 : ℕ → Submodule R D) [GradedAlgebra 𝒟] [IsStrictlyGradedComm 𝒟]
  (δ : DividedPowerStructure 𝒟)

/-- An element of even degree is central. -/
public theorem even_mem_grade_commute {e : ℕ} {x : D} (hx : x ∈ 𝒟 (2 * e)) (z : D) :
    x * z = z * x := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒟 z]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒟 z]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hmem : ((DirectSum.decompose 𝒟 z m : 𝒟 m) : D) ∈ 𝒟 m :=
    (DirectSum.decompose 𝒟 z m).property
  rw [IsStrictlyGradedComm.graded_comm (𝒜 := 𝒟) hx hmem, neg_one_pow_smul,
    show (-1 : D) ^ (2 * e * m) = 1 by
      rw [show 2 * e * m = 2 * (e * m) by ring, pow_mul]; simp, one_mul]

/-- A divided power of an element of even degree is homogeneous of the multiplied degree. -/
public theorem dpow_mem_grade_mul_of_mem_positiveEvenPart (n e : ℕ) {x : D}
    (hx : x ∈ positiveEvenPart 𝒟) (hxe : x ∈ 𝒟 (2 * e)) :
    δ.dpow n x ∈ 𝒟 (n * (2 * e)) := by
  by_cases hn : n = 0
  · subst n
    rw [δ.dpow_zero hx, Nat.zero_mul]
    exact SetLike.one_mem_graded 𝒟
  · have h := δ.dpow_mem_grade hn hx hxe
    rwa [show 2 * n * e = n * (2 * e) by ring] at h

omit [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ] in
/-- The mapping property of the even variable algebra of Tag 09PI, for ring homomorphisms. A
ring homomorphism out of `B⟨T⟩` is determined by, and may be prescribed by, its restriction to
`B` together with a choice of images for the divided powers of `T`, which must be the divided
powers of a single element of degree `d`. -/
@[stacks 09PI "mapping property"]
public theorem existsUnique_evenVariableAlgebra_ringHom
    (h : B →+* D) (hgrade : ∀ (m : ℕ) (b : B), b ∈ ℬ m → h b ∈ 𝒟 m)
    (d : ℕ) (hd : 0 < d) (heven : Even d) (t : D) (ht : t ∈ 𝒟 d) :
    ∃! g : EvenVariableAlgebra B →+* D,
      (∀ b : B, g (coeffEmbedding b) = h b) ∧
      (∀ n : ℕ, g (monomial n (1 : B)) = δ.dpow n t) ∧
      (∀ (m : ℕ) (x : EvenVariableAlgebra B),
        x ∈ EvenVariableAlgebra.grade ℬ d m → g x ∈ 𝒟 m) := by
  classical
  obtain ⟨e, he⟩ : ∃ e, d = 2 * e := by obtain ⟨k, hk⟩ := heven; exact ⟨k, by omega⟩
  have hte : t ∈ 𝒟 (2 * e) := by rw [← he]; exact ht
  have htpos : t ∈ positiveEvenPart 𝒟 := by
    refine Submodule.mem_iSup_of_mem (e - 1) ?_
    have hdeg : 2 * (e - 1 + 1) = 2 * e := by omega
    rw [hdeg]
    exact hte
  have hdpowdeg : ∀ n : ℕ, δ.dpow n t ∈ 𝒟 (n * d) := fun n => by
    rw [he]; exact dpow_mem_grade_mul_of_mem_positiveEvenPart 𝒟 δ n e htpos hte
  have hcentral : ∀ (n : ℕ) (z : D), δ.dpow n t * z = z * δ.dpow n t := fun n z =>
    even_mem_grade_commute 𝒟 (e := n * e)
      (by rw [show 2 * (n * e) = n * (2 * e) by ring]
          exact dpow_mem_grade_mul_of_mem_positiveEvenPart 𝒟 δ n e htpos hte) z
  -- The underlying additive map, summing the prescribed values over the coefficients.
  set G : EvenVariableAlgebra B →+ D :=
    { toFun := fun x => x.coeff.sum fun n b => h b * δ.dpow n t
      map_zero' := by simp [Finsupp.sum]
      map_add' := fun x y => by
        change (x.coeff + y.coeff).sum _ = x.coeff.sum _ + y.coeff.sum _
        exact Finsupp.sum_add_index' (by simp) (by intro a b₁ b₂; rw [map_add, add_mul]) }
  have hGmon : ∀ (n : ℕ) (b : B), G (monomial n b) = h b * δ.dpow n t := by
    intro n b
    change (Finsupp.single n b).sum (fun n b => h b * δ.dpow n t) = _
    rw [Finsupp.sum_single_index (by simp)]
  have hGcoeff : ∀ b : B, G (coeffEmbedding b) = h b := fun b => by
    rw [coeffEmbedding_apply, hGmon, δ.dpow_zero htpos, mul_one]
  have hGvar : ∀ n : ℕ, G (monomial n (1 : B)) = δ.dpow n t := fun n => by
    rw [hGmon, map_one, one_mul]
  have hGmul : ∀ x y : EvenVariableAlgebra B, G (x * y) = G x * G y := by
    have hmon : ∀ (n m : ℕ) (a b : B),
        G (monomial n a * monomial m b) = G (monomial n a) * G (monomial m b) := by
      intro n m a b
      have key : (h a * δ.dpow n t) * (h b * δ.dpow m t) =
          h (a * b) * (((n + m).choose n : D) * δ.dpow (n + m) t) := by
        calc (h a * δ.dpow n t) * (h b * δ.dpow m t)
            = h a * ((δ.dpow n t * h b) * δ.dpow m t) := by simp only [mul_assoc]
          _ = h a * ((h b * δ.dpow n t) * δ.dpow m t) := by rw [hcentral n (h b)]
          _ = (h a * h b) * (δ.dpow n t * δ.dpow m t) := by simp only [mul_assoc]
          _ = h (a * b) * (((n + m).choose n : D) * δ.dpow (n + m) t) := by
              rw [map_mul, δ.dpow_mul htpos]
      have hc : ((n + m).choose n : D) * h (a * b) = h (a * b) * ((n + m).choose n : D) :=
        (Nat.cast_commute _ _).eq
      rw [monomial_mul_monomial, hGmon, hGmon, hGmon, key, nsmul_eq_mul, map_mul,
        map_natCast, hc, mul_assoc]
    have hleft : ∀ (n : ℕ) (a : B) (y : EvenVariableAlgebra B),
        G (monomial n a * y) = G (monomial n a) * G y := by
      intro n a y
      induction y using EvenVariableAlgebra.induction_on with
      | zero => simp
      | add m b y ih =>
          have e2 : monomial n a * (monomial m b + y) =
              monomial n a * monomial m b + monomial n a * y := mul_add _ _ _
          rw [e2, map_add, map_add, ih, hmon, mul_add]
    intro x
    induction x using EvenVariableAlgebra.induction_on with
    | zero => intro y; simp
    | add n a x ih =>
        intro y
        have e1 : (monomial n a + x) * y = monomial n a * y + x * y := add_mul _ _ _
        rw [e1, map_add, map_add, ih y, add_mul, hleft]
  refine ⟨{ toFun := G
            map_one' := by
              have h1 : (1 : EvenVariableAlgebra B) = monomial 0 (1 : B) := rfl
              rw [h1, hGmon, map_one, δ.dpow_zero htpos, one_mul]
            map_zero' := G.map_zero
            map_add' := G.map_add
            map_mul' := hGmul }, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact hGcoeff
  · exact hGvar
  · intro m x hx
    rw [mem_grade_iff] at hx
    change x.coeff.sum (fun n b => h b * δ.dpow n t) ∈ 𝒟 m
    rw [Finsupp.sum]
    refine Submodule.sum_mem _ fun n hn => ?_
    rw [Finsupp.mem_support_iff] at hn
    have hcoeff := hx n
    split_ifs at hcoeff with hle
    · have hmul : h (x.coeff n) * δ.dpow n t ∈ 𝒟 (m - n * d + n * d) :=
        SetLike.GradedMul.mul_mem (hgrade (m - n * d) _ hcoeff) (hdpowdeg n)
      rwa [Nat.sub_add_cancel hle] at hmul
    · exact absurd (by simpa using hcoeff) hn
  · intro g hg
    ext x
    induction x using EvenVariableAlgebra.induction_on with
    | zero => simp
    | add n a y ih =>
        rw [map_add, map_add, ih]
        congr 1
        have hsplit : monomial n a = coeffEmbedding a * monomial n (1 : B) := by
          rw [coeffEmbedding_apply, monomial_mul_monomial]
          simp
        rw [hsplit, map_mul, hg.1, hg.2.1]
        change _ = G (coeffEmbedding a * monomial n (1 : B))
        rw [hGmul, hGcoeff, hGvar]

end EvenLift

end DividedPowers.TateResolution


end
