module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Combinatorics.Enumerative.Bell
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable.Extension
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable.Uniqueness
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable.Uniqueness

/-!
# Adjoining an odd variable: the compatible divided power structure

If `A` carries divided powers on its positive even part and `d` is odd, then `A⟨T⟩` carries a
unique compatible divided power structure, that is, a unique one for which the canonical inclusion
of `A` preserves all divided powers.  On the positive even part of the extension its operations are
determined by `γ_n (x + yT) = γ_n(x) + γ_{n-1}(x) y T`.  This file checks that the candidate
operations satisfy the divided power axioms and deduces existence and uniqueness.

## Main definitions

* `DividedPowers.TateResolution.oddVariableDividedPowerStructure` — the canonical compatible
  divided power structure on `A⟨T⟩`.

## Main results

* `DividedPowers.TateResolution.existsUnique_oddVariableDividedPowerStructure` — existence and
  uniqueness of the compatible divided power structure.
* `DividedPowers.TateResolution.oddVariableDividedPowerStructure_dpow` — its defining formula.

## References

* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

section OddDividedPowers

open OddVariableExtension
open scoped RightActions

attribute [local implicit_reducible] TwistedModule


variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

private theorem canonicalOddDpow_of_ne_zero
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) {z : OddVariableExtension Aᵢ d}
    (hz : z ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d)) {n : ℕ} (hn : n ≠ 0) :
    canonicalOddDpow Aᵢ gamma d n z =
      inclusion Aᵢ d (gamma.dpow n z.fst) +
        TrivSqZeroExt.inr (show TwistedModule Aᵢ d from
          gamma.dpow (n - 1) z.fst * (show A from z.snd)) := by
  rw [canonicalOddDpow_of_mem Aᵢ gamma d hz n]
  simp [hn]

private noncomputable def canonicalOddDividedPowerStructure
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) (hd_odd : Odd d) :
    DividedPowerStructure (OddVariableExtension.grade Aᵢ d) where
  dpow := canonicalOddDpow Aᵢ gamma d
  dpow_null := by
    intro n z hz
    simp [canonicalOddDpow, hz]
  dpow_zero := by
    intro z hz
    exact canonicalOddDpow_zero Aᵢ gamma d hz
  dpow_one := by
    intro z hz
    exact canonicalOddDpow_one Aᵢ gamma d hd_odd hz
  dpow_mem := by
    intro n z hn hz
    exact canonicalOddDpow_mem Aᵢ gamma d hd_odd hz hn
  dpow_mem_grade := by
    intro n e z hn hz he
    exact canonicalOddDpow_mem_grade Aᵢ gamma d hd_odd hz hn he
  dpow_mul := by
    intro m n z hz
    by_cases hm : m = 0
    · subst m
      simp [canonicalOddDpow_zero Aᵢ gamma d hz]
    · by_cases hn : n = 0
      · subst n
        simp [canonicalOddDpow_zero Aᵢ gamma d hz]
      · classical
        rcases (positiveEvenPart_coeff_iff Aᵢ d hd_odd z).mp hz with ⟨hx, hy⟩
        have hnm : n + m ≠ 0 := by omega
        rw [canonicalOddDpow_of_ne_zero Aᵢ gamma d hz hn,
          canonicalOddDpow_of_ne_zero Aᵢ gamma d hz hm,
          canonicalOddDpow_of_ne_zero Aᵢ gamma d hz hnm]
        apply TrivSqZeroExt.ext
        · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add,
            TrivSqZeroExt.fst_inr]
          simp only [inclusion, TrivSqZeroExt.inlHom_apply, TrivSqZeroExt.fst_inl,
            add_zero, TrivSqZeroExt.fst_natCast]
          exact gamma.dpow_mul (x := z.fst) hx
        · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add,
            TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
            TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
            TrivSqZeroExt.fst_inr, inclusion,
            TrivSqZeroExt.inlHom_apply, TwistedModule.smul_eq_mul,
            TwistedModule.op_smul]
          have hEvenM : gamma.dpow m z.fst ∈ evenPart Aᵢ :=
            positiveEvenPart_le_evenPart Aᵢ (gamma.dpow_mem hm hx)
          have hEvenNm : gamma.dpow (n + m) z.fst ∈ evenPart Aᵢ :=
            positiveEvenPart_le_evenPart Aᵢ (gamma.dpow_mem hnm hx)
          simp only [signRingEquiv_eq_self_of_evenPart Aᵢ d hEvenM,
            signRingEquiv_eq_self_of_evenPart Aᵢ d hEvenNm,
            TrivSqZeroExt.snd_natCast, zero_add, add_zero]
          have h1 := gamma.dpow_mul (m := m - 1) (n := n) (x := z.fst) hx
          have h2 := gamma.dpow_mul (m := m) (n := n - 1) (x := z.fst) hx
          have hidx1 : n + (m - 1) = n + m - 1 := by omega
          have hidx2 : (n - 1) + m = n + m - 1 := by omega
          rw [hidx1] at h1
          rw [hidx2] at h2
          have hchooseNat : Nat.choose (n + (m - 1)) n +
              Nat.choose ((n - 1) + m) (n - 1) = Nat.choose (n + m) n := by
            rw [hidx1, hidx2]
            have htop : (n + m - 1) + 1 = n + m := by omega
            have hbot : (n - 1) + 1 = n := by omega
            calc
              _ = Nat.choose (n + m - 1) (n - 1) +
                  Nat.choose (n + m - 1) n := Nat.add_comm _ _
              _ = Nat.choose ((n + m - 1) + 1) ((n - 1) + 1) :=
                by
                  simpa [Nat.succ_eq_add_one, hbot] using
                    (Nat.choose_succ_succ (n + m - 1) (n - 1)).symm
              _ = Nat.choose (n + m) n := by rw [htop, hbot]
          have hchoose : (Nat.choose (n + (m - 1)) n : A) +
              (Nat.choose ((n - 1) + m) (n - 1) : A) =
                (Nat.choose (n + m) n : A) := by
            rw [← Nat.cast_add, hchooseNat]
          have hchooseAligned : (Nat.choose (n + m - 1) n : A) +
              (Nat.choose (n + m - 1) (n - 1) : A) =
                (Nat.choose (n + (m - 1)) n : A) +
                  (Nat.choose ((n - 1) + m) (n - 1) : A) := by
            rw [hidx1, hidx2]
          have hcomm : (show A from z.snd) * gamma.dpow m z.fst =
              gamma.dpow m z.fst * (show A from z.snd) :=
            (evenPart_comm_oddPart Aᵢ (x := gamma.dpow m z.fst)
              (y := (show A from z.snd)) hEvenM hy).symm
          change gamma.dpow n z.fst *
              (gamma.dpow (m - 1) z.fst * (show A from z.snd)) +
            gamma.dpow (n - 1) z.fst * (show A from z.snd) * gamma.dpow m z.fst =
              (Nat.choose (n + m) n : A) *
                (gamma.dpow (n + m - 1) z.fst * (show A from z.snd)) +
              0 * gamma.dpow (n + m) z.fst
          simp only [zero_mul, add_zero]
          calc
            gamma.dpow n z.fst * (gamma.dpow (m - 1) z.fst * (show A from z.snd)) +
                gamma.dpow (n - 1) z.fst * (show A from z.snd) * gamma.dpow m z.fst =
                (gamma.dpow n z.fst * gamma.dpow (m - 1) z.fst) * (show A from z.snd) +
                (gamma.dpow (n - 1) z.fst * gamma.dpow m z.fst) * (show A from z.snd) := by
                  refine congrArg₂ (fun a b : A => a + b) ?_ ?_
                  · rw [mul_assoc]
                  · calc
                      gamma.dpow (n - 1) z.fst * (show A from z.snd) * gamma.dpow m z.fst =
                          gamma.dpow (n - 1) z.fst *
                            ((show A from z.snd) * gamma.dpow m z.fst) := by rw [mul_assoc]
                      _ = gamma.dpow (n - 1) z.fst *
                            (gamma.dpow m z.fst * (show A from z.snd)) := by rw [hcomm]
                      _ = (gamma.dpow (n - 1) z.fst * gamma.dpow m z.fst) *
                            (show A from z.snd) := by rw [mul_assoc]
            _ = ((Nat.choose (n + (m - 1)) n : A) +
                  (Nat.choose ((n - 1) + m) (n - 1) : A)) *
                (gamma.dpow (n + m - 1) z.fst * (show A from z.snd)) := by
                  rw [h1, h2, ← add_mul, ← add_mul, mul_assoc]
                  exact congrArg (fun c : A => c *
                    (gamma.dpow (n + m - 1) z.fst * (show A from z.snd))) hchooseAligned
            _ = (Nat.choose (n + m) n : A) *
                (gamma.dpow (n + m - 1) z.fst * (show A from z.snd)) :=
                  congrArg (fun c : A => c *
                    (gamma.dpow (n + m - 1) z.fst * (show A from z.snd))) hchoose
  dpow_mul_even := by
    intro n x y hn hx hy
    have hxy : x * y ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d) :=
      evenPart_mul_positiveEvenPart_extension_mem Aᵢ d hd_odd hx hy
    by_cases hn1 : n = 1
    · subst n
      rw [canonicalOddDpow_one Aᵢ gamma d hd_odd hxy,
        canonicalOddDpow_one Aᵢ gamma d hd_odd hy, pow_one]
    · have hnsub : n - 1 ≠ 0 := by omega
      rcases (evenPart_coeff_iff Aᵢ d hd_odd x).mp hx with ⟨ha, hb⟩
      rcases (positiveEvenPart_coeff_iff Aᵢ d hd_odd y).mp hy with ⟨hc, he⟩
      have hEvenC : y.fst ∈ evenPart Aᵢ :=
        positiveEvenPart_le_evenPart Aᵢ hc
      have hsignA : signRingEquiv Aᵢ d x.fst = x.fst :=
        signRingEquiv_eq_self_of_evenPart Aᵢ d ha
      have hsignC : signRingEquiv Aᵢ d y.fst = y.fst :=
        signRingEquiv_eq_self_of_evenPart Aᵢ d hEvenC
      have hxySnd : (show A from (x * y).snd) =
          x.fst * (show A from y.snd) + (show A from x.snd) * y.fst := by
        rw [OddVariableExtension.mul_snd, hsignC]
      have hsmul : x.snd <• x.fst = x.fst •> x.snd := by
        change (show A from x.snd) * signRingEquiv Aᵢ d x.fst =
          x.fst * (show A from x.snd)
        rw [hsignA]
        exact (evenPart_comm_oddPart Aᵢ ha hb).symm
      have hpowSnd : (x ^ n).snd = n • (x.snd <• x.fst ^ n.pred) :=
        TrivSqZeroExt.snd_pow_of_smul_comm' x n hsmul
      rw [canonicalOddDpow_of_ne_zero Aᵢ gamma d hxy hn,
        canonicalOddDpow_of_ne_zero Aᵢ gamma d hy hn, hxySnd]
      apply TrivSqZeroExt.ext
      · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.fst_inr, inclusion, TrivSqZeroExt.inlHom_apply,
          TrivSqZeroExt.fst_inl, add_zero]
        exact gamma.dpow_mul_even hn ha hc
      · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
          TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
          TrivSqZeroExt.fst_inr, inclusion,
          TrivSqZeroExt.inlHom_apply, TwistedModule.smul_eq_mul,
          TwistedModule.op_smul]
        have hGammaPos : gamma.dpow n y.fst ∈ positiveEvenPart Aᵢ :=
          gamma.dpow_mem hn hc
        have hsignGamma : signRingEquiv Aᵢ d (gamma.dpow n y.fst) =
            gamma.dpow n y.fst :=
          signRingEquiv_eq_self_of_evenPart Aᵢ d
            (positiveEvenPart_le_evenPart Aᵢ hGammaPos)
        rw [hpowSnd]
        simp only [TrivSqZeroExt.fst_pow, hsignGamma, zero_add, add_zero,
          TwistedModule.op_smul, map_pow, hsignA]
        have hExtract := gamma.dpow_mul_even hnsub ha hc
        have hRec : y.fst * gamma.dpow (n - 1) y.fst =
            (n : A) * gamma.dpow n y.fst := by
          have h := gamma.dpow_mul (m := n - 1) (n := 1) (x := y.fst) hc
          simpa [gamma.dpow_one hc, Nat.choose_one_right,
            show 1 + (n - 1) = n by omega] using h
        have hGPos : gamma.dpow (n - 1) y.fst ∈ positiveEvenPart Aᵢ :=
          gamma.dpow_mem hnsub hc
        have hGEven : gamma.dpow (n - 1) y.fst ∈ evenPart Aᵢ :=
          positiveEvenPart_le_evenPart Aᵢ hGPos
        have hAPredEven : x.fst ^ (n - 1) ∈ evenPart Aᵢ :=
          evenPart_pow_mem Aᵢ ha (n - 1)
        have hcommGA : gamma.dpow (n - 1) y.fst * x.fst =
            x.fst * gamma.dpow (n - 1) y.fst :=
          evenPart_mul_comm Aᵢ hGEven x.fst
        have hcommGB : gamma.dpow (n - 1) y.fst * (show A from x.snd) =
            (show A from x.snd) * gamma.dpow (n - 1) y.fst :=
          evenPart_comm_oddPart Aᵢ hGEven hb
        have hcommGC : gamma.dpow (n - 1) y.fst * y.fst =
            y.fst * gamma.dpow (n - 1) y.fst :=
          evenPart_mul_comm Aᵢ hGEven y.fst
        have hcommAB : x.fst ^ (n - 1) * (show A from x.snd) =
            (show A from x.snd) * x.fst ^ (n - 1) :=
          evenPart_comm_oddPart Aᵢ hAPredEven hb
        have hpow : x.fst ^ (n - 1) * x.fst = x.fst ^ n := by
          calc
            x.fst ^ (n - 1) * x.fst = x.fst ^ ((n - 1) + 1) := (pow_succ _ _).symm
            _ = x.fst ^ n := by congr 1; omega
        simp only [TrivSqZeroExt.fst_mul]
        rw [hExtract]
        rw [← Nat.cast_smul_eq_nsmul A n _]
        simp only [TwistedModule.smul_eq_mul]
        change x.fst ^ (n - 1) * gamma.dpow (n - 1) y.fst *
            (x.fst * (show A from y.snd) + (show A from x.snd) * y.fst) =
          x.fst ^ n * (gamma.dpow (n - 1) y.fst * (show A from y.snd)) +
            (n : A) * ((show A from x.snd) * x.fst ^ (n - 1)) *
              gamma.dpow n y.fst
        exact (calc
          x.fst ^ (n - 1) * gamma.dpow (n - 1) y.fst *
              (x.fst * (show A from y.snd) + (show A from x.snd) * y.fst) =
            x.fst ^ n * (gamma.dpow (n - 1) y.fst * (show A from y.snd)) +
              (n : A) * ((show A from x.snd) * x.fst ^ (n - 1)) *
                gamma.dpow n y.fst := by
                  rw [mul_add]
                  apply congrArg₂ (fun u v : A => u + v)
                  · calc
                      x.fst ^ (n - 1) * gamma.dpow (n - 1) y.fst *
                          (x.fst * (show A from y.snd)) =
                        x.fst ^ (n - 1) *
                          (gamma.dpow (n - 1) y.fst * x.fst) * (show A from y.snd) := by
                            simp only [mul_assoc]
                      _ = x.fst ^ (n - 1) *
                          (x.fst * gamma.dpow (n - 1) y.fst) * (show A from y.snd) := by
                            rw [hcommGA]
                      _ = x.fst ^ n *
                          (gamma.dpow (n - 1) y.fst * (show A from y.snd)) := by
                            rw [← mul_assoc, ← mul_assoc, hpow]
                  · calc
                      x.fst ^ (n - 1) * gamma.dpow (n - 1) y.fst *
                          ((show A from x.snd) * y.fst) =
                        x.fst ^ (n - 1) *
                          (gamma.dpow (n - 1) y.fst * (show A from x.snd)) * y.fst := by
                            simp only [mul_assoc]
                      _ = x.fst ^ (n - 1) *
                          ((show A from x.snd) * gamma.dpow (n - 1) y.fst) * y.fst := by
                            rw [hcommGB]
                      _ = x.fst ^ (n - 1) * (show A from x.snd) *
                          (y.fst * gamma.dpow (n - 1) y.fst) := by
                            calc
                              _ = x.fst ^ (n - 1) *
                                  ((show A from x.snd) *
                                    (gamma.dpow (n - 1) y.fst * y.fst)) := by
                                      simp only [mul_assoc]
                              _ = x.fst ^ (n - 1) *
                                  ((show A from x.snd) *
                                    (y.fst * gamma.dpow (n - 1) y.fst)) := by rw [hcommGC]
                              _ = x.fst ^ (n - 1) * (show A from x.snd) *
                                  (y.fst * gamma.dpow (n - 1) y.fst) := by
                                    simp only [mul_assoc]
                      _ = x.fst ^ (n - 1) * (show A from x.snd) *
                          ((n : A) * gamma.dpow n y.fst) := by rw [hRec]
                      _ = (n : A) *
                          ((show A from x.snd) * x.fst ^ (n - 1)) *
                            gamma.dpow n y.fst := by
                              calc
                                _ = (x.fst ^ (n - 1) * (show A from x.snd) *
                                    (n : A)) * gamma.dpow n y.fst := by
                                      simp only [mul_assoc]
                                _ = ((n : A) *
                                    (x.fst ^ (n - 1) * (show A from x.snd))) *
                                    gamma.dpow n y.fst := by
                                      rw [(Nat.cast_commute n
                                        (x.fst ^ (n - 1) * (show A from x.snd))).eq.symm]
                                _ = ((n : A) *
                                    ((show A from x.snd) * x.fst ^ (n - 1))) *
                                    gamma.dpow n y.fst := by rw [hcommAB]
        )
  dpow_mul_odd := by
    classical
    intro n e f x y hn hx hy
    have hfst : (x * y).fst = x.fst * y.fst := by
      simp [TrivSqZeroExt.fst_mul]
    have hidx : 2 * (e + f + 1) = (2 * e + 1) + (2 * f + 1) := by omega
    have hfstGrade : (x * y).fst ∈ Aᵢ (2 * (e + f + 1)) := by
      rw [hfst]
      have h := SetLike.mul_mem_graded (i := 2 * e + 1) (j := 2 * f + 1)
        ((OddVariableExtension.mem_grade_iff Aᵢ d (2 * e + 1) x).mp hx).1
        ((OddVariableExtension.mem_grade_iff Aᵢ d (2 * f + 1) y).mp hy).1
      rw [hidx]
      exact h
    have hprodGrade : x * y ∈ OddVariableExtension.grade Aᵢ d (2 * (e + f + 1)) := by
      have h := SetLike.mul_mem_graded hx hy
      rw [hidx]
      exact h
    have hprodPos : x * y ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d) :=
      Submodule.mem_iSup_of_mem (e + f) hprodGrade
    have hfstPos : (x * y).fst ∈ positiveEvenPart Aᵢ :=
      Submodule.mem_iSup_of_mem (e + f) hfstGrade
    have hgamma : gamma.dpow n (x * y).fst = 0 := by
      rw [hfst]
      exact gamma.dpow_mul_odd hn
        ((OddVariableExtension.mem_grade_iff Aᵢ d (2 * e + 1) x).mp hx).1
        ((OddVariableExtension.mem_grade_iff Aᵢ d (2 * f + 1) y).mp hy).1
    have htail : gamma.dpow (n - 1) (x * y).fst * (show A from (x * y).snd) = 0 := by
      by_cases hn2 : n = 2
      · subst n
        simp only [show 2 - 1 = 1 by decide, gamma.dpow_one hfstPos]
        exact oddHomogeneousProduct_fst_mul_snd_eq_zero Aᵢ d hd_odd hx hy
      · have hn' : 1 < n - 1 := by omega
        rw [hfst]
        rw [gamma.dpow_mul_odd hn'
          ((OddVariableExtension.mem_grade_iff Aᵢ d (2 * e + 1) x).mp hx).1
          ((OddVariableExtension.mem_grade_iff Aᵢ d (2 * f + 1) y).mp hy).1]
        simp
    rw [canonicalOddDpow_of_mem Aᵢ gamma d hprodPos n]
    simp only [ite_eq_right (Nat.ne_of_gt (by omega : 0 < n)), hgamma, htail,
      inclusion, TrivSqZeroExt.inlHom_apply, TrivSqZeroExt.inl_zero,
      TrivSqZeroExt.inr_zero]
    exact zero_add 0
  dpow_add := by
    classical
    intro n x y hx hy
    rcases (positiveEvenPart_coeff_iff Aᵢ d hd_odd x).mp hx with ⟨hxa, hxb⟩
    rcases (positiveEvenPart_coeff_iff Aᵢ d hd_odd y).mp hy with ⟨hya, hyb⟩
    have hz : x + y ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d) :=
      (positiveEvenPart (OddVariableExtension.grade Aᵢ d)).add_mem hx hy
    have hza := (positiveEvenPart_coeff_iff Aᵢ d hd_odd (x + y)).mp hz
    have hEvenDpow (j : ℕ) (a : A) (ha : a ∈ positiveEvenPart Aᵢ) :
        gamma.dpow j a ∈ evenPart Aᵢ := by
      by_cases hj : j = 0
      · subst j
        rw [gamma.dpow_zero ha]
        apply Submodule.mem_iSup_of_mem 0
        simpa using (SetLike.GradedOne.one_mem : (1 : A) ∈ Aᵢ 0)
      · exact positiveEvenPart_le_evenPart Aᵢ (gamma.dpow_mem hj ha)
    have hDfst (j : ℕ) (z : OddVariableExtension Aᵢ d)
        (hz : z ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d)) :
        (canonicalOddDpow Aᵢ gamma d j z).fst = gamma.dpow j z.fst := by
      rw [canonicalOddDpow_of_mem Aᵢ gamma d hz j]
      by_cases hj : j = 0
      · subst j
        simp [gamma.dpow_zero ((positiveEvenPart_coeff_iff Aᵢ d hd_odd z).mp hz).1]
      · simp [hj, inclusion]
    have hDsnd (j : ℕ) (z : OddVariableExtension Aᵢ d)
        (hz : z ∈ positiveEvenPart (OddVariableExtension.grade Aᵢ d)) :
        (canonicalOddDpow Aᵢ gamma d j z).snd =
          if j = 0 then 0 else
            gamma.dpow (j - 1) z.fst * (show A from z.snd) := by
      rw [canonicalOddDpow_of_mem Aᵢ gamma d hz j]
      by_cases hj : j = 0 <;> simp [hj, inclusion]
      all_goals rfl
    have hsumGamma := dpow_add_range gamma hxa hya (n := n)
    have hsumGammaPred := dpow_add_range gamma hxa hya (n := n - 1)
    by_cases hn0 : n = 0
    · subst n
      simp [canonicalOddDpow_zero Aᵢ gamma d hz,
        canonicalOddDpow_zero Aᵢ gamma d hx,
        canonicalOddDpow_zero Aᵢ gamma d hy]
    · rw [canonicalOddDpow_of_mem Aᵢ gamma d hz n]
      simp only [ite_eq_right hn0]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply TrivSqZeroExt.ext
      · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sum,
          TrivSqZeroExt.fst_mul]
        simp_rw [hDfst _ x hx, hDfst _ y hy]
        simp [inclusion, hsumGamma, TrivSqZeroExt.fst_sum,
          TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl]
      · have hcomm (j : ℕ) (a : A) (ha : a ∈ positiveEvenPart Aᵢ) :
          signRingEquiv Aᵢ d (gamma.dpow j a) = gamma.dpow j a :=
          signRingEquiv_eq_self_of_evenPart Aᵢ d (hEvenDpow j a ha)
        simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sum,
          TrivSqZeroExt.snd_mul]
        simp_rw [hDfst _ x hx, hDfst _ y hy, hDsnd _ x hx, hDsnd _ y hy]
        simp_rw [TwistedModule.smul_eq_mul Aᵢ d, TwistedModule.op_smul Aᵢ d]
        have hnpos : 0 < n := Nat.pos_of_ne_zero (by simpa using hn0)
        have hsumPred : gamma.dpow (n - 1) (x.fst + y.fst) =
            ∑ k ∈ Finset.range n, gamma.dpow k x.fst *
              gamma.dpow (n - 1 - k) y.fst := by
          simpa [Nat.sub_add_cancel hnpos] using hsumGammaPred
        have hmoveX (j : ℕ) : (show A from x.snd) * gamma.dpow j x.fst =
            gamma.dpow j x.fst * (show A from x.snd) :=
          (evenPart_comm_oddPart Aᵢ (hEvenDpow j x.fst hxa) hxb).symm
        have hmoveY (j : ℕ) : (show A from y.snd) * gamma.dpow j y.fst =
            gamma.dpow j y.fst * (show A from y.snd) :=
          (evenPart_comm_oddPart Aᵢ (hEvenDpow j y.fst hya) hyb).symm
        have hmoveXB (j : ℕ) : (show A from x.snd) * gamma.dpow j y.fst =
            gamma.dpow j y.fst * (show A from x.snd) :=
          (evenPart_comm_oddPart Aᵢ (hEvenDpow j y.fst hya) hxb).symm
        have hS1 :
            (∑ k ∈ Finset.range (n + 1),
              gamma.dpow k x.fst *
                (if n - k = 0 then 0 else
                  gamma.dpow (n - k - 1) y.fst * (show A from y.snd))) =
              (∑ k ∈ Finset.range n,
                gamma.dpow k x.fst * gamma.dpow (n - 1 - k) y.fst) *
                  (show A from y.snd) := by
          have hstep :
              (∑ k ∈ Finset.range (n + 1),
                gamma.dpow k x.fst *
                  (if n - k = 0 then 0 else
                    gamma.dpow (n - k - 1) y.fst * (show A from y.snd))) =
                ∑ k ∈ Finset.range (n + 1),
                  if k = n then 0 else
                    (gamma.dpow k x.fst * gamma.dpow (n - 1 - k) y.fst) *
                      (show A from y.snd) := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hkn : k = n
            · simp [hkn]
            · have hklt : k < n + 1 := Finset.mem_range.mp hk
              have hklt' : k < n := by omega
              have hidx : n - k - 1 = n - 1 - k := by omega
              have hne : n - k ≠ 0 := by omega
              simp [hkn, hne, hidx, mul_assoc]
          calc
            _ = ∑ k ∈ Finset.range (n + 1),
                if k = n then 0 else
                  (gamma.dpow k x.fst * gamma.dpow (n - 1 - k) y.fst) *
                    (show A from y.snd) := hstep
            _ = ∑ k ∈ Finset.range n,
                gamma.dpow k x.fst * gamma.dpow (n - 1 - k) y.fst *
                  (show A from y.snd) :=
                sum_range_drop_last n (fun k ↦
                  gamma.dpow k x.fst * gamma.dpow (n - 1 - k) y.fst *
                    (show A from y.snd))
            _ = (∑ k ∈ Finset.range n,
                gamma.dpow k x.fst * gamma.dpow (n - 1 - k) y.fst) *
                  (show A from y.snd) := by rw [Finset.sum_mul]
        have hS2 :
            (∑ k ∈ Finset.range (n + 1),
              (if k = 0 then 0 else
                gamma.dpow (k - 1) x.fst * (show A from x.snd)) *
                  signRingEquiv Aᵢ d (gamma.dpow (n - k) y.fst)) =
              (∑ k ∈ Finset.range n,
                gamma.dpow k x.fst * gamma.dpow (n - 1 - k) y.fst) *
                  (show A from x.snd) := by
          have hstep :
              (∑ k ∈ Finset.range (n + 1),
                (if k = 0 then 0 else
                  gamma.dpow (k - 1) x.fst * (show A from x.snd)) *
                    signRingEquiv Aᵢ d (gamma.dpow (n - k) y.fst)) =
                (∑ k ∈ Finset.range (n + 1),
                  if k = 0 then 0 else
                    (gamma.dpow (k - 1) x.fst *
                      gamma.dpow (n - k) y.fst) * (show A from x.snd)) := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hk0 : k = 0
            · simp [hk0]
            · have hmove2 := hmoveXB (n - k)
              simp only [hk0, ↓reduceIte]
              calc
                (gamma.dpow (k - 1) x.fst * (show A from x.snd)) *
                    signRingEquiv Aᵢ d (gamma.dpow (n - k) y.fst) =
                    (gamma.dpow (k - 1) x.fst * (show A from x.snd)) *
                      gamma.dpow (n - k) y.fst := by rw [hcomm (n - k) y.fst hya]
                _ = gamma.dpow (k - 1) x.fst *
                    ((show A from x.snd) * gamma.dpow (n - k) y.fst) := by rw [mul_assoc]
                _ = gamma.dpow (k - 1) x.fst *
                    (gamma.dpow (n - k) y.fst * (show A from x.snd)) := by rw [hmove2]
                _ = (gamma.dpow (k - 1) x.fst *
                    gamma.dpow (n - k) y.fst) * (show A from x.snd) := by rw [← mul_assoc]
          calc
            _ = (∑ k ∈ Finset.range (n + 1),
                if k = 0 then 0 else
                  (gamma.dpow (k - 1) x.fst *
                    gamma.dpow (n - k) y.fst) * (show A from x.snd)) := hstep
            _ = (∑ k ∈ Finset.range (n + 1),
                if k = 0 then 0 else
                  gamma.dpow (k - 1) x.fst * gamma.dpow (n - k) y.fst) *
                  (show A from x.snd) := by
                    rw [Finset.sum_mul]
                    simp
            _ = (∑ k ∈ Finset.range n,
                gamma.dpow k x.fst * gamma.dpow (n - 1 - k) y.fst) *
                  (show A from x.snd) :=
                    congrArg (fun s : A ↦ s * (show A from x.snd))
                      (sum_range_shift_left n
                        (fun k ↦ gamma.dpow k x.fst) (fun k ↦ gamma.dpow k y.fst))
        rw [Finset.sum_add_distrib]
        simp only [TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
          inclusion, TrivSqZeroExt.inlHom_apply, zero_add]
        have hS1' :
            (∑ k ∈ Finset.range n.succ,
              gamma.dpow k x.fst *
                (if n - k = 0 then 0 else
                  gamma.dpow (n - k - 1) y.fst * (show A from y.snd))) =
              (∑ k ∈ Finset.range n,
                gamma.dpow k x.fst * gamma.dpow (n - 1 - k) y.fst) *
                  (show A from y.snd) := by
          simpa only [Nat.add_one] using hS1
        have hS2' :
            (∑ k ∈ Finset.range n.succ,
              (if k = 0 then 0 else
                gamma.dpow (k - 1) x.fst * (show A from x.snd)) *
                  signRingEquiv Aᵢ d (gamma.dpow (n - k) y.fst)) =
              (∑ k ∈ Finset.range n,
                gamma.dpow k x.fst * gamma.dpow (n - 1 - k) y.fst) *
                  (show A from x.snd) := by
          simpa only [Nat.add_one] using hS2
        change gamma.dpow (n - 1) (x + y).fst * ((show A from x.snd) + (show A from y.snd)) =
          (∑ k ∈ Finset.range n.succ,
            gamma.dpow k x.fst *
              (if n - k = 0 then 0 else gamma.dpow (n - k - 1) y.fst * (show A from y.snd))) +
          ∑ k ∈ Finset.range n.succ,
            (if k = 0 then 0 else gamma.dpow (k - 1) x.fst * (show A from x.snd)) *
              signRingEquiv Aᵢ d (gamma.dpow (n - k) y.fst)
        rw [hS1', hS2', ← hsumPred]
        rw [TrivSqZeroExt.fst_add, mul_add, add_comm]
  dpow_dpow := by
    classical
    intro m n z hm hn hz
    rcases (positiveEvenPart_coeff_iff Aᵢ d hd_odd z).mp hz with ⟨ha, hb⟩
    have hinner : canonicalOddDpow Aᵢ gamma d m z ∈
        positiveEvenPart (OddVariableExtension.grade Aᵢ d) :=
      canonicalOddDpow_mem Aᵢ gamma d hd_odd hz hm
    have hnm : n * m ≠ 0 := by positivity
    rw [canonicalOddDpow_of_ne_zero Aᵢ gamma d hinner hn,
      canonicalOddDpow_of_ne_zero Aᵢ gamma d hz hm,
      canonicalOddDpow_of_ne_zero Aᵢ gamma d hz hnm]
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inr, inclusion, TrivSqZeroExt.inlHom_apply,
        TrivSqZeroExt.fst_inl, add_zero, TrivSqZeroExt.fst_natCast]
      exact gamma.dpow_dpow hm hn ha
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, inclusion, TrivSqZeroExt.inlHom_apply,
        TwistedModule.smul_eq_mul, TwistedModule.op_smul,
        TrivSqZeroExt.fst_natCast, TrivSqZeroExt.snd_natCast,
        zero_add, add_zero]
      by_cases hn1 : n = 1
      · subst n
        simp only [Nat.sub_self, one_mul, Nat.factorial_one, pow_one,
          Nat.cast_one,
          Nat.div_self (Nat.factorial_pos m),
          gamma.dpow_zero (gamma.dpow_mem hm ha)]
        change gamma.dpow (m - 1) z.fst * (show A from z.snd) =
          gamma.dpow (m - 1) z.fst * (show A from z.snd) +
            (0 : A) * signRingEquiv Aᵢ d (gamma.dpow m z.fst)
        rw [zero_mul, add_zero]
      · have hnm1 : n - 1 ≠ 0 := by omega
        have hiter := gamma.dpow_dpow (m := m) (n := n - 1) hm hnm1 ha
        have hpred : n - 1 + 1 = n := by omega
        have hcoef :
            ((((n * m).factorial / (n.factorial * m.factorial ^ n) : ℕ) : A) =
              (Nat.choose (n * m - 1) ((n - 1) * m) : A) *
                (((( (n - 1) * m).factorial /
                  ((n - 1).factorial * m.factorial ^ (n - 1))) : ℕ) : A)) := by
          have h := factorial_div_succ (n - 1) m hm
          simpa [hpred] using congrArg (fun c : ℕ => (c : A)) h
        have hidxMul : (n - 1) * m + (m - 1) = n * m - 1 := by
          have hn' : (n - 1) + 1 = n := by omega
          have hsplit : (n - 1) * m + m = n * m := by
            calc
              (n - 1) * m + m = (n - 1) * m + 1 * m := by simp
              _ = ((n - 1) + 1) * m := (Nat.add_mul _ _ _).symm
              _ = n * m := by rw [hn']
          omega
        have hprod := gamma.dpow_mul (n := (n - 1) * m) (m := m - 1) (x := z.fst) ha
        have hprod' : gamma.dpow ((n - 1) * m) z.fst * gamma.dpow (m - 1) z.fst =
            (Nat.choose (n * m - 1) ((n - 1) * m) : A) *
              gamma.dpow (n * m - 1) z.fst := by
          simpa only [hidxMul] using hprod
        rw [hiter]
        calc
          _ = ((((n - 1) * m).factorial /
                ((n - 1).factorial * m.factorial ^ (n - 1)) : ℕ) : A) *
                (gamma.dpow ((n - 1) * m) z.fst *
                  gamma.dpow (m - 1) z.fst) * (show A from z.snd) := by
                    simp only [mul_assoc]
          _ = ((((n - 1) * m).factorial /
                ((n - 1).factorial * m.factorial ^ (n - 1)) : ℕ) : A) *
                ((Nat.choose (n * m - 1) ((n - 1) * m) : A) *
                  gamma.dpow (n * m - 1) z.fst) * (show A from z.snd) := by
                  rw [hprod']
          _ = (Nat.choose (n * m - 1) ((n - 1) * m) : A) *
                ((((n - 1) * m).factorial /
                  ((n - 1).factorial * m.factorial ^ (n - 1)) : ℕ) : A) *
                  (gamma.dpow (n * m - 1) z.fst * (show A from z.snd)) := by
                    calc
                      _ = ((((n - 1) * m).factorial /
                          ((n - 1).factorial * m.factorial ^ (n - 1)) : ℕ) : A) *
                            (Nat.choose (n * m - 1) ((n - 1) * m) : A) *
                            (gamma.dpow (n * m - 1) z.fst * (show A from z.snd)) := by
                              simp only [mul_assoc]
                      _ = (Nat.choose (n * m - 1) ((n - 1) * m) : A) *
                            ((((n - 1) * m).factorial /
                              ((n - 1).factorial * m.factorial ^ (n - 1)) : ℕ) : A) *
                            (gamma.dpow (n * m - 1) z.fst * (show A from z.snd)) := by
                              rw [(Nat.cast_commute _ _).eq]
          _ = (((n * m).factorial /
                (n.factorial * m.factorial ^ n) : ℕ) : A) *
                (gamma.dpow (n * m - 1) z.fst * (show A from z.snd)) := by
                  rw [← hcoef]
          _ = (((n * m).factorial /
                (n.factorial * m.factorial ^ n) : ℕ) : A) *
                (gamma.dpow (n * m - 1) z.fst * (show A from z.snd)) +
                0 * signRingEquiv Aᵢ d (gamma.dpow (n * m) z.fst) := by simp

/-- There is a unique divided power structure on an odd-variable extension which extends the
given divided powers on the coefficient algebra. -/
@[stacks 09PH "existence and uniqueness"]
public theorem existsUnique_oddVariableDividedPowerStructure
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) (hd : 0 < d) (hd_odd : Odd d) :
    ∃! delta : DividedPowerStructure (OddVariableExtension.grade Aᵢ d),
      IsOddVariableDividedPowerExtension Aᵢ d gamma delta := by
  -- `hd` is subsumed by `hd_odd`, which already gives `d ≠ 0`; it is named in the
  -- Stacks statement, so it is kept and referenced here rather than renamed away.
  have := hd
  refine ⟨canonicalOddDividedPowerStructure Aᵢ gamma d hd_odd, ?_, ?_⟩
  · intro n x hx
    exact canonicalOddDpow_inclusion Aᵢ gamma d hx n
  · intro delta hdelta
    exact oddVariableDividedPowerStructure_unique Aᵢ gamma d hd_odd
      hdelta (by
        intro n x hx
        exact canonicalOddDpow_inclusion Aᵢ gamma d hx n)

/-- The canonical divided power structure on an odd-variable extension. -/
public noncomputable def oddVariableDividedPowerStructure
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) (hd : 0 < d) (hd_odd : Odd d) :
    DividedPowerStructure (OddVariableExtension.grade Aᵢ d) :=
  (existsUnique_oddVariableDividedPowerStructure Aᵢ gamma d hd hd_odd).choose

/-- The canonical divided power structure extends the divided powers on the coefficient
algebra. -/
public theorem oddVariableDividedPowerStructure_isExtension
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) (hd : 0 < d) (hd_odd : Odd d) :
    IsOddVariableDividedPowerExtension Aᵢ d gamma
      (oddVariableDividedPowerStructure Aᵢ gamma d hd hd_odd) :=
  (existsUnique_oddVariableDividedPowerStructure Aᵢ gamma d hd hd_odd).choose_spec.1

/-- For `x` in the positive even part and `y` in the odd part, the `n`th divided power of
`x + yT` is `gamma_n(x) + gamma_(n - 1)(x)yT`. -/
@[stacks 09PH "divided power formula"]
public theorem oddVariableDividedPowerStructure_dpow
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (gamma : DividedPowerStructure Aᵢ) (d : ℕ) (hd : 0 < d) (hd_odd : Odd d)
    (n : ℕ) (hn : n ≠ 0) (x y : A) (hx : x ∈ positiveEvenPart Aᵢ)
    (hy : y ∈ oddPart Aᵢ) :
    (oddVariableDividedPowerStructure Aᵢ gamma d hd hd_odd).dpow n
        (inclusion Aᵢ d x + inclusion Aᵢ d y * generator Aᵢ d) =
      inclusion Aᵢ d (gamma.dpow n x) +
        inclusion Aᵢ d (gamma.dpow (n - 1) x * y) * generator Aᵢ d :=
  dpow_inclusion_add_oddFormula Aᵢ gamma d hd_odd
    (oddVariableDividedPowerStructure Aᵢ gamma d hd hd_odd)
    (oddVariableDividedPowerStructure_isExtension Aᵢ gamma d hd hd_odd)
    n hn x y hx hy

end OddDividedPowers

end DividedPowers.TateResolution
