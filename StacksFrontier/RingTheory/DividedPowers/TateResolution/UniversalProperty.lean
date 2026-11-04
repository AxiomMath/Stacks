module

public import Mathlib.Tactic.NoncommRing
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable

/-!
# Mapping out of an odd-variable divided-power extension

A graded ring homomorphism out of the coefficient algebra, together with a choice of image for
the adjoined variable, extends uniquely to the odd-variable extension `A⟨T⟩`. This file
provides that extension together with the graded-commutativity facts it rests on.

Everything here is stated for ring homomorphisms rather than algebra homomorphisms. This is
deliberate: the consumer is the mapping property of an iterated divided-power polynomial
algebra, whose intermediate finite stages carry an `R`-algebra structure supplied
existentially, which therefore cannot be assumed compatible with the ambient one. Signs are
handled through `ringHom_neg_one_pow_smul`, which observes that scaling by a power of `-1` is
negation or the identity and so is preserved by any ring homomorphism.

## Main definitions

* `DividedPowers.TateResolution.oddLift` — the ring homomorphism out of an odd-variable
  extension determined by its restriction to the coefficients and its value on the variable.

## Main results

* `DividedPowers.TateResolution.ringHom_mem_positiveEvenPart` and
  `DividedPowers.TateResolution.ringHom_mem_oddPart` transport the positive even part and the
  odd part along a graded ring homomorphism.
* `DividedPowers.TateResolution.mul_comm_signRingEquiv` transports the Koszul commutation rule
  along a graded ring homomorphism.
* `DividedPowers.TateResolution.oddLift_unique` shows the extension is determined by those two
  pieces of data.
* `DividedPowers.TateResolution.dpow_oddPart_mul_eq_zero` and
  `DividedPowers.TateResolution.dpow_add_eq_zero` are the vanishing facts for divided powers of
  products of odd elements.
* `DividedPowers.TateResolution.oddLift_mem_grade` shows the extension is graded.
* `DividedPowers.TateResolution.eq_zero_of_mem_odd_grade_of_mem_positiveEvenPart` and
  `DividedPowers.TateResolution.dpow_zero_eq_zero` are the degeneracy facts that pin down the
  divided powers of an odd-degree variable: such a variable meets the positive even part only
  in zero, where all its positive divided powers vanish.

## References

* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w


section Transport

variable {R : Type u} {A : Type v} {D : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring D] [Algebra R D]
variable (Aᵢ : ℕ → Submodule R A) (Dᵢ : ℕ → Submodule R D)

/-- A ring homomorphism carries a graded supremum into the corresponding graded supremum. -/
private theorem ringHom_mem_iSup {ι : Type*} (S : ι → Submodule R A) (T : ι → Submodule R D)
    (g : A →+* D) (hg : ∀ (i : ι) (a : A), a ∈ S i → g a ∈ T i) {a : A} (ha : a ∈ ⨆ i, S i) :
    g a ∈ ⨆ i, T i := by
  induction ha using Submodule.iSup_induction' with
  | mem e a ha => exact Submodule.mem_iSup_of_mem e (hg _ a ha)
  | zero => simp
  | add a b _ _ ha hb => simpa [map_add] using (⨆ i, T i).add_mem ha hb

/-- A graded ring homomorphism carries the positive even part into the positive even part. -/
public theorem ringHom_mem_positiveEvenPart (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m)
    {a : A} (ha : a ∈ positiveEvenPart Aᵢ) : g a ∈ positiveEvenPart Dᵢ :=
  ringHom_mem_iSup _ _ g (fun _ a ha => hg _ a ha) ha

/-- A graded ring homomorphism carries the odd part into the odd part. -/
public theorem ringHom_mem_oddPart (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m)
    {a : A} (ha : a ∈ oddPart Aᵢ) : g a ∈ oddPart Dᵢ :=
  ringHom_mem_iSup _ _ g (fun _ a ha => hg _ a ha) ha

end Transport

/-- In a strictly graded-commutative ring, an element of odd degree squares to zero. -/
private theorem mul_self_eq_zero_of_mem_odd_aux {R : Type u} {D : Type w} [CommRing R] [Ring D]
    [Algebra R D] (Dᵢ : ℕ → Submodule R D) [IsStrictlyGradedComm Dᵢ] {d : ℕ} (hd : Odd d)
    {τ : D} (hτ : τ ∈ Dᵢ d) : τ * τ = 0 := by
  obtain ⟨e, he⟩ := hd
  have h : τ ^ 2 = 0 := IsStrictlyGradedComm.odd_sq_zero (𝒜 := Dᵢ) (d := e) (by
    rw [show 2 * e + 1 = d by omega]; exact hτ)
  rwa [pow_two] at h

section OddTarget

variable {R : Type u} {D : Type w} [CommRing R] [Ring D] [Algebra R D]
variable (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]

omit [GradedAlgebra Dᵢ] in
/-- An odd homogeneous element anticommutes with every element of the odd part. -/
public theorem mul_oddPart_comm {d : ℕ} (hd : Odd d) {τ : D} (hτ : τ ∈ Dᵢ d)
    {w : D} (hw : w ∈ oddPart Dᵢ) : τ * w = -(w * τ) := by
  induction hw using Submodule.iSup_induction' with
  | mem e w hw =>
      have h := IsStrictlyGradedComm.graded_comm (𝒜 := Dᵢ) hτ hw
      obtain ⟨q, hq⟩ := hd
      have hpar : Odd (d * (2 * e + 1)) := by
        refine ⟨2 * q * e + q + e, ?_⟩
        subst hq; ring
      rw [h, hpar.neg_one_pow, neg_one_smul]
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, ha, hb]; noncomm_ring

omit [IsStrictlyGradedComm Dᵢ] in
/-- The product of an element of the odd part with an odd homogeneous element lies in the
positive even part. -/
public theorem oddPart_mul_mem_positiveEvenPart {d : ℕ} (hd : Odd d) {τ : D} (hτ : τ ∈ Dᵢ d)
    {w : D} (hw : w ∈ oddPart Dᵢ) : w * τ ∈ positiveEvenPart Dᵢ := by
  obtain ⟨q, hq⟩ := hd
  induction hw using Submodule.iSup_induction' with
  | mem e w hw =>
      refine Submodule.mem_iSup_of_mem (e + q) ?_
      have hm : w * τ ∈ Dᵢ ((2 * e + 1) + d) := SetLike.GradedMul.mul_mem hw hτ
      rwa [show 2 * (e + q + 1) = 2 * e + 1 + d by omega]
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact (positiveEvenPart Dᵢ).add_mem ha hb

variable (δ : DividedPowerStructure Dᵢ)

/-- Higher divided powers of a sum vanish when they vanish on both summands and the summands
multiply to zero. -/
public theorem dpow_add_eq_zero {x y : D} (hx : x ∈ positiveEvenPart Dᵢ)
    (hy : y ∈ positiveEvenPart Dᵢ)
    (hxz : ∀ n, 1 < n → δ.dpow n x = 0) (hyz : ∀ n, 1 < n → δ.dpow n y = 0)
    (hxy : x * y = 0) {n : ℕ} (hn : 1 < n) : δ.dpow n (x + y) = 0 := by
  rw [δ.dpow_add hx hy]
  refine Finset.sum_eq_zero ?_
  intro ij hij
  have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rcases Nat.lt_or_ge 1 ij.1 with h1 | h1
  · rw [hxz ij.1 h1, zero_mul]
  rcases Nat.lt_or_ge 1 ij.2 with h2 | h2
  · rw [hyz ij.2 h2, mul_zero]
  have hi : ij.1 = 1 := by omega
  have hj : ij.2 = 1 := by omega
  rw [hi, hj, δ.dpow_one hx, δ.dpow_one hy, hxy]

/-- Higher divided powers vanish on the product of an element of the odd part with an odd
homogeneous element. -/
public theorem dpow_oddPart_mul_eq_zero {d : ℕ} (hd : Odd d) {τ : D} (hτ : τ ∈ Dᵢ d)
    {w : D} (hw : w ∈ oddPart Dᵢ) : ∀ n : ℕ, 1 < n → δ.dpow n (w * τ) = 0 := by
  obtain ⟨q, hq⟩ := hd
  have hτ' : τ ∈ Dᵢ (2 * q + 1) := by rwa [← hq]
  induction hw using Submodule.iSup_induction' with
  | mem e w hw => exact fun n hn => δ.dpow_mul_odd hn hw hτ'
  | zero => exact fun n hn => δ.dpow_mul_odd hn (Dᵢ (2 * 0 + 1)).zero_mem hτ'
  | add a b hamem hbmem ha hb =>
      intro n hn
      have hamem' : a ∈ oddPart Dᵢ := hamem
      have hbmem' : b ∈ oddPart Dᵢ := hbmem
      rw [add_mul]
      refine dpow_add_eq_zero Dᵢ δ
        (oddPart_mul_mem_positiveEvenPart Dᵢ ⟨q, hq⟩ hτ hamem')
        (oddPart_mul_mem_positiveEvenPart Dᵢ ⟨q, hq⟩ hτ hbmem')
        ha hb ?_ hn
      calc a * τ * (b * τ) = a * (τ * b) * τ := by noncomm_ring
        _ = a * (-(b * τ)) * τ := by
            rw [mul_oddPart_comm Dᵢ ⟨q, hq⟩ hτ hbmem']
        _ = -(a * b * (τ * τ)) := by noncomm_ring
        _ = 0 := by rw [mul_self_eq_zero_of_mem_odd_aux Dᵢ ⟨q, hq⟩ hτ, mul_zero, neg_zero]

end OddTarget

open OddVariableExtension

section OddLift

variable {R : Type u} {A : Type v} {D : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring D] [Algebra R D]

/-- A ring homomorphism commutes with scaling by a power of `-1`. -/
public theorem ringHom_neg_one_pow_smul (g : A →+* D) (k : ℕ) (a : A) :
    g (((-1 : R) ^ k) • a) = ((-1 : R) ^ k) • g a := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow]; simp
  · rw [hk.neg_one_pow]; simp

/-- The coefficient part of a product in the odd-variable extension is the product of the
coefficient parts. -/
public theorem oddExt_mul_fst (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ)
    (x y : OddVariableExtension Aᵢ d) : (x * y).fst = x.fst * y.fst :=
  congrArg Prod.fst (coefficients_mul Aᵢ d x y)

/-- The variable part of a product `x * y` in the odd-variable extension is
`x.fst * y.snd + x.snd * signRingEquiv Aᵢ d y.fst`. -/
public theorem oddExt_mul_snd (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ)
    (x y : OddVariableExtension Aᵢ d) :
    (show A from (x * y).snd) =
      x.fst * (show A from y.snd) +
        (show A from x.snd) * signRingEquiv Aᵢ d y.fst :=
  congrArg Prod.snd (coefficients_mul Aᵢ d x y)

variable (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]

omit [IsStrictlyGradedComm Aᵢ] [GradedAlgebra Dᵢ] in
/-- The Koszul commutation rule transported along a graded ring homomorphism. -/
public theorem mul_comm_signRingEquiv (d : ℕ) (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m)
    (τ : D) (hτ : τ ∈ Dᵢ d) (a : A) :
    τ * g a = g (signRingEquiv Aᵢ d a) * τ := by
  induction a using DirectSum.Decomposition.inductionOn Aᵢ with
  | zero => simp
  | @homogeneous m a =>
      have ha : (a : A) ∈ Aᵢ m := a.property
      rw [signRingEquiv_of_mem Aᵢ d m ha, ringHom_neg_one_pow_smul (R := R) g,
        IsStrictlyGradedComm.graded_comm (𝒜 := Dᵢ) hτ (hg m a ha), smul_mul_assoc]
  | add a b ha hb =>
      rw [map_add, mul_add, ha, hb, map_add, map_add, add_mul]

omit [IsStrictlyGradedComm Aᵢ] [GradedAlgebra Aᵢ] [GradedAlgebra Dᵢ] in
/-- In a strictly graded-commutative ring, an element of odd degree squares to zero. -/
public theorem mul_self_eq_zero_of_mem_odd (d : ℕ) (hd : Odd d) {τ : D} (hτ : τ ∈ Dᵢ d) :
    τ * τ = 0 :=
  mul_self_eq_zero_of_mem_odd_aux Dᵢ hd hτ

/-- The ring homomorphism out of an odd-variable extension determined by a graded ring
homomorphism on the coefficient algebra together with an image for the adjoined variable. -/
public def oddLift (d : ℕ) (hd : Odd d) (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m)
    (τ : D) (hτ : τ ∈ Dᵢ d) : OddVariableExtension Aᵢ d →+* D where
  toFun x := g x.fst + g (show A from x.snd) * τ
  map_one' := by
    change g (1 : OddVariableExtension Aᵢ d).fst
      + g (show A from (1 : OddVariableExtension Aᵢ d).snd) * τ = 1
    rw [show (1 : OddVariableExtension Aᵢ d).fst = 1 from rfl,
      show (show A from (1 : OddVariableExtension Aᵢ d).snd) = 0 from rfl]
    simp
  map_zero' := by
    change g (0 : OddVariableExtension Aᵢ d).fst
      + g (show A from (0 : OddVariableExtension Aᵢ d).snd) * τ = 0
    rw [show (0 : OddVariableExtension Aᵢ d).fst = 0 from rfl,
      show (show A from (0 : OddVariableExtension Aᵢ d).snd) = 0 from rfl]
    simp
  map_add' x y := by
    change g (x + y).fst + g (show A from (x + y).snd) * τ
      = (g x.fst + g (show A from x.snd) * τ) + (g y.fst + g (show A from y.snd) * τ)
    rw [show (x + y).fst = x.fst + y.fst from rfl,
      show (show A from (x + y).snd)
        = (show A from x.snd) + (show A from y.snd) from rfl,
      map_add, map_add, add_mul]
    noncomm_ring
  map_mul' x y := by
    change g (x * y).fst + g (show A from (x * y).snd) * τ
      = (g x.fst + g (show A from x.snd) * τ) * (g y.fst + g (show A from y.snd) * τ)
    have h3 : g (show A from x.snd) * τ * g y.fst
        = g (show A from x.snd) * g (signRingEquiv Aᵢ d y.fst) * τ := by
      rw [mul_assoc, mul_comm_signRingEquiv Aᵢ Dᵢ d g hg τ hτ, ← mul_assoc]
    have hkey : τ * (g (show A from y.snd) * τ) = 0 := by
      rw [← mul_assoc, mul_comm_signRingEquiv Aᵢ Dᵢ d g hg τ hτ, mul_assoc,
        mul_self_eq_zero_of_mem_odd Dᵢ d hd hτ, mul_zero]
    have h4 : g (show A from x.snd) * τ * (g (show A from y.snd) * τ) = 0 := by
      rw [mul_assoc, hkey, mul_zero]
    have expand : (g x.fst + g (show A from x.snd) * τ)
          * (g y.fst + g (show A from y.snd) * τ)
        = g x.fst * g y.fst + g x.fst * g (show A from y.snd) * τ
          + g (show A from x.snd) * τ * g y.fst
          + g (show A from x.snd) * τ * (g (show A from y.snd) * τ) := by
      noncomm_ring
    rw [oddExt_mul_fst Aᵢ d x y, oddExt_mul_snd Aᵢ d x y, map_mul, map_add, map_mul,
      map_mul, expand, h3, h4]
    noncomm_ring

omit [IsStrictlyGradedComm Aᵢ] [GradedAlgebra Dᵢ] in
/-- `oddLift` restricts to `g` on the coefficient algebra. -/
@[simp] public theorem oddLift_inclusion (d : ℕ) (hd : Odd d) (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m) (τ : D) (hτ : τ ∈ Dᵢ d) (a : A) :
    oddLift Aᵢ Dᵢ d hd g hg τ hτ (inclusion Aᵢ d a) = g a := by
  show g (inclusion Aᵢ d a).fst
    + g (show A from (inclusion Aᵢ d a).snd) * τ = g a
  rw [show (inclusion Aᵢ d a).fst = a from rfl,
    show (show A from (inclusion Aᵢ d a).snd) = 0 from rfl]
  simp

omit [IsStrictlyGradedComm Aᵢ] [GradedAlgebra Dᵢ] in
/-- `oddLift` sends the adjoined variable to `τ`. -/
@[simp] public theorem oddLift_generator (d : ℕ) (hd : Odd d) (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m) (τ : D) (hτ : τ ∈ Dᵢ d) :
    oddLift Aᵢ Dᵢ d hd g hg τ hτ (generator Aᵢ d) = τ := by
  show g (generator Aᵢ d).fst
    + g (show A from (generator Aᵢ d).snd) * τ = τ
  rw [show (generator Aᵢ d).fst = 0 from rfl,
    show (show A from (generator Aᵢ d).snd) = 1 from rfl]
  simp

omit [IsStrictlyGradedComm Aᵢ] [GradedAlgebra Dᵢ] in
/-- `oddLift` sends `x` to `g x.fst + g x.snd * τ`. -/
public theorem oddLift_apply (d : ℕ) (hd : Odd d) (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m) (τ : D) (hτ : τ ∈ Dᵢ d)
    (x : OddVariableExtension Aᵢ d) :
    oddLift Aᵢ Dᵢ d hd g hg τ hτ x = g x.fst + g (show A from x.snd) * τ := rfl

omit [IsStrictlyGradedComm Aᵢ] [GradedAlgebra Dᵢ] in
/-- A ring homomorphism out of an odd-variable extension is determined by its restriction to
the coefficient algebra and its value on the adjoined variable. -/
public theorem oddLift_unique (d : ℕ) (hd : Odd d) (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m) (τ : D) (hτ : τ ∈ Dᵢ d)
    (G : OddVariableExtension Aᵢ d →+* D)
    (hGincl : ∀ a : A, G (inclusion Aᵢ d a) = g a)
    (hGgen : G (generator Aᵢ d) = τ) :
    G = oddLift Aᵢ Dᵢ d hd g hg τ hτ := by
  ext x
  rw [oddLift_apply, ← hGincl, ← hGincl, ← hGgen, ← map_mul, ← map_add]
  exact congrArg G (inclusion_fst_add_inclusion_snd_mul_generator Aᵢ d x).symm

end OddLift

section Degenerate

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]

/-- An element homogeneous of two different degrees vanishes. -/
public theorem eq_zero_of_mem_grade_ne {x : A} {i j : ℕ} (hi : x ∈ Aᵢ i) (hj : x ∈ Aᵢ j)
    (hij : i ≠ j) : x = 0 := by
  calc x = (DirectSum.decompose Aᵢ x j : A) :=
        (DirectSum.decompose_of_mem_same Aᵢ hj).symm
    _ = 0 := DirectSum.decompose_of_mem_ne Aᵢ hi hij

/-- The positive even part meets an odd homogeneous piece only in zero. -/
public theorem eq_zero_of_mem_odd_grade_of_mem_positiveEvenPart {k : ℕ} {x : A}
    (hx : x ∈ Aᵢ (2 * k + 1)) (hpos : x ∈ positiveEvenPart Aᵢ) : x = 0 := by
  have key : ∀ y : A, y ∈ positiveEvenPart Aᵢ →
      (DirectSum.decompose Aᵢ y (2 * k + 1) : A) = 0 := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem e z hz => exact DirectSum.decompose_of_mem_ne Aᵢ hz (by omega)
    | zero => simp
    | add z w _ _ hz hw => simp [DirectSum.decompose_add, hz, hw]
  rw [← DirectSum.decompose_of_mem_same Aᵢ hx]
  exact key x hpos

variable [IsStrictlyGradedComm Aᵢ]

/-- Positive divided powers of zero vanish. -/
public theorem dpow_zero_eq_zero (γ : DividedPowerStructure Aᵢ) {n : ℕ} (hn : n ≠ 0) :
    γ.dpow n (0 : A) = 0 := by
  have h := γ.dpow_mul_even (n := n) (x := 0) (y := 0) hn
    (positiveEvenPart_le_evenPart Aᵢ (positiveEvenPart Aᵢ).zero_mem)
    (positiveEvenPart Aᵢ).zero_mem
  rw [mul_zero] at h
  rw [h, zero_pow hn, zero_mul]

end Degenerate

section OddGrade

variable {R : Type u} {A : Type v} {D : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring D] [Algebra R D]
variable (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]

omit [IsStrictlyGradedComm Aᵢ] in
/-- The extension of a graded ring homomorphism to an odd-variable extension is graded. -/
public theorem oddLift_mem_grade (d : ℕ) (hd : Odd d) (g : A →+* D)
    (hg : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → g a ∈ Dᵢ m) (τ : D) (hτ : τ ∈ Dᵢ d)
    (m : ℕ) (z : OddVariableExtension Aᵢ d)
    (hz : z ∈ OddVariableExtension.grade Aᵢ d m) :
    oddLift Aᵢ Dᵢ d hd g hg τ hτ z ∈ Dᵢ m := by
  rw [oddLift_apply]
  have h := (OddVariableExtension.mem_grade_iff Aᵢ d m z).mp hz
  refine (Dᵢ m).add_mem (hg m _ h.1) ?_
  rcases le_or_gt d m with hle | hlt
  · have h2 : (show A from z.snd) ∈ Aᵢ (m - d) := by simpa [hle] using h.2
    have hprod : g (show A from z.snd) * τ ∈ Dᵢ (m - d + d) :=
      SetLike.GradedMul.mul_mem (hg _ _ h2) hτ
    rwa [Nat.sub_add_cancel hle] at hprod
  · have h2 : (show A from z.snd) = 0 := by
      have hthis := h.2
      simp only [eq_false (show ¬ d ≤ m by omega), ite_false] at hthis
      exact (Submodule.mem_bot R).mp hthis
    rw [h2, map_zero, zero_mul]
    exact (Dᵢ m).zero_mem

end OddGrade

end DividedPowers.TateResolution

end
