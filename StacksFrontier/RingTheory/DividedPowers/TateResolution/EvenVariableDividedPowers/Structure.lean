module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.Vector
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.PolynomialUniversalProperty
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers.Transport
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers.Basic
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers.EvenPolynomial
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers.Transport

/-!
# Divided powers after adjoining an even variable: the structure

Let `A` be a strictly graded-commutative graded `R`-algebra with a divided power structure `γ`
on its positive even part, and let `d > 0` be even. This file proves that the transported
operation on `A⟨T⟩` vanishes in degrees above one on products of odd homogeneous elements, and
assembles the divided power structure on `A⟨T⟩` extending `γ`.

## Main definitions

* `DividedPowers.TateResolution.evenVariableDividedPowerStructure` — the divided power structure
  on `A⟨T⟩` extending `γ`.

## Main results

* `DividedPowers.TateResolution.dpow_coeffEmbedding` says the extended structure restricts to `γ`
  on the coefficient algebra, and `DividedPowers.TateResolution.dpow_monomial_one` computes
  `γₙ(T⁽ⁱ⁾)`.
* `DividedPowers.TateResolution.dpow_positivePolynomial` is the finite multinomial expansion, and
  `DividedPowers.TateResolution.dpow_coeff_add_positive` adds a positive even constant
  coefficient through the divided power binomial formula.
* `DividedPowers.TateResolution.evenVariableDividedPowerStructure_unique` says that those two
  prescriptions determine the structure.

## Implementation notes

The divided power structure is transported from the divided power polynomial algebra of Tag
07H5. The even part of `A` is a commutative subalgebra, so the even part together with the
positive even part and `γ` is a divided power ring in the sense of Tag 07GU; and the even part
of `A⟨T⟩` is the one-variable divided power polynomial algebra
`DividedPowerAlgebra A₊ (Unit →₀ A₊)` over it, by comparing the two monomial bases. The
canonical structure of Tag 07H5 therefore transports to the positive even part of `A⟨T⟩`, and
extending it by zero off that part gives the divided power operation. The `dpow_mul_odd` axiom,
which has no counterpart in Tag 07H5, is proved separately: a product of two odd homogeneous
elements of `A⟨T⟩` has square zero, so its higher divided powers vanish.

## References

* [Stacks Project, Tag 09PI](https://stacks.math.columbia.edu/tag/09PI)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

section Structure

open scoped BigOperators

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

open EvenVariableAlgebra

private theorem evenExtensionDpow_odd_monomial_product
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜)
    {r s i j n : ℕ} (hn : 1 < n) {a b : A}
    (ha : a ∈ 𝒜 (2 * r + 1)) (hb : b ∈ 𝒜 (2 * s + 1)) :
    evenExtensionDpow d hd γ n
      (EvenVariableAlgebra.monomial i a * EvenVariableAlgebra.monomial j b) = 0 := by
  have habPos : a * b ∈ positiveEvenPart 𝒜 := extensionOddProduct_mem 𝒜 ha hb
  have hcomm : b * a = -(a * b) := by
    have haodd : Odd (2 * r + 1) := ⟨r, by omega⟩
    have hbodd : Odd (2 * s + 1) := ⟨s, by omega⟩
    simpa only [(hbodd.mul haodd).neg_one_pow, neg_one_smul] using
      IsStrictlyGradedComm.graded_comm hb ha
  have hab2 : (a * b) ^ 2 = 0 := by
    have ha2 := IsStrictlyGradedComm.odd_sq_zero ha
    have hmul : (a * b) * (a * b) = -(a * a) * (b * b) := by
      calc
        (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
        _ = -(a * a) * (b * b) := by rw [hcomm]; simp only [mul_neg, neg_mul, mul_assoc]
    rw [pow_two, hmul, ← pow_two, ha2]
    simp
  by_cases hzero : i + j = 0
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    have hmul : EvenVariableAlgebra.monomial 0 a *
        EvenVariableAlgebra.monomial 0 b = coeffEmbedding (a * b) := by
      rw [EvenVariableAlgebra.monomial_mul_monomial]
      simp [coeffEmbedding_apply]
    rw [hmul, evenExtensionDpow_coeffEmbedding d hd γ n habPos]
    rw [γ.dpow_mul_odd hn ha hb]
    simp
  · let c : A := (Nat.choose (i + j) i) • (a * b)
    have hprodEven : a * b ∈ evenPart 𝒜 := by
      have h := SetLike.mul_mem_graded ha hb
      have hdeg : (2 * r + 1) + (2 * s + 1) = 2 * (r + s + 1) := by omega
      exact Submodule.mem_iSup_of_mem (r + s + 1) (hdeg ▸ h)
    have hcEven : c ∈ evenPart 𝒜 := (evenPart 𝒜).nsmul_mem hprodEven _
    have hcPos : EvenVariableAlgebra.monomial (i + j) c ∈
        positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
      exact evenPolynomial_monomial_mem_positiveEvenPart d hd (i + j) hcEven
        (by intro h; exact False.elim (hzero (by omega)))
    have hc2 : c ^ 2 = 0 := by
      dsimp [c]
      rw [nsmul_eq_mul, pow_two]
      let N : A := Nat.cast (Nat.choose (i + j) i)
      have hN : N * (a * b) * (N * (a * b)) = (N * N) * ((a * b) * (a * b)) := by
        have hcommN : (a * b) * N = N * (a * b) :=
          (Nat.cast_commute (Nat.choose (i + j) i) (a * b)).eq.symm
        calc
          (N * (a * b)) * (N * (a * b)) = N * ((a * b * N) * (a * b)) := by
            simp only [mul_assoc]
          _ = N * ((N * (a * b)) * (a * b)) := by rw [hcommN]
          _ = (N * N) * ((a * b) * (a * b)) := by simp only [mul_assoc]
      show (N * (a * b)) * (N * (a * b)) = 0
      rw [hN]
      have habMul : (a * b) * (a * b) = 0 := by simpa [pow_two] using hab2
      rw [habMul]
      simp
    have hcpow : c ^ n = 0 := by
      have hn2 : 2 ≤ n := by omega
      have hdecomp : n = 2 + (n - 2) := by omega
      rw [hdecomp, pow_add, hc2]
      simp
    rw [EvenVariableAlgebra.monomial_mul_monomial]
    show evenExtensionDpow d hd γ n
      (EvenVariableAlgebra.monomial (i + j) c) = 0
    rw [evenExtensionDpow_monomial d hd γ n (i + j)
      (Nat.pos_of_ne_zero hzero) hcEven]
    simp [hcpow]

private theorem evenExtensionDpow_zero_arg
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) {n : ℕ} (hn : n ≠ 0) :
    evenExtensionDpow d hd γ n 0 = 0 := by
  rw [evenExtensionDpow_of_mem d hd γ n (Submodule.zero_mem _)]
  show ((evenExtensionDividedPowers d hd γ).dpow n
    (0 : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
      EvenVariableAlgebra A) = 0
  rw [(evenExtensionDividedPowers d hd γ).dpow_eval_zero hn]
  simp

private theorem evenExtensionDpow_add_zero_of_products
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜)
    {u v : EvenVariableAlgebra A}
    (hu : u ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d))
    (hv : v ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d))
    (hpu : ∀ n : ℕ, 1 < n → evenExtensionDpow d hd γ n u = 0)
    (hpv : ∀ n : ℕ, 1 < n → evenExtensionDpow d hd γ n v = 0)
    (huv : u * v = 0) (n : ℕ) (hn : 1 < n) :
    evenExtensionDpow d hd γ n (u + v) = 0 := by
  let D := evenExtensionDividedPowers d hd γ
  let U : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
    ⟨u, positiveEvenPart_le_evenPart _ hu⟩
  let V : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
    ⟨v, positiveEvenPart_le_evenPart _ hv⟩
  have hU : U ∈ positiveEvenIdeal (EvenVariableAlgebra.grade 𝒜 d) := hu
  have hV : V ∈ positiveEvenIdeal (EvenVariableAlgebra.grade 𝒜 d) := hv
  have hUV : U * V = 0 := by
    apply Subtype.ext
    exact huv
  have hpu' : ∀ m : ℕ, 1 < m → D.dpow m U = 0 := by
    intro m hm
    apply Subtype.ext
    have h := hpu m hm
    rw [evenExtensionDpow_of_mem d hd γ m hu] at h
    exact h
  have hpv' : ∀ m : ℕ, 1 < m → D.dpow m V = 0 := by
    intro m hm
    apply Subtype.ext
    have h := hpv m hm
    rw [evenExtensionDpow_of_mem d hd γ m hv] at h
    exact h
  rw [evenExtensionDpow_of_mem d hd γ n ((positiveEvenPart _).add_mem hu hv)]
  show ((D.dpow n (U + V) : evenSubalgebra
    (EvenVariableAlgebra.grade 𝒜 d)) : EvenVariableAlgebra A) = 0
  exact congrArg Subtype.val
    (dividedPowers_dpow_add_eq_zero_of_mul_eq_zero D hU hV hpu' hpv' hUV n hn)

private theorem evenExtensionDpow_oddProduct_right_span
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜)
    {r s i : ℕ} {a : A} (ha : a ∈ 𝒜 (2 * r + 1))
    {y : EvenVariableAlgebra A}
    (hy : y ∈ EvenVariableAlgebra.grade 𝒜 d (2 * s + 1)) :
    ∀ n : ℕ, 1 < n → evenExtensionDpow d hd γ n
      (EvenVariableAlgebra.monomial i a * y) = 0 := by
  apply EvenVariableAlgebra.homogeneous_induction_on
    (𝒜 := 𝒜) (d := d) (m := 2 * s + 1)
    (P := fun z ↦ ∀ n : ℕ, 1 < n → evenExtensionDpow d hd γ n
      (EvenVariableAlgebra.monomial i a * z) = 0) hy
  · intro n hn
    have hn0 : n ≠ 0 := by omega
    rw [mul_zero, evenExtensionDpow_zero_arg d hd γ hn0]
  · intro j b hj hb n hn
    obtain ⟨q, hq, hbOdd⟩ := extensionOddCoeff_mem d s j hj hb
    have hpos := evenExtensionDpow_odd_monomial_product d hd γ
      (i := i) (j := j) hn ha hbOdd
    simpa [EvenVariableAlgebra.monomial_mul_monomial] using hpos
  · intro y₁ y₂ hy₁ hy₂ ih₁ ih₂ n hn
    rcases Fact.out (p := Even d) with ⟨q, hq⟩
    have hmono : EvenVariableAlgebra.monomial i a ∈
        EvenVariableAlgebra.grade 𝒜 d (2 * (r + i * q) + 1) := by
      have hdegree : (2 * r + 1) + i * d = 2 * (r + i * q) + 1 := by
        rw [hq]
        ring
      rw [← hdegree]
      exact EvenVariableAlgebra.monomial_mem_grade 𝒜 d i (2 * r + 1) ha
    have h₁pos : EvenVariableAlgebra.monomial i a * y₁ ∈
        positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) :=
      extensionOddProduct_mem (EvenVariableAlgebra.grade 𝒜 d)
        hmono hy₁
    have h₂pos : EvenVariableAlgebra.monomial i a * y₂ ∈
        positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) :=
      extensionOddProduct_mem (EvenVariableAlgebra.grade 𝒜 d)
        hmono hy₂
    have hsumPos : EvenVariableAlgebra.monomial i a * (y₁ + y₂) ∈
        positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
      simpa only [mul_add] using (positiveEvenPart _).add_mem h₁pos h₂pos
    rw [mul_add]
    apply evenExtensionDpow_add_zero_of_products d hd γ h₁pos h₂pos
    · intro m hm
      exact ih₁ m hm
    · intro m hm
      exact ih₂ m hm
    · exact extensionOddProduct_same_left_zero d hd
        hmono hy₁ hy₂
    · exact hn

private theorem evenExtensionDpow_oddProduct_zero
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜)
    {r s : ℕ} {x y : EvenVariableAlgebra A}
    (hx : x ∈ EvenVariableAlgebra.grade 𝒜 d (2 * r + 1))
    (hy : y ∈ EvenVariableAlgebra.grade 𝒜 d (2 * s + 1))
    (n : ℕ) (hn : 1 < n) :
    evenExtensionDpow d hd γ n (x * y) = 0 := by
  have hforall : ∀ m : ℕ, 1 < m → evenExtensionDpow d hd γ m (x * y) = 0 := by
    apply EvenVariableAlgebra.homogeneous_induction_on
      (𝒜 := 𝒜) (d := d) (m := 2 * r + 1)
      (P := fun z ↦ ∀ m : ℕ, 1 < m → evenExtensionDpow d hd γ m (z * y) = 0) hx
    · intro m hm
      have hm0 : m ≠ 0 := by omega
      rw [zero_mul, evenExtensionDpow_zero_arg d hd γ hm0]
    · intro i a hi ha m hm
      obtain ⟨q, hq, haOdd⟩ := extensionOddCoeff_mem d r i hi ha
      exact evenExtensionDpow_oddProduct_right_span d hd γ
        (r := r - i * q) (s := s) (i := i) haOdd hy m hm
    · intro x₁ x₂ hx₁ hx₂ ih₁ ih₂ m hm
      rw [add_mul]
      have h₁pos := extensionOddProduct_mem
        (EvenVariableAlgebra.grade 𝒜 d) hx₁ hy
      have h₂pos := extensionOddProduct_mem
        (EvenVariableAlgebra.grade 𝒜 d) hx₂ hy
      apply evenExtensionDpow_add_zero_of_products d hd γ h₁pos h₂pos
      · exact ih₁
      · exact ih₂
      · exact extensionOddProduct_same_right_zero d hd hx₁ hy hx₂
      · exact hm
  exact hforall n hn

/-- The divided-power structure on the algebra obtained by adjoining an even
variable of positive degree. -/
@[no_expose, stacks 09PI "even_variable_divided_powers"]
public noncomputable def evenVariableDividedPowerStructure
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) :
    DividedPowerStructure (EvenVariableAlgebra.grade 𝒜 d) := by
  let D := evenExtensionDividedPowers d hd γ
  refine {
    dpow := evenExtensionDpow d hd γ
    dpow_null := ?_
    dpow_zero := ?_
    dpow_one := ?_
    dpow_mem := ?_
    dpow_mem_grade := ?_
    dpow_mul := ?_
    dpow_mul_even := ?_
    dpow_mul_odd := ?_
    dpow_add := ?_
    dpow_dpow := ?_ }
  · intro n x hx
    simp [evenExtensionDpow, hx]
  · intro x hx
    rw [evenExtensionDpow_of_mem d hd γ 0 hx]
    exact congrArg Subtype.val (D.dpow_zero hx)
  · intro x hx
    rw [evenExtensionDpow_of_mem d hd γ 1 hx]
    exact congrArg Subtype.val (D.dpow_one hx)
  · intro n x hn hx
    rw [evenExtensionDpow_of_mem d hd γ n hx]
    exact D.dpow_mem hn hx
  · intro n k x hn hx hxgrade
    exact evenExtensionDpow_mem_grade d hd γ hx hxgrade
  · intro m n x hx
    rw [evenExtensionDpow_of_mem d hd γ n hx,
      evenExtensionDpow_of_mem d hd γ m hx,
      evenExtensionDpow_of_mem d hd γ (n + m) hx]
    exact congrArg Subtype.val (D.mul_dpow hx)
  · intro n x y hn hx hy
    have hprod : x * y ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) :=
      evenPart_mul_positiveEvenPart _ hx hy
    let X : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) := ⟨x, hx⟩
    let Y : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
      ⟨y, positiveEvenPart_le_evenPart _ hy⟩
    have hX : X = (⟨x, hx⟩ : evenSubalgebra
        (EvenVariableAlgebra.grade 𝒜 d)) := rfl
    have hY : Y = (⟨y, positiveEvenPart_le_evenPart _ hy⟩ :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) := rfl
    have hZ : (⟨x * y, positiveEvenPart_le_evenPart _ hprod⟩ :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) = X * Y := by
      apply Subtype.ext
      rfl
    have h := congrArg Subtype.val
      (D.dpow_mul (n := n) (a := X) (x := Y) hy)
    simpa only [evenExtensionDpow_of_mem d hd γ _ hprod,
      evenExtensionDpow_of_mem d hd γ _ hy,
      Subalgebra.coe_mul, Subalgebra.coe_pow, hX, hY, hZ] using h
  · intro n k l x y hn hx hy
    exact evenExtensionDpow_oddProduct_zero d hd γ hx hy n hn
  · intro n x y hx hy
    let X : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
      ⟨x, positiveEvenPart_le_evenPart _ hx⟩
    let Y : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
      ⟨y, positiveEvenPart_le_evenPart _ hy⟩
    have hX : (⟨x, positiveEvenPart_le_evenPart _ hx⟩ :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) = X := rfl
    have hY : (⟨y, positiveEvenPart_le_evenPart _ hy⟩ :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) = Y := rfl
    have hXY : (⟨x + y, positiveEvenPart_le_evenPart _
        ((positiveEvenPart _).add_mem hx hy)⟩ :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) = X + Y := by
      apply Subtype.ext
      rfl
    have h := congrArg Subtype.val
      ((evenExtensionDividedPowers d hd γ).dpow_add
        (n := n) (x := X) (y := Y) hx hy)
    have h' : ((evenExtensionDividedPowers d hd γ).dpow n (X + Y) :
        EvenVariableAlgebra A) =
        ∑ ij ∈ Finset.antidiagonal n,
          ((evenExtensionDividedPowers d hd γ).dpow ij.1 X : EvenVariableAlgebra A) *
          ((evenExtensionDividedPowers d hd γ).dpow ij.2 Y : EvenVariableAlgebra A) := by
      simpa only [Subalgebra.coe_add, Subalgebra.coe_mul,
        AddSubmonoidClass.coe_finsetSum] using h
    simp only [evenExtensionDpow_of_mem d hd γ _ hx,
      evenExtensionDpow_of_mem d hd γ _ hy,
      evenExtensionDpow_of_mem d hd γ n ((positiveEvenPart _).add_mem hx hy),
      hX, hY, hXY]
    exact h'
  · intro m n x hm hn hx
    let X : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
      ⟨x, positiveEvenPart_le_evenPart _ hx⟩
    let Y := (evenExtensionDividedPowers d hd γ).dpow m X
    have hYpos : (Y : EvenVariableAlgebra A) ∈
        positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) :=
      (evenExtensionDividedPowers d hd γ).dpow_mem hm hx
    have hY : (⟨(Y : EvenVariableAlgebra A),
        positiveEvenPart_le_evenPart _ hYpos⟩ :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) = Y := by
      apply Subtype.ext
      rfl
    have hXI : X ∈ positiveEvenIdeal (EvenVariableAlgebra.grade 𝒜 d) := hx
    have hcomp := congrArg Subtype.val
      (D.dpow_comp (m := n) (n := m) hm hXI)
    have hcoeff : Nat.uniformBell n m = dividedPowerMonomialCoefficient n m := by
      rw [Nat.uniformBell_eq_div n hm]
      simp [dividedPowerMonomialCoefficient,
        Nat.mul_comm]
    rw [evenExtensionDpow_of_mem d hd γ m hx]
    rw [evenExtensionDpow_of_mem d hd γ n hYpos,
      hY,
      evenExtensionDpow_of_mem d hd γ (n * m) hx]
    simp only [Subalgebra.coe_mul, SubringClass.coe_natCast, hcoeff] at hcomp ⊢
    exact hcomp

/-- The new divided powers restrict to the original structure on `A`. -/
@[stacks 09PI "even_variable_divided_powers"]
public theorem dpow_coeffEmbedding
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n : ℕ) {x : A}
    (hx : x ∈ positiveEvenPart 𝒜) :
    (evenVariableDividedPowerStructure d hd γ).dpow n (coeffEmbedding x) =
      coeffEmbedding (γ.dpow n x) := by
  simpa only [evenVariableDividedPowerStructure] using
    evenExtensionDpow_coeffEmbedding d hd γ n hx

/-- The divided powers of the formal monomial `T⁽ⁱ⁾`. -/
@[stacks 09PI "even_variable_divided_powers"]
public theorem dpow_monomial_one
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n i : ℕ) (hi : 0 < i) :
    (evenVariableDividedPowerStructure d hd γ).dpow n (monomial i (1 : A)) =
      monomial (n * i) (dividedPowerMonomialCoefficient n i • (1 : A)) := by
  simpa only [evenVariableDividedPowerStructure] using
    evenExtensionDpow_monomial_one d hd γ n i hi

/-- A series with zero constant term and even positive coefficients is a positive even element. -/
private theorem coeff_even_and_mem_positiveEvenPart
    {ℬ : ℕ → Submodule R A} (d : ℕ) [Fact (Even d)] (hd : 0 < d) (x : EvenVariableAlgebra A)
    (hzero : x.coeff 0 = 0) (heven : ∀ i : ℕ, 0 < i → x.coeff i ∈ evenPart ℬ) :
    (∀ i : ℕ, x.coeff i ∈ evenPart ℬ) ∧
      x ∈ positiveEvenPart (EvenVariableAlgebra.grade ℬ d) := by
  have hevenAll : ∀ i : ℕ, x.coeff i ∈ evenPart ℬ := by
    intro i
    by_cases hi : i = 0
    · subst i
      rw [hzero]
      exact (evenPart ℬ).zero_mem
    · exact heven i (Nat.pos_of_ne_zero hi)
  exact ⟨hevenAll, positiveEvenPart_mem_of_coeff_even d hd x hevenAll (by
    rw [hzero]
    exact (positiveEvenPart ℬ).zero_mem)⟩

/-- The multinomial expansion for a finite sum of positive-exponent terms
whose coefficients are even. -/
@[stacks 09PI "even_variable_divided_powers"]
public theorem dpow_positivePolynomial
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n : ℕ)
    (x : EvenVariableAlgebra A)
    (hzero : x.coeff 0 = 0)
    (heven : ∀ i : ℕ, 0 < i → x.coeff i ∈
      evenPart 𝒜) :
    (evenVariableDividedPowerStructure d hd γ).dpow n x =
      positivePolynomialDividedPower n x := by
  classical
  let C := evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)
  let _ : CommRing C := evenSubalgebraCommRing (EvenVariableAlgebra.grade 𝒜 d)
  let Δ := evenExtensionDividedPowers d hd γ
  obtain ⟨hevenAll, hxPos⟩ := coeff_even_and_mem_positiveEvenPart d hd x hzero heven
  let X : C := ⟨x, positiveEvenPart_le_evenPart _ hxPos⟩
  let α := ↥x.coeff.support
  have huniv : (Finset.univ : Finset α) = x.coeff.support.attach := by
    ext i
    exact ⟨fun _ => Finset.mem_attach x.coeff.support i,
      fun _ => Finset.mem_univ i⟩
  have hindexPos (i : α) : 0 < i.val := by
    have hmem : x.coeff i.val ≠ 0 := (Finsupp.mem_support_iff.mp i.property)
    by_contra hnot
    have hizero : i.val = 0 := by omega
    apply hmem
    simp [hizero, hzero]
  have hmonoPos (i : α) : monomial i.val (x.coeff i.val) ∈
      positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) :=
    evenPolynomial_monomial_mem_positiveEvenPart d hd i.val (hevenAll i.val)
      (by intro hi; rw [hi, hzero]; exact (positiveEvenPart 𝒜).zero_mem)
  let term (i : α) : positiveEvenIdeal (EvenVariableAlgebra.grade 𝒜 d) :=
    ⟨⟨monomial i.val (x.coeff i.val),
        evenPolynomial_monomial_mem_evenPart d i.val (hevenAll i.val)⟩,
      hmonoPos i⟩
  let f (i : α) : C := term i
  have hsum : (∑ i : α, f i) = X := by
    apply Subtype.ext
    show ((Finset.univ.sum (fun i : α => f i) : C) :
      EvenVariableAlgebra A) = x
    simp only [AddSubmonoidClass.coe_finsetSum]
    rw [huniv]
    simp only [f, term]
    have hattach : (∑ i ∈ x.coeff.support.attach,
        monomial i.val (x.coeff i.val)) =
        ∑ i ∈ x.coeff.support, monomial i (x.coeff i) := by
      simp
    exact hattach.trans (EvenVariableAlgebra.sum_monomial x)
  let fac (i : α) (k : ℕ) : C :=
    ⟨monomial (k * i.val)
      (dividedPowerMonomialCoefficient k i.val • x.coeff i.val ^ k),
      evenPolynomial_monomial_mem_evenPart d (k * i.val)
        ((evenPart 𝒜).nsmul_mem
          (evenPart_pow_mem 𝒜 (hevenAll i.val) k)
          (dividedPowerMonomialCoefficient k i.val))⟩
  let F (e : α → ℕ) : C := ∏ i : α, fac i (e i)
  have hfactor (i : α) (k : ℕ) :
      Δ.dpow k (f i) = fac i k := by
    apply Subtype.ext
    have hpos := hmonoPos i
    have hdp := evenExtensionDpow_monomial d hd γ k i.val
      (hindexPos i) (a := x.coeff i.val) (hevenAll i.val)
    have hinput : (f i : C) =
        ⟨monomial i.val (x.coeff i.val), positiveEvenPart_le_evenPart _ hpos⟩ := by
      apply Subtype.ext
      rfl
    rw [hinput, ← evenExtensionDpow_of_mem d hd γ k hpos]
    exact hdp
  have hsumDpow : Δ.dpow n X =
      ∑ k ∈ (Finset.univ : Finset α).sym n,
        ∏ i : α, fac i (Multiset.count i (k : Multiset α)) := by
    calc
      Δ.dpow n X = Δ.dpow n (∑ i : α, f i) := by rw [hsum]
      _ = ∑ k ∈ (Finset.univ : Finset α).sym n,
          ∏ i ∈ (Finset.univ : Finset α), Δ.dpow
            (Multiset.count i (k : Multiset α)) (f i) := by
        simpa using Δ.dpow_sum (n := n)
          (s := (Finset.univ : Finset α)) (x := f)
          (fun i hi => (term i).property)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.prod_congr rfl
        intro i hi
        exact hfactor i (Multiset.count i (k : Multiset α))
  have hreindex := sum_sym_count_eq_sum_assignments (ι := α) n F
  have hmainC : Δ.dpow n X =
      ∑ e : α → Fin (n + 1),
        if (∑ i : α, (e i).val) = n then
          F (fun i => (e i).val) else 0 := by
    rw [hsumDpow]
    exact hreindex
  have hlist (e : α → Fin (n + 1)) :
      ((F (fun i => (e i).val) : C) : EvenVariableAlgebra A) =
        ((Finset.univ : Finset α).toList.map (fun i ↦
          monomial (i.val * (e i).val)
            (dividedPowerMonomialCoefficient (e i).val i.val •
              x.coeff i.val ^ (e i).val))).prod := by
    show ((∏ i : α, fac i (e i).val : C) : EvenVariableAlgebra A) = _
    have hmapcoerce (l : List α) :
        (((l.map (fun i => fac i (e i).val)).prod : C) :
          EvenVariableAlgebra A) =
        (l.map (fun i => (fac i (e i).val : EvenVariableAlgebra A))).prod := by
      induction l with
      | nil => rfl
      | cons i l ih => simp [ih]
    have hfin : (∏ i : α, fac i (e i).val : C) =
        ((Finset.univ : Finset α).toList.map
          (fun i => fac i (e i).val)).prod := by
      have h := Finset.prod_map_toList (Finset.univ : Finset α)
        (fun i => fac i (e i).val)
      exact h.symm
    rw [hfin, hmapcoerce]
    apply congrArg List.prod
    apply List.map_congr_left
    intro i hi
    simp [fac, Nat.mul_comm]
  have hExpr :
      (((∑ e : α → Fin (n + 1),
        if (∑ i : α, (e i).val) = n then
          F (fun i => (e i).val) else 0 : C) : C) : EvenVariableAlgebra A) =
        positivePolynomialDividedPower n x := by
    unfold positivePolynomialDividedPower
    simp only [AddSubmonoidClass.coe_finsetSum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hs : (∑ i : α, (e i).val) = n
    · simp only [ite_eq_left hs]
      conv_rhs => rw [ite_eq_left hs]
      exact hlist e
    · simp only [ite_eq_right hs]
      conv_rhs => rw [ite_eq_right hs]
      rfl
  calc
    (evenVariableDividedPowerStructure d hd γ).dpow n x =
        ((Δ.dpow n X : C) : EvenVariableAlgebra A) := by
      show evenExtensionDpow d hd γ n x = _
      rw [evenExtensionDpow_of_mem d hd γ n hxPos]
    _ = positivePolynomialDividedPower n x := by
      calc
        _ = (((∑ e : α → Fin (n + 1),
          if (∑ i : α, (e i).val) = n then F (fun i => (e i).val) else 0 : C) :
            C) : EvenVariableAlgebra A) := congrArg Subtype.val hmainC
        _ = positivePolynomialDividedPower n x := hExpr

/-- Adding a positive-even constant coefficient obeys the divided-power
binomial formula. -/
@[stacks 09PI "even_variable_divided_powers"]
public theorem dpow_coeff_add_positive
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n : ℕ)
    {x₀ : A} (hx₀ : x₀ ∈ positiveEvenPart 𝒜)
    (x : EvenVariableAlgebra A)
    (hzero : x.coeff 0 = 0)
    (heven : ∀ i : ℕ, 0 < i → x.coeff i ∈
      evenPart 𝒜) :
    (evenVariableDividedPowerStructure d hd γ).dpow n (coeffEmbedding x₀ + x) =
    ∑ ij ∈ Finset.antidiagonal n,
        coeffEmbedding (γ.dpow ij.1 x₀) *
      (evenVariableDividedPowerStructure d hd γ).dpow ij.2 x := by
  have hxpos := (coeff_even_and_mem_positiveEvenPart d hd x hzero heven).2
  have hconst : coeffEmbedding x₀ ∈
      positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
    simpa [coeffEmbedding_apply] using
      evenPolynomial_monomial_mem_positiveEvenPart d hd 0
        (positiveEvenPart_le_evenPart 𝒜 hx₀) (fun _ ↦ hx₀)
  have hadd := (evenVariableDividedPowerStructure d hd γ).dpow_add
    (n := n) (x := coeffEmbedding x₀) (y := x) hconst hxpos
  rw [hadd]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [dpow_coeffEmbedding d hd γ ij.1 hx₀]

/-- Compatibility and the formal-monomial rule determine the divided-power
structure uniquely. -/
@[stacks 09PI "even_variable_divided_powers"]
public theorem evenVariableDividedPowerStructure_unique
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜)
    (δ : DividedPowerStructure (EvenVariableAlgebra.grade 𝒜 d))
    (hcompat : ∀ (n : ℕ) {x : A},
      x ∈ positiveEvenPart 𝒜 →
        δ.dpow n (coeffEmbedding x) = coeffEmbedding (γ.dpow n x))
    (hmonomial : ∀ (n i : ℕ), 0 < i →
      δ.dpow n (monomial i (1 : A)) =
        monomial (n * i) (dividedPowerMonomialCoefficient n i • (1 : A))) :
    δ = evenVariableDividedPowerStructure d hd γ := by
  classical
  let E : DividedPowerAlgebra (evenSubalgebra 𝒜)
      (Unit →₀ evenSubalgebra 𝒜) ≃+*
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
    evenDPAToExtensionEquiv (𝒜 := 𝒜) d
  let hJ : (dividedPowerPolynomialIdeal
      (positiveEvenIdeal 𝒜) Unit).map E =
      positiveEvenIdeal (EvenVariableAlgebra.grade 𝒜 d) :=
    evenDPAPositiveIdeal_map_eq d hd
  let δE := extensionDividedPowersOfStructure d δ
  let eDP := DividedPowers.equiv hJ
  let δP := eDP.symm δE
  have hback : eDP δP = δE := eDP.apply_symm_apply δE
  have hmap (n : ℕ) (z : DividedPowerAlgebra (evenSubalgebra 𝒜) (Unit →₀ evenSubalgebra 𝒜)) :
      E (δP.dpow n z) = δE.dpow n (E z) := by
    simpa [eDP, DividedPowers.equiv_apply'] using congrArg
      (fun D : DividedPowers (positiveEvenIdeal (EvenVariableAlgebra.grade 𝒜 d)) =>
        D.dpow n (E z)) hback
  have hcoeff : DividedPowers.IsDPMorphism
      (coefficientDividedPowerRing γ).dividedPowers δP
      (algebraMap (evenSubalgebra 𝒜)
        (DividedPowerAlgebra (evenSubalgebra 𝒜) (Unit →₀ evenSubalgebra 𝒜))) := by
    constructor
    · rw [Ideal.map_le_iff_le_comap]
      intro b hb
      show algebraMap (evenSubalgebra 𝒜)
        (DividedPowerAlgebra (evenSubalgebra 𝒜) (Unit →₀ evenSubalgebra 𝒜)) b ∈
        dividedPowerPolynomialIdeal (positiveEvenIdeal 𝒜) Unit
      exact Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hb)
    · intro n b hb
      apply E.injective
      rw [hmap, evenDPAToExtension_algebraMap]
      have hbpos : (b : A) ∈ positiveEvenPart 𝒜 := by
        simpa [positiveEvenIdeal] using hb
      have hcomp := hcompat n hbpos
      change δ.dpow n (coeffEmbedding (b : A)) =
        coeffEmbedding (γ.dpow n (b : A)) at hcomp
      rw [evenDPAToExtension_algebraMap]
      apply Subtype.ext
      show δ.dpow n (coeffEmbedding (b : A)) =
        coeffEmbedding (γ.dpow n (b : A))
      exact hcomp
  have hvariable : ∀ (i : Unit) (n : ℕ),
      δP.dpow n (dividedPowerPolynomialVariable
        (evenSubalgebra 𝒜) i) =
      dividedPowerPolynomialVariableMonomial
        (evenSubalgebra 𝒜) i n := by
    intro i n
    cases i
    apply E.injective
    rw [hmap,
      show E (dividedPowerPolynomialVariable (evenSubalgebra 𝒜) ()) =
        ⟨monomial 1 (1 : A), evenPolynomial_monomial_mem_evenPart d 1
          (Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜))⟩ by
        simpa [E, dividedPowerPolynomialVariable] using
          (evenDPAToExtension_dp_monomial d 1)]
    have hmonomap : E (dividedPowerPolynomialVariableMonomial
        (evenSubalgebra 𝒜) () n) =
        ⟨monomial n (1 : A), evenPolynomial_monomial_mem_evenPart d n
          (Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜))⟩ := by
      simpa [E, dividedPowerPolynomialVariableMonomial] using
        evenDPAToExtension_dp_monomial d n
    rw [hmonomap]
    apply Subtype.ext
    show δ.dpow n (monomial 1 (1 : A)) = monomial n (1 : A)
    rw [hmonomial n 1 (by omega)]
    have hcoeffOne : dividedPowerMonomialCoefficient n 1 = 1 := by
      simp only [dividedPowerMonomialCoefficient,
        Nat.factorial_one, one_pow, mul_one]
      exact Nat.div_self (Nat.factorial_pos n)
    rw [hcoeffOne]
    simp
  have huniq := dividedPowerPolynomialDividedPowers_unique
    (coefficientDividedPowerRing γ) Unit δP hvariable hcoeff
  apply DividedPowerStructure.ext
  funext n x
  by_cases hx : x ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d)
  · let X : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
      ⟨x, positiveEvenPart_le_evenPart _ hx⟩
    let z := E.symm X
    have hz : E z = X := E.apply_symm_apply X
    have hdp := congrArg (fun P : DividedPowers
        (dividedPowerPolynomialIdeal (positiveEvenIdeal 𝒜) Unit) => P.dpow n z)
      huniq
    have hleft : E (δP.dpow n z) = δ.dpow n x := by
      have hmap_val : ((E (δP.dpow n z) :
          evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
          EvenVariableAlgebra A) =
          (((δE.dpow n (E z) : evenSubalgebra
            (EvenVariableAlgebra.grade 𝒜 d)) : EvenVariableAlgebra A)) :=
        congrArg Subtype.val (hmap n z)
      rw [hz] at hmap_val
      dsimp [δE, extensionDividedPowersOfStructure,
        evenPartDividedPowers] at hmap_val
      simpa [X] using hmap_val
    have hright : E ((canonicalEvenPolynomialDividedPowers γ).dpow n z) =
        (evenVariableDividedPowerStructure d hd γ).dpow n x := by
      show E ((canonicalEvenPolynomialDividedPowers γ).dpow n z) =
        evenExtensionDpow d hd γ n x
      rw [evenExtensionDpow_of_mem d hd γ n hx]
      show E ((canonicalEvenPolynomialDividedPowers γ).dpow n z) =
        (((evenExtensionDividedPowers d hd γ).dpow n X :
          evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
          EvenVariableAlgebra A)
      rw [← hz]
      rw [evenExtensionDividedPowers, DividedPowers.ofRingEquiv_dpow_apply]
    have hdpE : ((E (δP.dpow n z) :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
        EvenVariableAlgebra A) =
        ((E ((canonicalEvenPolynomialDividedPowers γ).dpow n z) :
          evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
          EvenVariableAlgebra A) := congrArg Subtype.val (congrArg E hdp)
    rw [hleft, hright] at hdpE
    exact hdpE
  · show δ.dpow n x = evenExtensionDpow d hd γ n x
    rw [δ.dpow_null hx, evenExtensionDpow]
    simp [hx]

end Structure

end DividedPowers.TateResolution
