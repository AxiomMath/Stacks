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
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers.EvenPolynomial
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers.Basic
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers.EvenPolynomial

/-!
# Divided powers after adjoining an even variable: the transported operation

Let `A` be a strictly graded-commutative graded `R`-algebra with a divided power structure `γ`
on its positive even part, and let `d > 0` be even. This file transports the canonical
structure of Tag 07H5 to the positive even part of `A⟨T⟩`, extends it by zero to an operation
on all of `A⟨T⟩`, and computes that operation on the coefficient algebra, on the formal
monomials and on homogeneous elements. It ends with the square-zero facts about products of
two odd homogeneous elements used for the `dpow_mul_odd` axiom. All declarations here are
private auxiliaries for
`StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers.Structure`.

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

private noncomputable def evenExtensionDividedPowers (d : ℕ)
    [Fact (Even d)] (hd : 0 < d) (γ : DividedPowerStructure 𝒜) :
    DividedPowers (positiveEvenIdeal (EvenVariableAlgebra.grade 𝒜 d)) :=
  DividedPowers.ofRingEquiv (evenDPAPositiveIdeal_map_eq d hd)
    (canonicalEvenPolynomialDividedPowers γ)

private theorem evenPolynomialDPARingEquiv_symm_algebraMap (B : Type*)
    [CommRing B] (b : B) :
    (evenPolynomialDPARingEquiv B).symm
      (algebraMap B (DividedPowerAlgebra B (Unit →₀ B)) b) =
    EvenVariableAlgebra.monomial 0 b := by
  have hmap : evenPolynomialDPARingEquiv B
      (EvenVariableAlgebra.monomial 0 b) =
      algebraMap B (DividedPowerAlgebra B (Unit →₀ B)) b := by
    simpa [evenPolynomialDPARingEquiv, DividedPowerAlgebra.dp_zero] using
      evenPolynomialDPAEquiv_monomial B 0 b
  have := congrArg (evenPolynomialDPARingEquiv B).symm hmap
  simpa using this.symm

private theorem evenPolynomialDPARingEquiv_symm_dp (B : Type*) [CommRing B]
    (n : ℕ) :
    (evenPolynomialDPARingEquiv B).symm
      (DividedPowerAlgebra.dp B n (Finsupp.single () (1 : B))) =
        EvenVariableAlgebra.monomial n (1 : B) := by
  have hmap : evenPolynomialDPARingEquiv B
      (EvenVariableAlgebra.monomial n (1 : B)) =
      DividedPowerAlgebra.dp B n (Finsupp.single () (1 : B)) := by
    show evenPolynomialDPAEquiv B _ = _
    exact evenPolynomialDPAEquiv_basis B n
  have := congrArg (evenPolynomialDPARingEquiv B).symm hmap
  simpa using this.symm

private theorem evenDPAToExtension_algebraMap (d : ℕ) [Fact (Even d)]
    (b : evenSubalgebra 𝒜) :
    evenDPAToExtensionEquiv (𝒜 := 𝒜) d
      (algebraMap (evenSubalgebra 𝒜)
        (DividedPowerAlgebra (evenSubalgebra 𝒜)
          (Unit →₀ evenSubalgebra 𝒜)) b) =
      ⟨coeffEmbedding (b : A), by
        exact evenPolynomial_monomial_mem_evenPart d 0 b.property⟩ := by
  apply Subtype.ext
  let p : EvenVariableAlgebra (evenSubalgebra 𝒜) :=
    (evenPolynomialDPARingEquiv (evenSubalgebra 𝒜)).symm
      (algebraMap (evenSubalgebra 𝒜)
        (DividedPowerAlgebra (evenSubalgebra 𝒜)
          (Unit →₀ evenSubalgebra 𝒜)) b)
  show ((evenPolynomialToEvenSubalgebraEquiv d p :
    evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
    EvenVariableAlgebra A) = coeffEmbedding (b : A)
  rw [show p = EvenVariableAlgebra.monomial 0 b from
    evenPolynomialDPARingEquiv_symm_algebraMap (evenSubalgebra 𝒜) b]
  apply EvenVariableAlgebra.ext
  ext i
  rw [evenPolynomialToEvenSubalgebraEquiv_apply]
  rw [evenPolynomialToEvenSubalgebra_coeff]
  by_cases hi : i = 0 <;> simp [EvenVariableAlgebra.coeffEmbedding, hi]

private theorem evenDPAToExtension_dp_monomial (d : ℕ) [Fact (Even d)]
    (n : ℕ) :
    evenDPAToExtensionEquiv (𝒜 := 𝒜) d
      (DividedPowerAlgebra.dp (evenSubalgebra 𝒜) n
        (Finsupp.single () (1 : evenSubalgebra 𝒜))) =
      ⟨EvenVariableAlgebra.monomial n (1 : A), by
        exact evenPolynomial_monomial_mem_evenPart d n
          (Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜))⟩ := by
  apply Subtype.ext
  let p : EvenVariableAlgebra (evenSubalgebra 𝒜) :=
    (evenPolynomialDPARingEquiv (evenSubalgebra 𝒜)).symm
      (DividedPowerAlgebra.dp (evenSubalgebra 𝒜) n
        (Finsupp.single () (1 : evenSubalgebra 𝒜)))
  show ((evenPolynomialToEvenSubalgebraEquiv d p :
    evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
    EvenVariableAlgebra A) = EvenVariableAlgebra.monomial n (1 : A)
  rw [show p = EvenVariableAlgebra.monomial n (1 : evenSubalgebra 𝒜) from
    evenPolynomialDPARingEquiv_symm_dp (evenSubalgebra 𝒜) n]
  apply EvenVariableAlgebra.ext
  ext i
  rw [evenPolynomialToEvenSubalgebraEquiv_apply,
    evenPolynomialToEvenSubalgebra_coeff]
  by_cases hi : i = n <;> simp [EvenVariableAlgebra.monomial, hi]

private theorem evenExtensionDividedPowers_dpow_algebraMap
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n : ℕ)
    (b : evenSubalgebra 𝒜) (hb : b ∈ positiveEvenIdeal 𝒜) :
    (evenExtensionDividedPowers d hd γ).dpow n
        (evenDPAToExtensionEquiv (𝒜 := 𝒜) d
          (algebraMap (evenSubalgebra 𝒜)
            (DividedPowerAlgebra (evenSubalgebra 𝒜)
              (Unit →₀ evenSubalgebra 𝒜)) b)) =
      evenDPAToExtensionEquiv (𝒜 := 𝒜) d
        (algebraMap (evenSubalgebra 𝒜)
          (DividedPowerAlgebra (evenSubalgebra 𝒜)
            (Unit →₀ evenSubalgebra 𝒜))
          ((baseDividedPowers γ).dpow n b)) := by
  rw [evenExtensionDividedPowers, DividedPowers.ofRingEquiv_dpow_apply]
  have hcoeff :=
    (dividedPowerPolynomialCoefficient_isDPMorphism
      (coefficientDividedPowerRing γ) Unit).dpow_comp
      (n := n) (a := b) hb
  exact congrArg (evenDPAToExtensionEquiv (𝒜 := 𝒜) d)
    hcoeff

private theorem evenExtensionDividedPowers_dpow_variable
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n : ℕ) :
    (evenExtensionDividedPowers d hd γ).dpow n
        (evenDPAToExtensionEquiv (𝒜 := 𝒜) d
          (dividedPowerPolynomialVariable
            (evenSubalgebra 𝒜) ())) =
      evenDPAToExtensionEquiv (𝒜 := 𝒜) d
        (DividedPowerAlgebra.dp (evenSubalgebra 𝒜) n
          (Finsupp.single () (1 : evenSubalgebra 𝒜))) := by
  rw [evenExtensionDividedPowers, DividedPowers.ofRingEquiv_dpow_apply]
  exact congrArg (evenDPAToExtensionEquiv (𝒜 := 𝒜) d)
    (dividedPowerPolynomialDividedPowers_dpow_variable
      (coefficientDividedPowerRing γ) Unit () n)

private noncomputable def evenExtensionDpow
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n : ℕ) (x : EvenVariableAlgebra A) :
    EvenVariableAlgebra A := by
  classical
  by_cases hx : x ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d)
  · exact (((evenExtensionDividedPowers d hd γ).dpow n
      ⟨x, positiveEvenPart_le_evenPart _ hx⟩ :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
      EvenVariableAlgebra A)
  · exact 0

private theorem evenExtensionDpow_of_mem
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n : ℕ) {x : EvenVariableAlgebra A}
    (hx : x ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d)) :
    evenExtensionDpow d hd γ n x =
      (((evenExtensionDividedPowers d hd γ).dpow n
        ⟨x, positiveEvenPart_le_evenPart _ hx⟩ :
          evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
        EvenVariableAlgebra A) := by
  simp [evenExtensionDpow, hx]

private theorem evenExtensionDpow_mem
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) {n : ℕ} {x : EvenVariableAlgebra A}
    (hn : n ≠ 0) (hx : x ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d)) :
    evenExtensionDpow d hd γ n x ∈
      positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
  rw [evenExtensionDpow_of_mem d hd γ n hx]
  exact (evenExtensionDividedPowers d hd γ).dpow_mem hn
    (show (⟨x, positiveEvenPart_le_evenPart _ hx⟩ :
      evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) ∈
      positiveEvenIdeal (EvenVariableAlgebra.grade 𝒜 d) from hx)

private def evenPartDividedPowers
    {B : Type v} [Ring B] [Algebra R B]
    (𝒝 : ℕ → Submodule R B) [GradedAlgebra 𝒝]
    [IsStrictlyGradedComm 𝒝]
    (δ : DividedPowerStructure 𝒝) :
    DividedPowers (positiveEvenIdeal 𝒝) where
  dpow n x := ⟨δ.dpow n (x : B), by
    by_cases hx : (x : B) ∈ positiveEvenPart 𝒝
    · exact gamma_dpow_mem_evenPart δ hx
    · rw [δ.dpow_null hx]
      exact (evenSubalgebra 𝒝).zero_mem⟩
  dpow_null {n x} hx := by
    apply Subtype.ext
    exact δ.dpow_null (by simpa [positiveEvenIdeal] using hx)
  dpow_zero {x} hx := by
    apply Subtype.ext
    exact δ.dpow_zero (by simpa [positiveEvenIdeal] using hx)
  dpow_one {x} hx := by
    apply Subtype.ext
    exact δ.dpow_one (by simpa [positiveEvenIdeal] using hx)
  dpow_mem {n x} hn hx := by
    change δ.dpow n ((x : evenSubalgebra 𝒝) : B) ∈ positiveEvenPart 𝒝
    exact δ.dpow_mem hn (by simpa [positiveEvenIdeal] using hx)
  dpow_add {n x y} hx hy := by
    apply Subtype.ext
    change δ.dpow n (((x : evenSubalgebra 𝒝) : B) +
      ((y : evenSubalgebra 𝒝) : B)) = _
    simpa using δ.dpow_add
      (by simpa [positiveEvenIdeal] using hx)
      (by simpa [positiveEvenIdeal] using hy)
  dpow_mul {n a x} hx := by
    apply Subtype.ext
    change δ.dpow n ((a : B) * (x : B)) = _
    by_cases hn : n = 0
    · subst n
      have hx' : (x : B) ∈ positiveEvenPart 𝒝 := by
        simpa [positiveEvenIdeal] using hx
      have hax : (a : B) * (x : B) ∈ positiveEvenPart 𝒝 :=
        evenPart_mul_positiveEvenPart 𝒝 a.property hx'
      simp [δ.dpow_zero hx', δ.dpow_zero hax]
    · simpa using δ.dpow_mul_even hn a.property
        (by simpa [positiveEvenIdeal] using hx)
  mul_dpow {m n x} hx := by
    apply Subtype.ext
    change δ.dpow m ((x : evenSubalgebra 𝒝) : B) *
      δ.dpow n ((x : evenSubalgebra 𝒝) : B) = _
    simpa using δ.dpow_mul (by simpa [positiveEvenIdeal] using hx)
  dpow_comp {m n x} hn hx := by
    apply Subtype.ext
    have hx' : ((x : evenSubalgebra 𝒝) : B) ∈ positiveEvenPart 𝒝 := by
      simpa [positiveEvenIdeal] using hx
    by_cases hm : m = 0
    · subst m
      have hinner : δ.dpow n ((x : evenSubalgebra 𝒝) : B) ∈
          positiveEvenPart 𝒝 := δ.dpow_mem hn hx'
      simp [δ.dpow_zero hx', δ.dpow_zero hinner, Nat.uniformBell_zero_left]
    · rw [Nat.uniformBell_eq_div m hn]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        δ.dpow_dpow (m := n) (n := m) hn hm hx'

private noncomputable def extensionDividedPowersOfStructure
    (d : ℕ) [Fact (Even d)]
    (δ : DividedPowerStructure (EvenVariableAlgebra.grade 𝒜 d)) :
    DividedPowers (positiveEvenIdeal (EvenVariableAlgebra.grade 𝒜 d)) :=
  @evenPartDividedPowers R inferInstance (EvenVariableAlgebra A) _ _
    (EvenVariableAlgebra.grade 𝒜 d) _ _ δ

private theorem evenExtensionDpow_coeffEmbedding
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n : ℕ) {x : A}
    (hx : x ∈ positiveEvenPart 𝒜) :
    evenExtensionDpow d hd γ n (coeffEmbedding x) =
      coeffEmbedding (γ.dpow n x) := by
  let b : evenSubalgebra 𝒜 := ⟨x, positiveEvenPart_le_evenPart 𝒜 hx⟩
  have hx' : coeffEmbedding x ∈
      positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
    simpa [coeffEmbedding_apply] using
      evenPolynomial_monomial_mem_positiveEvenPart d hd 0
        (positiveEvenPart_le_evenPart 𝒜 hx) (fun _ ↦ hx)
  rw [evenExtensionDpow_of_mem d hd γ n hx']
  let z : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
    ⟨coeffEmbedding x, positiveEvenPart_le_evenPart _ hx'⟩
  have hz : z = evenDPAToExtensionEquiv (𝒜 := 𝒜) d
      (algebraMap (evenSubalgebra 𝒜)
        (DividedPowerAlgebra (evenSubalgebra 𝒜)
          (Unit →₀ evenSubalgebra 𝒜)) b) := by
    simpa [z, b] using (evenDPAToExtension_algebraMap d b).symm
  show ((evenExtensionDividedPowers d hd γ).dpow n z :
    EvenVariableAlgebra A) = _
  rw [hz, evenExtensionDividedPowers_dpow_algebraMap d hd γ n b hx,
    evenDPAToExtension_algebraMap]
  rfl

private theorem evenExtensionDpow_monomial_one
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n i : ℕ) (hi : 0 < i) :
    evenExtensionDpow d hd γ n (monomial i (1 : A)) =
      monomial (n * i)
        (dividedPowerMonomialCoefficient n i • (1 : A)) := by
  let B := evenSubalgebra 𝒜
  let P := DividedPowerAlgebra B (Unit →₀ B)
  let E := evenDPAToExtensionEquiv (𝒜 := 𝒜) d
  let t := Finsupp.single () (1 : B)
  have hpos : monomial i (1 : A) ∈
      positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
    apply evenPolynomial_monomial_mem_positiveEvenPart d hd i
    · exact Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜)
    · intro hi0
      omega
  rw [evenExtensionDpow_of_mem d hd γ n hpos]
  let z : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
    ⟨monomial i (1 : A), positiveEvenPart_le_evenPart _ hpos⟩
  have hz : z = E (DividedPowerAlgebra.dp B i t) := by
    simpa [z, B, P, E, t] using (evenDPAToExtension_dp_monomial d i).symm
  have hvarmem :
      dividedPowerPolynomialVariable B () ∈
        dividedPowerPolynomialIdeal (positiveEvenIdeal 𝒜) Unit := by
    rw [dividedPowerPolynomialIdeal]
    apply Submodule.mem_sup_right
    apply RingHom.mem_ker.mpr
    show dividedPowerPolynomialAugmentation B Unit
      (DividedPowerAlgebra.dp B 1 (Finsupp.single () (1 : B))) = 0
    rw [dividedPowerPolynomialAugmentation_dp_single]
    simp
  have hcomp :=
    (canonicalEvenPolynomialDividedPowers γ).dpow_comp
      (m := n) (n := i) (by omega) hvarmem
  simp only [canonicalEvenPolynomialDividedPowers] at hcomp
  rw [dividedPowerPolynomialDividedPowers_dpow_variable,
    dividedPowerPolynomialDividedPowers_dpow_variable] at hcomp
  have hcoefEven :
      dividedPowerMonomialCoefficient n i • (1 : A) ∈ evenPart 𝒜 :=
    (evenPart 𝒜).nsmul_mem
      (Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜))
      (dividedPowerMonomialCoefficient n i)
  have htarget :
      E ((Nat.uniformBell n i : P) * DividedPowerAlgebra.dp B (n * i) t) =
        ⟨monomial (n * i)
          (dividedPowerMonomialCoefficient n i • (1 : A)),
          evenPolynomial_monomial_mem_evenPart d (n * i)
            hcoefEven⟩ := by
    rw [map_mul, map_natCast, evenDPAToExtension_dp_monomial]
    apply Subtype.ext
    show (Nat.uniformBell n i : EvenVariableAlgebra A) *
        monomial (n * i) (1 : A) = _
    rw [show (Nat.uniformBell n i : EvenVariableAlgebra A) =
      coeffEmbedding (Nat.uniformBell n i : A) by simp,
      coeffEmbedding_apply, EvenVariableAlgebra.monomial_mul_monomial]
    have hcoeff : Nat.uniformBell n i = dividedPowerMonomialCoefficient n i := by
      rw [Nat.uniformBell_eq_div n (by omega : i ≠ 0)]
      simp [dividedPowerMonomialCoefficient,
        Nat.mul_comm]
    simp [hcoeff, EvenVariableAlgebra.monomial]
  show ((evenExtensionDividedPowers d hd γ).dpow n z :
    EvenVariableAlgebra A) = _
  rw [hz, evenExtensionDividedPowers, DividedPowers.ofRingEquiv_dpow_apply]
  simp only [
    dividedPowerPolynomialVariableMonomial] at hcomp
  have hcomp' : (canonicalEvenPolynomialDividedPowers γ).dpow n
      (DividedPowerAlgebra.dp B i t) =
      (Nat.uniformBell n i : P) * DividedPowerAlgebra.dp B (n * i) t := by
    simpa only [canonicalEvenPolynomialDividedPowers] using hcomp
  rw [hcomp', htarget]

private theorem evenExtensionDpow_monomial
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n i : ℕ) (hi : 0 < i)
    {a : A} (ha : a ∈ evenPart 𝒜) :
    evenExtensionDpow d hd γ n (monomial i a) =
      monomial (n * i) (dividedPowerMonomialCoefficient n i • a ^ n) := by
  let X : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
    ⟨coeffEmbedding a, by
      exact evenPolynomial_monomial_mem_evenPart d 0 ha⟩
  have hy : monomial i (1 : A) ∈
      positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
    apply evenPolynomial_monomial_mem_positiveEvenPart d hd i
    · exact Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜)
    · omega
  let Y : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
    ⟨monomial i (1 : A), positiveEvenPart_le_evenPart _ hy⟩
  have hpos : monomial i a ∈
      positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
    apply evenPolynomial_monomial_mem_positiveEvenPart d hd i
    · exact ha
    · omega
  let Z : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
    ⟨monomial i a, positiveEvenPart_le_evenPart _ hpos⟩
  have hz : Z = X * Y := by
    apply Subtype.ext
    show monomial i a = coeffEmbedding a * monomial i (1 : A)
    rw [show coeffEmbedding a = monomial 0 a by rfl,
      EvenVariableAlgebra.monomial_mul_monomial]
    simp [EvenVariableAlgebra.monomial]
  have hmul := (evenExtensionDividedPowers d hd γ).dpow_mul
      (n := n) (a := X) (x := Y) hy
  have hmul' := congrArg (fun z : evenSubalgebra
      (EvenVariableAlgebra.grade 𝒜 d) => (z : EvenVariableAlgebra A)) hmul
  rw [evenExtensionDpow_of_mem d hd γ n hpos]
  show ((evenExtensionDividedPowers d hd γ).dpow n Z :
      EvenVariableAlgebra A) = _
  calc
    (((evenExtensionDividedPowers d hd γ).dpow n Z :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) : EvenVariableAlgebra A) =
      (((evenExtensionDividedPowers d hd γ).dpow n (X * Y) :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) : EvenVariableAlgebra A) := by
          rw [hz]
    _ = ((X ^ n * (evenExtensionDividedPowers d hd γ).dpow n Y :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) : EvenVariableAlgebra A) := hmul'
    _ = monomial (n * i) (dividedPowerMonomialCoefficient n i • a ^ n) := by
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow]
      show ((X : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
          EvenVariableAlgebra A) ^ n *
        (((evenExtensionDividedPowers d hd γ).dpow n Y :
          evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) : EvenVariableAlgebra A) = _
      have hyDP : (((evenExtensionDividedPowers d hd γ).dpow n Y :
          evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) : EvenVariableAlgebra A) =
          evenExtensionDpow d hd γ n (monomial i (1 : A)) := by
        rw [evenExtensionDpow_of_mem d hd γ n hy]
      rw [hyDP, show (X : EvenVariableAlgebra A) = coeffEmbedding a by rfl]
      rw [evenExtensionDpow_monomial_one d hd γ n i hi]
      rw [show coeffEmbedding a = monomial 0 a by rfl]
      have hpow : monomial 0 a ^ n = monomial 0 (a ^ n) := by
        simpa only [coeffEmbedding_apply] using (map_pow (coeffEmbedding :
          A →+* EvenVariableAlgebra A) a n).symm
      rw [hpow, EvenVariableAlgebra.monomial_mul_monomial]
      simp only [Nat.zero_add, Nat.choose_zero_right, one_smul]
      apply congrArg (EvenVariableAlgebra.monomial (n * i))
      simpa using (Nat.cast_commute
        (dividedPowerMonomialCoefficient n i) (a ^ n)).eq.symm

private theorem positiveEvenPart_inter_grade_zero_eq_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (x : A) (hx : x ∈ positiveEvenPart 𝒜) (hx0 : x ∈ 𝒜 0) : x = 0 := by
  change x ∈ (⨆ d : ℕ, 𝒜 (2 * (d + 1))) at hx
  rw [Submodule.iSup_eq_span] at hx
  have hproj_aux : ∀ y : A,
      y ∈ Submodule.span R (⋃ d : ℕ, (𝒜 (2 * (d + 1)) : Set A)) →
        GradedAlgebra.proj 𝒜 0 y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hy
        rw [GradedAlgebra.proj_apply,
          DirectSum.decompose_of_mem_ne 𝒜 hd (by omega)]
    | zero => simp
    | add y z hy hz ihy ihz => simp [map_add, ihy, ihz]
    | smul r y hy ih => simp [map_smul, ih]
  have hproj : GradedAlgebra.proj 𝒜 0 x = 0 := hproj_aux x hx
  have hprojx : GradedAlgebra.proj 𝒜 0 x = x := by
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx0]
  exact hprojx.symm.trans hproj

private theorem evenExtensionDpow_zero_mem_grade
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) (n k : ℕ) :
    evenExtensionDpow d hd γ n 0 ∈ EvenVariableAlgebra.grade 𝒜 d (2 * n * k) := by
  rw [evenExtensionDpow_of_mem d hd γ n (Submodule.zero_mem _)]
  show ((evenExtensionDividedPowers d hd γ).dpow n
    (0 : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
      EvenVariableAlgebra A) ∈ _
  by_cases hn : n = 0
  · subst n
    rw [(evenExtensionDividedPowers d hd γ).dpow_zero (Submodule.zero_mem _)]
    simpa using SetLike.one_mem_graded (EvenVariableAlgebra.grade 𝒜 d)
  · rw [(evenExtensionDividedPowers d hd γ).dpow_eval_zero hn]
    exact Submodule.zero_mem _

private theorem evenExtensionDpow_mem_grade
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    (γ : DividedPowerStructure 𝒜) {n k : ℕ} {x : EvenVariableAlgebra A}
    (hxpos : x ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d))
    (hxgrade : x ∈ EvenVariableAlgebra.grade 𝒜 d (2 * k)) :
    evenExtensionDpow d hd γ n x ∈ EvenVariableAlgebra.grade 𝒜 d (2 * n * k) := by
  by_cases hk : k = 0
  · subst k
    have hxzero : x = 0 :=
      positiveEvenPart_inter_grade_zero_eq_zero
        (EvenVariableAlgebra.grade 𝒜 d) x hxpos hxgrade
    subst x
    exact evenExtensionDpow_zero_mem_grade d hd γ n 0
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hgradePos : EvenVariableAlgebra.grade 𝒜 d (2 * k) ≤
        positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
      have hdegree : 2 * k = 2 * ((k - 1) + 1) := by omega
      rw [hdegree]
      exact le_iSup_of_le (k - 1) le_rfl
    apply EvenVariableAlgebra.homogeneous_induction_on
      (𝒜 := 𝒜) (d := d) (m := 2 * k)
      (P := fun z ↦ ∀ n : ℕ, evenExtensionDpow d hd γ n z ∈
        EvenVariableAlgebra.grade 𝒜 d (2 * n * k)) hxgrade
    · exact fun n ↦ evenExtensionDpow_zero_mem_grade d hd γ n k
    · intro i a hid ha n
      have hmonoGrade : EvenVariableAlgebra.monomial i a ∈
          EvenVariableAlgebra.grade 𝒜 d (2 * k) := by
        have hsum : (2 * k - i * d) + i * d = 2 * k := by omega
        rw [← hsum]
        exact EvenVariableAlgebra.monomial_mem_grade 𝒜 d i
          (2 * k - i * d) ha
      have hmonoPos := hgradePos hmonoGrade
      rcases Fact.out (p := Even d) with ⟨q, hq⟩
      have hcoeffDegree : 2 * k - i * d = 2 * (k - i * q) := by
        have hid' : i * d = 2 * (i * q) := by rw [hq]; ring
        rw [hid']
        omega
      have haEven : a ∈ evenPart 𝒜 := by
        apply Submodule.mem_iSup_of_mem (k - i * q)
        rw [← hcoeffDegree]
        exact ha
      by_cases hi : i = 0
      · subst i
        have hapos : a ∈ positiveEvenPart 𝒜 := by
          apply Submodule.mem_iSup_of_mem (k - 1)
          have hbase : 2 * k - 0 * d = 2 * ((k - 1) + 1) := by omega
          rw [← hbase]
          exact ha
        rw [show EvenVariableAlgebra.monomial 0 a = coeffEmbedding a by rfl,
          evenExtensionDpow_coeffEmbedding d hd γ n hapos]
        by_cases hn : n = 0
        · subst n
          rw [γ.dpow_zero hapos]
          simpa using SetLike.one_mem_graded 𝒜
        · have hdpow : γ.dpow n a ∈ 𝒜 (2 * n * k) :=
            γ.dpow_mem_grade hn hapos (by simpa using ha)
          simpa [EvenVariableAlgebra.coeffEmbedding_mem_grade_iff] using hdpow
      · have hcoefPow : a ^ n ∈ 𝒜 (n * (2 * k - i * d)) := by
          have h := SetLike.pow_mem_graded n ha
          convert h using 1
          simp
        have hcoef :
            dividedPowerMonomialCoefficient n i • a ^ n ∈
              𝒜 (n * (2 * k - i * d)) :=
          (𝒜 (n * (2 * k - i * d))).nsmul_mem hcoefPow _
        have hdegree : n * (2 * k - i * d) + (n * i) * d = 2 * n * k := by
          have hsum : (2 * k - i * d) + i * d = 2 * k := by omega
          calc
            n * (2 * k - i * d) + (n * i) * d =
                n * ((2 * k - i * d) + i * d) := by ring
            _ = n * (2 * k) := congrArg (fun t : ℕ ↦ n * t) hsum
            _ = 2 * n * k := by ring
        show evenExtensionDpow d hd γ n (monomial i a) ∈
          EvenVariableAlgebra.grade 𝒜 d (2 * n * k)
        rw [evenExtensionDpow_monomial d hd γ n i (Nat.pos_of_ne_zero hi) haEven]
        rw [← hdegree]
        exact EvenVariableAlgebra.monomial_mem_grade 𝒜 d (n * i)
          (n * (2 * k - i * d)) hcoef
    · intro y z hy hz ihy ihz n
      have hypos := hgradePos hy
      have hzpos := hgradePos hz
      let Y : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
        ⟨y, positiveEvenPart_le_evenPart _ hypos⟩
      let Z : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
        ⟨z, positiveEvenPart_le_evenPart _ hzpos⟩
      have hadd := (evenExtensionDividedPowers d hd γ).dpow_add
        (n := n) (x := Y) (y := Z) hypos hzpos
      have hadd' : ((evenExtensionDividedPowers d hd γ).dpow n (Y + Z) :
          EvenVariableAlgebra A) =
        ∑ ij ∈ Finset.antidiagonal n,
          (((evenExtensionDividedPowers d hd γ).dpow ij.1 Y :
            evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
            EvenVariableAlgebra A) *
          (((evenExtensionDividedPowers d hd γ).dpow ij.2 Z :
            evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
            EvenVariableAlgebra A) := by
        simpa only [Subalgebra.coe_add, Subalgebra.coe_mul,
          AddSubmonoidClass.coe_finsetSum] using
          congrArg (fun w : evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) =>
            (w : EvenVariableAlgebra A)) hadd
      rw [evenExtensionDpow_of_mem d hd γ n
        ((positiveEvenPart _).add_mem hypos hzpos)]
      show ((evenExtensionDividedPowers d hd γ).dpow n (Y + Z) :
        EvenVariableAlgebra A) ∈ EvenVariableAlgebra.grade 𝒜 d (2 * n * k)
      rw [hadd']
      apply Submodule.sum_mem
      intro ij hij
      have hmul := SetLike.mul_mem_graded (ihy ij.1) (ihz ij.2)
      rw [evenExtensionDpow_of_mem d hd γ ij.1 hypos,
        evenExtensionDpow_of_mem d hd γ ij.2 hzpos] at hmul
      have hdegree : 2 * ij.1 * k + 2 * ij.2 * k = 2 * n * k := by
        have hanti := Finset.mem_antidiagonal.mp hij
        rw [← hanti]
        ring
      rw [hdegree] at hmul
      exact hmul

private theorem extensionOddProduct_mem
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {d e : ℕ} {x y : A}
    (hx : x ∈ 𝒜 (2 * d + 1)) (hy : y ∈ 𝒜 (2 * e + 1)) :
    x * y ∈ positiveEvenPart 𝒜 := by
  have hxy := SetLike.mul_mem_graded hx hy
  have hdegree : (2 * d + 1) + (2 * e + 1) = 2 * (d + e + 1) := by omega
  exact Submodule.mem_iSup_of_mem (d + e) (hdegree ▸ hxy)

private theorem dividedPowers_dpow_add_eq_zero_of_mul_eq_zero
    {B : Type*} [CommRing B] {I : Ideal B} (D : DividedPowers I)
    {a b : B} (ha : a ∈ I) (hb : b ∈ I)
    (hpa : ∀ n : ℕ, 1 < n → D.dpow n a = 0)
    (hpb : ∀ n : ℕ, 1 < n → D.dpow n b = 0)
    (hab : a * b = 0) (n : ℕ) (hn : 1 < n) :
    D.dpow n (a + b) = 0 := by
  rw [D.dpow_add ha hb]
  apply Finset.sum_eq_zero
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 = 0
  · have hj : 1 < ij.2 := by omega
    simp [hi, D.dpow_zero ha, hpb ij.2 hj]
  by_cases hj : ij.2 = 0
  · have hi' : 1 < ij.1 := by omega
    simp [hj, D.dpow_zero hb, hpa ij.1 hi']
  by_cases hi' : ij.1 = 1
  · by_cases hj' : ij.2 = 1
    · simp [hi', hj', D.dpow_one ha, D.dpow_one hb, hab]
    · have hj'' : 1 < ij.2 := by omega
      simp [hpb ij.2 hj'']
  · have hi'' : 1 < ij.1 := by omega
    simp [hpa ij.1 hi'']

omit [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] in
private theorem extensionOddCoeff_mem
    (d : ℕ) [Fact (Even d)] (k i : ℕ) {a : A}
    (hid : i * d ≤ 2 * k + 1)
    (ha : a ∈ 𝒜 (2 * k + 1 - i * d)) :
    ∃ q : ℕ, d = 2 * q ∧ a ∈ 𝒜 (2 * (k - i * q) + 1) := by
  rcases Fact.out (p := Even d) with ⟨q, hq⟩
  have hq' : d = 2 * q := by omega
  refine ⟨q, hq', ?_⟩
  have hidEven : i * d = 2 * (i * q) := by rw [hq]; ring
  have hid' : i * d ≤ 2 * k := by omega
  have hdegree : 2 * k + 1 - i * d = 2 * (k - i * q) + 1 := by omega
  rw [← hdegree]
  exact ha

/-- Two odd homogeneous elements of `A⟨T⟩` anticommute. -/
private theorem extensionOdd_mul_comm
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℕ → Submodule R A} [IsStrictlyGradedComm 𝒜]
    (d : ℕ) [Fact (Even d)] {k l : ℕ} {x y : EvenVariableAlgebra A}
    (hx : x ∈ EvenVariableAlgebra.grade 𝒜 d (2 * k + 1))
    (hy : y ∈ EvenVariableAlgebra.grade 𝒜 d (2 * l + 1)) :
    x * y = -(y * x) := by
  have hxodd : Odd (2 * k + 1) := ⟨k, by omega⟩
  have hyodd : Odd (2 * l + 1) := ⟨l, by omega⟩
  simpa only [(hxodd.mul hyodd).neg_one_pow, neg_one_smul] using
    IsStrictlyGradedComm.graded_comm hx hy

omit [GradedAlgebra 𝒜] in
private theorem extensionOddProduct_same_left_zero
    (d : ℕ) [Fact (Even d)] (_hd : 0 < d)
    {k l m : ℕ} {x y z : EvenVariableAlgebra A}
    (hx : x ∈ EvenVariableAlgebra.grade 𝒜 d (2 * k + 1))
    (hy : y ∈ EvenVariableAlgebra.grade 𝒜 d (2 * l + 1))
    (_hz : z ∈ EvenVariableAlgebra.grade 𝒜 d (2 * m + 1)) :
    (x * y) * (x * z) = 0 := by
  have hcomm := extensionOdd_mul_comm d hy hx
  have hx2 := IsStrictlyGradedComm.odd_sq_zero hx
  calc
    (x * y) * (x * z) = x * (y * x) * z := by simp only [mul_assoc]
    _ = -(x * x) * (y * z) := by
      rw [hcomm]
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [← pow_two, hx2]; simp

omit [GradedAlgebra 𝒜] in
private theorem extensionOddProduct_same_right_zero
    (d : ℕ) [Fact (Even d)] (hd : 0 < d)
    {k l m : ℕ} {x y z : EvenVariableAlgebra A}
    (hx : x ∈ EvenVariableAlgebra.grade 𝒜 d (2 * k + 1))
    (hy : y ∈ EvenVariableAlgebra.grade 𝒜 d (2 * l + 1))
    (hz : z ∈ EvenVariableAlgebra.grade 𝒜 d (2 * m + 1)) :
    (x * y) * (z * y) = 0 := by
  rw [extensionOdd_mul_comm d hx hy, extensionOdd_mul_comm d hz hy]
  simp only [neg_mul, mul_neg, neg_neg]
  exact extensionOddProduct_same_left_zero d hd hy hx hz

end Structure

end DividedPowers.TateResolution
