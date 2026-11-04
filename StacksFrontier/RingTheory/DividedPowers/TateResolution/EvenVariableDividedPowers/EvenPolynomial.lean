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
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers.Basic
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers.Basic

/-!
# Divided powers after adjoining an even variable: the even polynomial algebra

Let `A` be a strictly graded-commutative graded `R`-algebra with a divided power structure `γ`
on its positive even part, and let `d > 0` be even. This file compares the one-variable
algebra over the even part `A₊` of `A` with the one-variable divided power polynomial algebra
`DividedPowerAlgebra A₊ (Unit →₀ A₊)`, by comparing the two monomial bases, equips it with the
canonical divided powers of Tag 07H5, and identifies it with the even part of `A⟨T⟩`, matching
the positive even parts. It also describes membership in the even and positive even parts of
`A⟨T⟩` coefficientwise. All declarations here are private auxiliaries for
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

private def coefficientLinearEquiv (B : Type*) [CommRing B] :
    EvenVariableAlgebra B ≃ₗ[B] (ℕ →₀ B) where
  toFun := EvenVariableAlgebra.coeff
  invFun := EvenVariableAlgebra.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := EvenVariableAlgebra.coeff_add
  map_smul' := EvenVariableAlgebra.coeff_smul

private noncomputable def singletonExponentEquiv : ℕ ≃ (Unit →₀ ℕ) where
  toFun n := Finsupp.single () n
  invFun f := f ()
  left_inv _ := by simp
  right_inv f := by
    apply Finsupp.ext
    intro i
    cases i
    simp [Finsupp.single]

private noncomputable def evenPolynomialBasis (B : Type*) [CommRing B] :
    Module.Basis ℕ B (EvenVariableAlgebra B) :=
  (Finsupp.basisSingleOne : Module.Basis ℕ B (ℕ →₀ B)).map
    (coefficientLinearEquiv B).symm

private noncomputable def dividedPowerPolynomialBasis (B : Type*) [CommRing B] :
    Module.Basis ℕ B (DividedPowerAlgebra B (Unit →₀ B)) :=
  (_root_.DividedPowers.dividedPowerPolynomialMonomialBasis B
    Unit).reindex singletonExponentEquiv.symm

private noncomputable def evenPolynomialDPAEquiv (B : Type*) [CommRing B] :
    EvenVariableAlgebra B ≃ₗ[B] DividedPowerAlgebra B (Unit →₀ B) :=
  (evenPolynomialBasis B).equiv (dividedPowerPolynomialBasis B) (Equiv.refl ℕ)

private theorem evenPolynomialBasis_apply (B : Type*) [CommRing B] (n : ℕ) :
    evenPolynomialBasis B n = EvenVariableAlgebra.monomial n (1 : B) := by
  rfl

private theorem dividedPowerPolynomialBasis_apply (B : Type*) [CommRing B] (n : ℕ) :
    dividedPowerPolynomialBasis B n =
      DividedPowerAlgebra.dp B n (Finsupp.single () (1 : B)) := by
  rw [dividedPowerPolynomialBasis, Module.Basis.reindex_apply]
  rw [_root_.DividedPowers.dividedPowerPolynomialMonomialBasis_apply,
    _root_.DividedPowers.dividedPowerPolynomialMonomial]
  cases n with
  | zero =>
      show (Finsupp.single () 0).prod
        (fun i k ↦ DividedPowerAlgebra.dp B k (Finsupp.single i (1 : B))) = _
      rw [Finsupp.prod]
      simp [DividedPowerAlgebra.dp_zero]
  | succ n =>
      show (Finsupp.single () (n + 1)).prod
        (fun i k ↦ DividedPowerAlgebra.dp B k (Finsupp.single i (1 : B))) = _
      have hsupport : (Finsupp.single () (n + 1) : Unit →₀ ℕ).support = {()} :=
        Finsupp.support_single () (by omega)
      rw [Finsupp.prod]
      rw [hsupport]
      simp

private theorem evenPolynomialDPAEquiv_basis (B : Type*) [CommRing B] (n : ℕ) :
    evenPolynomialDPAEquiv B (EvenVariableAlgebra.monomial n (1 : B)) =
      DividedPowerAlgebra.dp B n (Finsupp.single () (1 : B)) := by
  rw [← evenPolynomialBasis_apply, evenPolynomialDPAEquiv]
  rw [Module.Basis.equiv_apply]
  exact dividedPowerPolynomialBasis_apply B n

private theorem evenPolynomialDPAEquiv_monomial (B : Type*) [CommRing B]
    (n : ℕ) (a : B) :
    evenPolynomialDPAEquiv B (EvenVariableAlgebra.monomial n a) =
      algebraMap B (DividedPowerAlgebra B (Unit →₀ B)) a *
        DividedPowerAlgebra.dp B n (Finsupp.single () (1 : B)) := by
  have hmono : EvenVariableAlgebra.monomial n a =
      a • EvenVariableAlgebra.monomial n (1 : B) := by
    simp [EvenVariableAlgebra.smul_monomial]
  rw [hmono, map_smul, evenPolynomialDPAEquiv_basis]
  simp [Algebra.smul_def]

private theorem dividedPowerPolynomialAugmentation_dp_single
    (B : Type*) [CommRing B] (n : ℕ) :
    dividedPowerPolynomialAugmentation B Unit
      (DividedPowerAlgebra.dp B n (Finsupp.single () (1 : B))) =
      if n = 0 then 1 else 0 := by
  have h : dividedPowerPolynomialAugmentation B Unit
      = DividedPowerAlgebra.augmentation B (Unit →₀ B) := rfl
  rw [h, DividedPowerAlgebra.augmentation_dp]

private theorem dividedPowerPolynomialAugmentation_evenPolynomialDPAEquiv
    (B : Type*) [CommRing B] (x : EvenVariableAlgebra B) :
    dividedPowerPolynomialAugmentation B Unit
      (evenPolynomialDPAEquiv B x) = x.coeff 0 := by
  induction x using EvenVariableAlgebra.induction_on with
  | zero => simp
  | add n a x ih =>
      rw [map_add, map_add, ih,
        evenPolynomialDPAEquiv_monomial,
        map_mul, dividedPowerPolynomialAugmentation_dp_single]
      simp [EvenVariableAlgebra.coeff_add, Finsupp.single_apply]

private theorem dividedPowerPolynomialIdeal_mem_iff_augmentation_mem
    (B : Type*) [CommRing B] (I : Ideal B)
    (y : DividedPowerAlgebra B (Unit →₀ B)) :
    y ∈ dividedPowerPolynomialIdeal I Unit ↔
      dividedPowerPolynomialAugmentation B Unit y ∈ I := by
  let ε := dividedPowerPolynomialAugmentation B Unit
  let f := algebraMap B (DividedPowerAlgebra B (Unit →₀ B))
  have hmap : Ideal.map f I ≤ Ideal.comap ε I := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    show ε (f b) ∈ I
    show dividedPowerPolynomialAugmentation B Unit
      (algebraMap B (DividedPowerAlgebra B (Unit →₀ B)) b) ∈ I
    simpa [dividedPowerPolynomialAugmentation] using hb
  have hker : RingHom.ker ε ≤ Ideal.comap ε I := by
    intro z hz
    show ε z ∈ I
    simp [RingHom.mem_ker.mp hz]
  have hle : dividedPowerPolynomialIdeal I Unit ≤ Ideal.comap ε I := by
    rw [dividedPowerPolynomialIdeal]
    exact sup_le hmap hker
  have hrev : Ideal.comap ε I ≤ dividedPowerPolynomialIdeal I Unit := by
    intro z hz
    rw [dividedPowerPolynomialIdeal]
    have hcoeff : ε z ∈ I := hz
    have hconst : f (ε z) ∈ Ideal.map f I := Ideal.mem_map_of_mem f hcoeff
    have hdiff : z - f (ε z) ∈ RingHom.ker ε := by
      apply RingHom.mem_ker.mpr
      simp [ε, f, map_sub]
    have hsum : f (ε z) + (z - f (ε z)) = z := by ring
    rw [← hsum]
    exact add_mem (Submodule.mem_sup_left hconst) (Submodule.mem_sup_right hdiff)
  constructor
  · intro hz
    exact hle hz
  · intro hz
    exact hrev hz

/-- Two-variable induction over `EvenVariableAlgebra`: a binary predicate that is additive in each
variable and holds on pairs of monomials holds everywhere. -/
private theorem evenVariable_induction_two {B : Type*} [Ring B]
    {P : EvenVariableAlgebra B → EvenVariableAlgebra B → Prop}
    (zero_left : ∀ y, P 0 y) (zero_right : ∀ x, P x 0)
    (add_left : ∀ x x' y, P x y → P x' y → P (x + x') y)
    (add_right : ∀ x y y', P x y → P x y' → P x (y + y'))
    (monomial : ∀ n a m b, P (EvenVariableAlgebra.monomial n a) (EvenVariableAlgebra.monomial m b))
    (x y : EvenVariableAlgebra B) : P x y := by
  induction x using EvenVariableAlgebra.induction_on with
  | zero => exact zero_left y
  | add n a x hx =>
      refine add_left _ _ _ ?_ hx
      clear hx
      induction y using EvenVariableAlgebra.induction_on with
      | zero => exact zero_right _
      | add m b y hy => exact add_right _ _ _ (monomial n a m b) hy

private theorem evenPolynomialDPAEquiv_map_monomial_mul (B : Type*) [CommRing B]
    (n m : ℕ) (a b : B) :
    evenPolynomialDPAEquiv B
        (EvenVariableAlgebra.monomial n a * EvenVariableAlgebra.monomial m b) =
    evenPolynomialDPAEquiv B (EvenVariableAlgebra.monomial n a) *
        evenPolynomialDPAEquiv B (EvenVariableAlgebra.monomial m b) := by
  rw [EvenVariableAlgebra.monomial_mul_monomial,
    evenPolynomialDPAEquiv_monomial, evenPolynomialDPAEquiv_monomial,
    evenPolynomialDPAEquiv_monomial]
  let D := DividedPowerAlgebra B (Unit →₀ B)
  let t := Finsupp.single () (1 : B)
  have hdp : DividedPowerAlgebra.dp B n t * DividedPowerAlgebra.dp B m t =
      (Nat.choose (n + m) n : D) * DividedPowerAlgebra.dp B (n + m) t := by
    simpa [D, t, Algebra.smul_def] using
      (DividedPowerAlgebra.dp_mul (R := B) (n := n) (p := m) (m := t))
  calc
    algebraMap B D (Nat.choose (n + m) n • (a * b)) *
        DividedPowerAlgebra.dp B (n + m) t =
        (algebraMap B D a * algebraMap B D b) *
          ((Nat.choose (n + m) n : D) *
            DividedPowerAlgebra.dp B (n + m) t) := by
      simp [D, Algebra.smul_def, map_mul, mul_comm, mul_left_comm, mul_assoc]
    _ = (algebraMap B D a * algebraMap B D b) *
          (DividedPowerAlgebra.dp B n t * DividedPowerAlgebra.dp B m t) := by
      rw [← hdp]
    _ = algebraMap B D a * DividedPowerAlgebra.dp B n t *
          (algebraMap B D b * DividedPowerAlgebra.dp B m t) := by ring

private theorem evenPolynomialDPAEquiv_map_mul (B : Type*) [CommRing B]
    (x y : EvenVariableAlgebra B) :
    evenPolynomialDPAEquiv B (x * y) = evenPolynomialDPAEquiv B x *
      evenPolynomialDPAEquiv B y := by
  induction x, y using evenVariable_induction_two with
  | zero_left y => simp
  | zero_right x => simp
  | add_left x x' y hx hx' => simp [add_mul, hx, hx']
  | add_right x y y' hy hy' => simp [mul_add, hy, hy']
  | monomial n a m b => exact evenPolynomialDPAEquiv_map_monomial_mul B n m a b

private noncomputable def evenPolynomialDPARingEquiv (B : Type*) [CommRing B] :
    EvenVariableAlgebra B ≃+* DividedPowerAlgebra B (Unit →₀ B) where
  toFun := evenPolynomialDPAEquiv B
  invFun := (evenPolynomialDPAEquiv B).symm
  left_inv := (evenPolynomialDPAEquiv B).left_inv
  right_inv := (evenPolynomialDPAEquiv B).right_inv
  map_mul' := evenPolynomialDPAEquiv_map_mul B
  map_add' := map_add (evenPolynomialDPAEquiv B)

private theorem evenPolynomial_mul_comm (B : Type*) [CommRing B]
    (x y : EvenVariableAlgebra B) : x * y = y * x := by
  induction x, y using evenVariable_induction_two with
  | zero_left y => simp
  | zero_right x => simp
  | add_left x x' y hx hx' => rw [add_mul, mul_add, hx, hx']
  | add_right x y y' hy hy' => rw [add_mul, mul_add, hy, hy']
  | monomial n a m b =>
      rw [EvenVariableAlgebra.monomial_mul_monomial,
        EvenVariableAlgebra.monomial_mul_monomial, Nat.add_comm m n, Nat.choose_symm_add]
      simp [mul_comm]

private noncomputable instance evenPolynomialCommRing (B : Type*) [CommRing B] :
    CommRing (EvenVariableAlgebra B) :=
  { (inferInstance : Ring (EvenVariableAlgebra B)) with
    mul_comm := evenPolynomial_mul_comm B }

private abbrev coefficientDividedPowerRing
    (γ : DividedPowerStructure 𝒜) : DividedPowerRing :=
  .of (evenSubalgebra 𝒜) (positiveEvenIdeal 𝒜) (baseDividedPowers γ)

private noncomputable def canonicalEvenPolynomialDividedPowers
    (γ : DividedPowerStructure 𝒜) :
    DividedPowers
      (dividedPowerPolynomialIdeal
        (coefficientDividedPowerRing γ).ideal Unit) :=
  dividedPowerPolynomialDividedPowers
    (coefficientDividedPowerRing γ) Unit

private noncomputable def evenPolynomialPositiveIdeal
    (γ : DividedPowerStructure 𝒜) : Ideal (EvenVariableAlgebra (evenSubalgebra 𝒜)) :=
  (dividedPowerPolynomialIdeal
    (coefficientDividedPowerRing γ).ideal Unit).comap
      (evenPolynomialDPARingEquiv (evenSubalgebra 𝒜)).toRingHom

private noncomputable def evenPolynomialDividedPowers
    (γ : DividedPowerStructure 𝒜) : DividedPowers (evenPolynomialPositiveIdeal γ) :=
  let e := evenPolynomialDPARingEquiv (evenSubalgebra 𝒜)
  let I := dividedPowerPolynomialIdeal
    (coefficientDividedPowerRing γ).ideal Unit
  have hmap : I.map e.symm.toRingHom = I.comap e.toRingHom := by
    ext x
    change x ∈ I.map e.symm.toRingHom ↔ e x ∈ I
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ :=
        (Ideal.mem_map_iff_of_surjective _ e.symm.surjective).mp hx
      have hcomp := congrArg e hxy
      exact hcomp ▸ (by simpa using hy)
    · intro hx
      simpa using Ideal.mem_map_of_mem e.symm.toRingHom hx
  have hmap' : I.map e.symm.toRingHom = evenPolynomialPositiveIdeal γ := by
    simpa [evenPolynomialPositiveIdeal, e, I] using hmap
  DividedPowers.ofRingEquiv hmap' (canonicalEvenPolynomialDividedPowers γ)

omit [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] in
private theorem evenPart_coeff_mem
    (d : ℕ) [Fact (Even d)] (x : EvenVariableAlgebra A)
    (hx : x ∈ evenPart (EvenVariableAlgebra.grade 𝒜 d)) (i : ℕ) :
    x.coeff i ∈ evenPart 𝒜 := by
  change x ∈ (⨆ k : ℕ, EvenVariableAlgebra.grade 𝒜 d (2 * k)) at hx
  rw [Submodule.iSup_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      have hcoeff := (EvenVariableAlgebra.mem_grade_iff 𝒜 d (2 * k) x).mp hk i
      by_cases hle : i * d ≤ 2 * k
      · have hcoeff' : x.coeff i ∈ 𝒜 (2 * k - i * d) := by
          simpa [hle] using hcoeff
        have hd : Even d := Fact.out
        rcases hd with ⟨q, hq⟩
        have hid : i * d = 2 * (i * q) := by rw [hq]; ring
        have hdegree : 2 * k - i * d = 2 * (k - i * q) := by
          rw [hid]
          omega
        exact Submodule.mem_iSup_of_mem (k - i * q) (by rw [← hdegree]; exact hcoeff')
      · have hzero : x.coeff i = 0 := by
          have : x.coeff i ∈ (⊥ : Submodule R A) := by simpa [hle] using hcoeff
          simpa using this
        rw [hzero]
        exact (evenPart 𝒜).zero_mem
  | zero => exact (evenPart 𝒜).zero_mem
  | add x y hx hy ihx ihy =>
      rw [EvenVariableAlgebra.coeff_add]
      exact (evenPart 𝒜).add_mem ihx ihy
  | smul r x hx ih =>
      rw [EvenVariableAlgebra.coeff_smul]
      exact (evenPart 𝒜).smul_mem r ih

omit [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] in
private theorem positiveEvenPart_constant_coeff_mem
    (d : ℕ) (x : EvenVariableAlgebra A)
    (hx : x ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d)) :
    x.coeff 0 ∈ positiveEvenPart 𝒜 := by
  change x ∈ (⨆ k : ℕ, EvenVariableAlgebra.grade 𝒜 d (2 * (k + 1))) at hx
  rw [Submodule.iSup_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      have hcoeff := (EvenVariableAlgebra.mem_grade_iff 𝒜 d (2 * (k + 1)) x).mp hk 0
      exact Submodule.mem_iSup_of_mem k (by simpa using hcoeff)
  | zero => exact (positiveEvenPart 𝒜).zero_mem
  | add x y hx hy ihx ihy =>
      rw [EvenVariableAlgebra.coeff_add]
      exact (positiveEvenPart 𝒜).add_mem ihx ihy
  | smul r x hx ih =>
      rw [EvenVariableAlgebra.coeff_smul]
      exact (positiveEvenPart 𝒜).smul_mem r ih

private noncomputable def evenPolynomialToExtensionFun
    (x : EvenVariableAlgebra (evenSubalgebra 𝒜)) : EvenVariableAlgebra A :=
  ⟨Finsupp.mapRange (fun b : evenSubalgebra 𝒜 ↦ (b : A)) (by simp) x.coeff⟩

private theorem evenPolynomialToExtensionFun_add
    (x y : EvenVariableAlgebra (evenSubalgebra 𝒜)) :
    evenPolynomialToExtensionFun (x + y) =
      evenPolynomialToExtensionFun x + evenPolynomialToExtensionFun y := by
  apply EvenVariableAlgebra.ext
  ext i
  simp [evenPolynomialToExtensionFun, Finsupp.mapRange_apply,
    EvenVariableAlgebra.coeff_add]

private theorem evenPolynomialToExtensionFun_zero :
    evenPolynomialToExtensionFun (0 : EvenVariableAlgebra (evenSubalgebra 𝒜)) = 0 := by
  apply EvenVariableAlgebra.ext
  simp [evenPolynomialToExtensionFun]

omit [IsStrictlyGradedComm 𝒜] in
private theorem evenPolynomialToExtension_monomial (n : ℕ) (a : evenSubalgebra 𝒜) :
    evenPolynomialToExtensionFun (EvenVariableAlgebra.monomial n a) =
      EvenVariableAlgebra.monomial n (a : A) := by
  apply EvenVariableAlgebra.ext
  ext i
  simp [evenPolynomialToExtensionFun, EvenVariableAlgebra.monomial,
    Finsupp.mapRange_single]

omit [IsStrictlyGradedComm 𝒜] in
private theorem evenPolynomialToExtension_map_monomial_mul
    (n m : ℕ) (a b : evenSubalgebra 𝒜) :
    evenPolynomialToExtensionFun
        (EvenVariableAlgebra.monomial n a * EvenVariableAlgebra.monomial m b) =
      evenPolynomialToExtensionFun (EvenVariableAlgebra.monomial n a) *
        evenPolynomialToExtensionFun (EvenVariableAlgebra.monomial m b) := by
  rw [EvenVariableAlgebra.monomial_mul_monomial,
    evenPolynomialToExtension_monomial, evenPolynomialToExtension_monomial,
    evenPolynomialToExtension_monomial]
  simp [EvenVariableAlgebra.monomial_mul_monomial, Subalgebra.coe_mul]

private theorem evenPolynomialToExtension_map_mul
    (x y : EvenVariableAlgebra (evenSubalgebra 𝒜)) :
    evenPolynomialToExtensionFun (x * y) =
      evenPolynomialToExtensionFun x * evenPolynomialToExtensionFun y := by
  induction x, y using evenVariable_induction_two with
  | zero_left y => simp [evenPolynomialToExtensionFun_zero]
  | zero_right x => simp [evenPolynomialToExtensionFun_zero]
  | add_left x x' y hx hx' => simp [add_mul, evenPolynomialToExtensionFun_add, hx, hx']
  | add_right x y y' hy hy' => simp [mul_add, evenPolynomialToExtensionFun_add, hy, hy']
  | monomial n a m b => exact evenPolynomialToExtension_map_monomial_mul n m a b

private noncomputable def evenPolynomialToExtension :
    EvenVariableAlgebra (evenSubalgebra 𝒜) →+* EvenVariableAlgebra A where
  toFun := evenPolynomialToExtensionFun
  map_zero' := by
    apply EvenVariableAlgebra.ext
    ext i
    simp [evenPolynomialToExtensionFun]
  map_add' := evenPolynomialToExtensionFun_add
  map_one' := by
    rw [show (1 : EvenVariableAlgebra (evenSubalgebra 𝒜)) =
      EvenVariableAlgebra.monomial 0 1 from rfl,
      evenPolynomialToExtension_monomial]
    rfl
  map_mul' := evenPolynomialToExtension_map_mul

/-- If `a T⁽ⁿ⁾` lies in `N` whenever `a` lies in a single summand `M k`, then it does for `a` in
the supremum of the `M k`. -/
private theorem monomial_mem_of_mem_iSup (n : ℕ) (M : ℕ → Submodule R A)
    (N : Submodule R (EvenVariableAlgebra A))
    (h : ∀ k, ∀ a ∈ M k, EvenVariableAlgebra.monomial n a ∈ N) {a : A} (ha : a ∈ ⨆ k, M k) :
    EvenVariableAlgebra.monomial n a ∈ N :=
  (iSup_le fun k a ha ↦ h k a ha : (⨆ k, M k) ≤ N.comap (EvenVariableAlgebra.monomialLinearMap n))
    ha

omit [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] in
private theorem evenPolynomial_monomial_mem_evenPart
    (d : ℕ) [Fact (Even d)] (n : ℕ) {a : A} (ha : a ∈ evenPart 𝒜) :
    EvenVariableAlgebra.monomial n a ∈
      evenPart (EvenVariableAlgebra.grade 𝒜 d) := by
  change a ∈ (⨆ k : ℕ, 𝒜 (2 * k)) at ha
  refine monomial_mem_of_mem_iSup n _ _ (fun k a hk ↦ ?_) ha
  obtain ⟨q, hq⟩ := Fact.out (p := Even d)
  have hdegree : 2 * k + n * d = 2 * (k + n * q) := by
    rw [hq]
    ring
  apply Submodule.mem_iSup_of_mem (k + n * q)
  simpa only [hdegree] using EvenVariableAlgebra.monomial_mem_grade 𝒜 d n (2 * k) hk

omit [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] in
private theorem evenPart_mem_of_coeff_even
    (d : ℕ) [Fact (Even d)] (x : EvenVariableAlgebra A)
    (hx : ∀ i, x.coeff i ∈ evenPart 𝒜) :
    x ∈ evenPart (EvenVariableAlgebra.grade 𝒜 d) := by
  rw [← EvenVariableAlgebra.sum_monomial x]
  apply Submodule.sum_mem
  intro i hi
  exact evenPolynomial_monomial_mem_evenPart d i (hx i)

omit [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] in
private theorem evenPolynomial_monomial_mem_positiveEvenPart
    (d : ℕ) [Fact (Even d)] (hd : 0 < d) (n : ℕ) {a : A}
    (haEven : a ∈ evenPart 𝒜)
    (hzeroBase : n = 0 → a ∈ positiveEvenPart 𝒜) :
    EvenVariableAlgebra.monomial n a ∈
      positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
  by_cases hn : n = 0
  · subst n
    have hpos := hzeroBase rfl
    change a ∈ (⨆ k : ℕ, 𝒜 (2 * (k + 1))) at hpos
    refine monomial_mem_of_mem_iSup 0 _ _ (fun k a hk ↦ ?_) hpos
    apply Submodule.mem_iSup_of_mem k
    simpa using EvenVariableAlgebra.monomial_mem_grade 𝒜 d 0 (2 * (k + 1)) hk
  · change a ∈ (⨆ k : ℕ, 𝒜 (2 * k)) at haEven
    refine monomial_mem_of_mem_iSup n _ _ (fun k a hk ↦ ?_) haEven
    obtain ⟨q, hq⟩ := Fact.out (p := Even d)
    have hdegree : 2 * k + n * d = 2 * (k + n * q) := by
      rw [hq]
      ring
    have hpositive : 0 < n * q := Nat.mul_pos (by omega) (by omega)
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k + n * q ≠ 0)
    apply Submodule.mem_iSup_of_mem r
    have heq : 2 * k + n * d = 2 * (r + 1) := by omega
    rw [← heq]
    exact EvenVariableAlgebra.monomial_mem_grade 𝒜 d n (2 * k) hk

omit [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] in
private theorem positiveEvenPart_mem_of_coeff_even
    (d : ℕ) [Fact (Even d)] (hd : 0 < d) (x : EvenVariableAlgebra A)
    (heven : ∀ i, x.coeff i ∈ evenPart 𝒜)
    (hzero : x.coeff 0 ∈ positiveEvenPart 𝒜) :
    x ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) := by
  rw [← EvenVariableAlgebra.sum_monomial x]
  apply Submodule.sum_mem
  intro i hi
  exact evenPolynomial_monomial_mem_positiveEvenPart d hd i (heven i)
    (fun hizero ↦ by simpa [hizero] using hzero)

omit [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] in
private theorem evenPart_positiveEvenPart_iff_constant
    (d : ℕ) [Fact (Even d)] (hd : 0 < d) (x : EvenVariableAlgebra A)
    (heven : ∀ i, x.coeff i ∈ evenPart 𝒜) :
    x ∈ positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) ↔
      x.coeff 0 ∈ positiveEvenPart 𝒜 := by
  constructor
  · exact positiveEvenPart_constant_coeff_mem d x
  · exact positiveEvenPart_mem_of_coeff_even d hd x heven

private noncomputable def evenPolynomialToEvenSubalgebra (d : ℕ)
    [Fact (Even d)] :
    EvenVariableAlgebra (evenSubalgebra 𝒜) →+*
      evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
  evenPolynomialToExtension.codRestrict
    (evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) (fun x ↦ by
      apply evenPart_mem_of_coeff_even d
      intro i
      exact (x.coeff i).property)

private theorem evenPolynomialToEvenSubalgebra_injective (d : ℕ)
    [Fact (Even d)] : Function.Injective (evenPolynomialToEvenSubalgebra (𝒜 := 𝒜) d) := by
  intro x y h
  apply EvenVariableAlgebra.ext
  ext i
  have hv : ((evenPolynomialToExtension x).coeff i) =
      ((evenPolynomialToExtension y).coeff i) := by
    have hval := congrArg Subtype.val h
    exact congrArg (fun z : EvenVariableAlgebra A ↦ z.coeff i) hval
  simpa [evenPolynomialToExtension, evenPolynomialToExtensionFun,
    Finsupp.mapRange_apply] using hv

private noncomputable def evenPolynomialPreimage
    (x : EvenVariableAlgebra A)
    (_hx : ∀ i, x.coeff i ∈ evenPart 𝒜) : EvenVariableAlgebra (evenSubalgebra 𝒜) := by
  classical
  refine ⟨Finsupp.mapRange (fun a : A ↦ if ha : a ∈ evenPart 𝒜 then ⟨a, ha⟩ else 0)
    ?_ x.coeff⟩
  exact Subtype.ext (by simp)

private theorem evenPolynomialPreimage_mapsTo
    (x : EvenVariableAlgebra A) (hx : ∀ i, x.coeff i ∈ evenPart 𝒜) :
    evenPolynomialToExtension (evenPolynomialPreimage x hx) = x := by
  apply EvenVariableAlgebra.ext
  ext i
  simp [evenPolynomialPreimage, evenPolynomialToExtension, evenPolynomialToExtensionFun,
    Finsupp.mapRange_apply, hx i]

private theorem evenPolynomialToEvenSubalgebra_surjective (d : ℕ)
    [Fact (Even d)] : Function.Surjective (evenPolynomialToEvenSubalgebra (𝒜 := 𝒜) d) := by
  intro x
  let y := evenPolynomialPreimage (x : EvenVariableAlgebra A)
    (fun i ↦ evenPart_coeff_mem d (x : EvenVariableAlgebra A) x.property i)
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact evenPolynomialPreimage_mapsTo (x : EvenVariableAlgebra A)
    (fun i ↦ evenPart_coeff_mem d (x : EvenVariableAlgebra A) x.property i)

private noncomputable def evenPolynomialToEvenSubalgebraEquiv (d : ℕ)
    [Fact (Even d)] : EvenVariableAlgebra (evenSubalgebra 𝒜) ≃+*
      evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
  RingEquiv.ofBijective (evenPolynomialToEvenSubalgebra (𝒜 := 𝒜) d)
    ⟨evenPolynomialToEvenSubalgebra_injective d,
      evenPolynomialToEvenSubalgebra_surjective d⟩

private theorem evenPolynomialToEvenSubalgebraEquiv_apply (d : ℕ)
    [Fact (Even d)] (x : EvenVariableAlgebra (evenSubalgebra 𝒜)) :
    evenPolynomialToEvenSubalgebraEquiv d x = evenPolynomialToEvenSubalgebra d x := rfl

private noncomputable def evenDPAToExtensionEquiv (d : ℕ)
    [Fact (Even d)] :
    DividedPowerAlgebra (evenSubalgebra 𝒜) (Unit →₀ evenSubalgebra 𝒜) ≃+*
      evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d) :=
  (evenPolynomialDPARingEquiv (evenSubalgebra 𝒜)).symm.trans
    (evenPolynomialToEvenSubalgebraEquiv d)

private theorem evenPolynomialToEvenSubalgebra_coeff (d : ℕ)
    [Fact (Even d)] (x : EvenVariableAlgebra (evenSubalgebra 𝒜)) (i : ℕ) :
    (((evenPolynomialToEvenSubalgebra d x :
      evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
      EvenVariableAlgebra A).coeff i) = (x.coeff i : A) := by
  simp [evenPolynomialToEvenSubalgebra, evenPolynomialToExtension,
    evenPolynomialToExtensionFun, Finsupp.mapRange_apply]

private theorem evenDPAToExtension_coeff_zero_augmentation (d : ℕ)
    [Fact (Even d)]
    (y : DividedPowerAlgebra (evenSubalgebra 𝒜) (Unit →₀ evenSubalgebra 𝒜)) :
    ((((evenDPAToExtensionEquiv (𝒜 := 𝒜) d) y :
      evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
      EvenVariableAlgebra A).coeff 0) =
        ((dividedPowerPolynomialAugmentation (evenSubalgebra 𝒜)
          Unit y : evenSubalgebra 𝒜) : A) := by
  let p : EvenVariableAlgebra (evenSubalgebra 𝒜) :=
    (evenPolynomialDPARingEquiv (evenSubalgebra 𝒜)).symm y
  have hp : evenPolynomialDPAEquiv (evenSubalgebra 𝒜) p = y := by
    simp [p, evenPolynomialDPARingEquiv]
  have haug := dividedPowerPolynomialAugmentation_evenPolynomialDPAEquiv
    (evenSubalgebra 𝒜) p
  rw [hp] at haug
  show (((evenPolynomialToEvenSubalgebra d p :
    evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
    EvenVariableAlgebra A).coeff 0) = _
  rw [evenPolynomialToEvenSubalgebra_coeff]
  exact congrArg Subtype.val haug.symm

private theorem evenDPAToExtension_ideal_mem_iff (d : ℕ)
    [Fact (Even d)] (hd : 0 < d)
    (y : DividedPowerAlgebra (evenSubalgebra 𝒜) (Unit →₀ evenSubalgebra 𝒜)) :
    evenDPAToExtensionEquiv (𝒜 := 𝒜) d y ∈
        positiveEvenIdeal (EvenVariableAlgebra.grade 𝒜 d) ↔
      dividedPowerPolynomialAugmentation (evenSubalgebra 𝒜)
        Unit y ∈ positiveEvenIdeal 𝒜 := by
  have heven (i : ℕ) :
      ((evenDPAToExtensionEquiv (𝒜 := 𝒜) d y :
        evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
        EvenVariableAlgebra A).coeff i ∈ evenPart 𝒜 := by
    exact evenPart_coeff_mem d _
      (evenDPAToExtensionEquiv (𝒜 := 𝒜) d y).property i
  show ((evenDPAToExtensionEquiv (𝒜 := 𝒜) d y :
      evenSubalgebra (EvenVariableAlgebra.grade 𝒜 d)) :
      EvenVariableAlgebra A) ∈
        positiveEvenPart (EvenVariableAlgebra.grade 𝒜 d) ↔
    ((dividedPowerPolynomialAugmentation (evenSubalgebra 𝒜)
      Unit y : evenSubalgebra 𝒜) : A) ∈ positiveEvenPart 𝒜
  rw [evenPart_positiveEvenPart_iff_constant d hd _ heven,
    evenDPAToExtension_coeff_zero_augmentation]

private theorem evenDPAPositiveIdeal_map_eq (d : ℕ)
    [Fact (Even d)] (hd : 0 < d) :
    (dividedPowerPolynomialIdeal (positiveEvenIdeal 𝒜) Unit).map
      (evenDPAToExtensionEquiv (𝒜 := 𝒜) d) =
        positiveEvenIdeal (EvenVariableAlgebra.grade 𝒜 d) := by
  ext x
  rw [Ideal.mem_map_iff_of_surjective
    (evenDPAToExtensionEquiv (𝒜 := 𝒜) d)
    (evenDPAToExtensionEquiv (𝒜 := 𝒜) d).surjective]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (evenDPAToExtension_ideal_mem_iff d hd y).2
      ((dividedPowerPolynomialIdeal_mem_iff_augmentation_mem
        (evenSubalgebra 𝒜) (positiveEvenIdeal 𝒜) y).1 hy)
  · intro hx
    refine ⟨(evenDPAToExtensionEquiv (𝒜 := 𝒜) d).symm x, ?_,
      (evenDPAToExtensionEquiv (𝒜 := 𝒜) d).apply_symm_apply x⟩
    apply (dividedPowerPolynomialIdeal_mem_iff_augmentation_mem
      (evenSubalgebra 𝒜) (positiveEvenIdeal 𝒜) _).2
    apply (evenDPAToExtension_ideal_mem_iff d hd _).1
    simpa using hx

end Structure

end DividedPowers.TateResolution
