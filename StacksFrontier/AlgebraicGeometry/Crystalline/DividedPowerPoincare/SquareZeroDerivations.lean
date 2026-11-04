module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Functoriality
public import StacksFrontier.LinearAlgebra.ExteriorPower.BasisConstr
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.SetIndexed
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.SetIndexedUniversalProperty
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.RingTheory.Koszul.Functoriality

/-!
# The divided power Poincaré lemma: the coefficient ring and square-zero extensions

The first part of `StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare`: the
coefficient ring `A` with the trivial divided powers on its zero ideal, the divided power
polynomial algebra `P = A⟨x_w : w ∈ W⟩` with its canonical divided powers and the local instances
used throughout, the identification `Crystalline.coefficientLinearEquiv` of the coefficients with
`A`, and the square-zero divided power extension `P ⊕ M` through which divided power derivations
out of `P` are lifted.

## References

* [Stacks Project, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
-/
@[expose] public section

universe u v w uA uW uM

namespace Crystalline

attribute [local implicit_reducible] RestrictScalars

open DividedPowers
open scoped TensorProduct

section OrdinaryExactness

open CategoryTheory
open scoped RightActions

variable (A : Type u) [CommRing A] (W : Type w)

/-- The trivial divided powers on the zero ideal of the coefficient ring. -/
public noncomputable def coefficientDividedPowerRing :
    DividedPowerRing.{u} :=
  { carrier := A
    ideal := ⊥
    dividedPowers := dividedPowersBot A }

/-- The canonical divided powers on its augmentation ideal. -/
public noncomputable def polynomialDividedPowers :=
  setIndexedDividedPowerPolynomialDividedPowers (coefficientDividedPowerRing A) W

attribute [local implicit_reducible] coefficientDividedPowerRing
  DividedPowers.setIndexedDividedPowerPolynomialDividedPowerRing

/-- The ring structure of the set-indexed divided power polynomial algebra, as the quotient of a
multivariate polynomial ring by the divided power relations.  It is a `local instance` of low
priority here and in every module that uses the coordinate equivalence below; it is public only
so that those modules can name it. -/
@[instance_reducible] public noncomputable def setIndexedDividedPowerPolynomialCommRing :
    CommRing (setIndexedDividedPowerPolynomialAlgebra A W) :=
  (DividedPowerAlgebra.ringCon (coefficientDividedPowerRing A)
    (W →₀ ↑(coefficientDividedPowerRing A))).instCommRingQuotient

attribute [local instance low] setIndexedDividedPowerPolynomialCommRing

/-- The coefficient ring is an algebra over itself through the identity.  A `local instance` of
low priority, public so that the modules consuming the coordinate equivalence below can name
it. -/
@[instance_reducible] public noncomputable def coefficientDividedPowerRingAlgebra :
    Algebra A (↑(coefficientDividedPowerRing A)) :=
  (RingHom.id A).toAlgebra

attribute [local instance low] coefficientDividedPowerRingAlgebra

/-- The divided power polynomial algebra `A⟨x_w : w ∈ W⟩` is an `A`-algebra.  A `local instance`
of low priority, public so that the modules consuming the coordinate equivalence below can name
it. -/
@[instance_reducible] public noncomputable def setIndexedDividedPowerPolynomialAlgebra' :
    Algebra A (setIndexedDividedPowerPolynomialAlgebra A W) :=
  Algebra.compHom _ (RingHom.id A)

attribute [local instance low] setIndexedDividedPowerPolynomialAlgebra'

/-- The coefficient map `A → A⟨x_w : w ∈ W⟩` into the carrier of the divided power ring of
divided power polynomials.  It is the structure map of
`Crystalline.setIndexedDividedPowerPolynomialDividedPowerRingAlgebra`. -/
public noncomputable def indexedDividedPowerPolynomialCoefficientMap
    (A : Type u) [CommRing A] (W : Type w) : A →+*
      ↑(setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W) := by
  let R := coefficientDividedPowerRing A
  let P := setIndexedDividedPowerPolynomialAlgebra A W
  let q : ↑R →+* P :=
    (RingCon.mkₐ (↑R) (DividedPowerAlgebra.ringCon (↑R) (W →₀ ↑R))).toRingHom.comp
      (MvPolynomial.C : ↑R →+* MvPolynomial (ℕ × (W →₀ ↑R)) ↑R)
  let qStd : A →+* P := q.comp (RingHom.id A)
  change A →+* P
  exact qStd

/-- **The `A`-algebra structure on the divided power polynomial algebra `A⟨x_w : w ∈ W⟩`**, read
on the carrier of its divided power ring.  This is the algebra structure the module of divided
power differentials `Ω¹_{P/A,δ}` is taken relative to, so it is public: a public statement about
that module cannot be made without it.  It remains a `local instance` of low priority — a global
one would compete with `Algebra.id` on the coefficient ring — so a module using it must name it,
and the three instances above, in a `local instance low` attribute. -/
@[instance_reducible]
public noncomputable def setIndexedDividedPowerPolynomialDividedPowerRingAlgebra :
    Algebra A (↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W)) :=
  (indexedDividedPowerPolynomialCoefficientMap A W).toAlgebra

attribute [local instance low] setIndexedDividedPowerPolynomialDividedPowerRingAlgebra

@[instance_reducible] private noncomputable def indexedDividedPowerPolynomialFinsuppModule :
    Module (↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W))
      (W →₀ DividedPowerAlgebra (↑(coefficientDividedPowerRing A))
        (W →₀ ↑(coefficientDividedPowerRing A))) := by
  let P := DividedPowerAlgebra (↑(coefficientDividedPowerRing A))
    (W →₀ ↑(coefficientDividedPowerRing A))
  change Module P (W →₀ P)
  exact Finsupp.module W P

attribute [local instance low] indexedDividedPowerPolynomialFinsuppModule

@[instance_reducible] private noncomputable def indexedDividedPowerPolynomialFinsuppModuleOp :
    Module (↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W))ᵐᵒᵖ
      (W →₀ DividedPowerAlgebra (↑(coefficientDividedPowerRing A))
        (W →₀ ↑(coefficientDividedPowerRing A))) := by
  let P := DividedPowerAlgebra (↑(coefficientDividedPowerRing A))
    (W →₀ ↑(coefficientDividedPowerRing A))
  let f : Pᵐᵒᵖ →+* P :=
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := fun x y ↦ (mul_comm x.unop y.unop).symm
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change Module Pᵐᵒᵖ (W →₀ P)
  exact Module.compHom (W →₀ P) f

attribute [local instance low] indexedDividedPowerPolynomialFinsuppModuleOp

private theorem indexedDividedPowerPolynomialFinsuppCentral :
    IsCentralScalar (DividedPowerAlgebra (↑(coefficientDividedPowerRing A))
      (W →₀ ↑(coefficientDividedPowerRing A)))
      (W →₀ DividedPowerAlgebra (↑(coefficientDividedPowerRing A))
        (W →₀ ↑(coefficientDividedPowerRing A))) := ⟨by
  intro c m
  classical
  ext i
  simpa only [Finsupp.smul_apply] using op_smul_eq_smul c (m i)
⟩

attribute [local instance low] indexedDividedPowerPolynomialFinsuppCentral

/-- The coefficient map identifies the base ring with its image in the polynomial algebra. -/
public noncomputable def coefficientLinearEquiv :
    A ≃ₗ[A] LinearMap.range
      (Algebra.linearMap A (setIndexedDividedPowerPolynomialAlgebra A W)) :=
  LinearEquiv.ofInjective _ (by
    intro a b h
    have h' := congrArg (dividedPowerPolynomialAugmentation A W) h
    simpa using h')

/-- The image of `a` under `coefficientLinearEquiv` is the constant `algebraMap A _ a`. -/
@[simp] public theorem coefficientLinearEquiv_apply (a : A) :
    ((coefficientLinearEquiv A W a : LinearMap.range
      (Algebra.linearMap A (setIndexedDividedPowerPolynomialAlgebra A W))) :
      setIndexedDividedPowerPolynomialAlgebra A W) =
      algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W) a := by
  rfl

private def sqZeroIdeal {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (I : Ideal R) :
    Ideal (TrivSqZeroExt R M) :=
  Ideal.comap (TrivSqZeroExt.fstHom R R M).toRingHom I

private noncomputable def sqZeroDpow {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] {I : Ideal R} (hI : DividedPowers I)
    (n : ℕ) (x : TrivSqZeroExt R M) : TrivSqZeroExt R M := by
  classical
  exact match n with
  | 0 => if x.1 ∈ I then 1 else 0
  | n + 1 => (hI.dpow (n + 1) x.1, hI.dpow n x.1 • x.2)

private theorem sqZeroDpow_fst {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] {I : Ideal R}
    (hI : DividedPowers I) (n : ℕ) (x : TrivSqZeroExt R M) (hx : x.fst ∈ I) :
    (sqZeroDpow hI n x).fst = hI.dpow n x.fst := by
  change x.1 ∈ I at hx
  cases n with
  | zero =>
    simp only [sqZeroDpow, ite_eq_left hx, TrivSqZeroExt.fst_one]
    change 1 = hI.dpow 0 x.1
    exact (hI.dpow_zero hx).symm
  | succ n => rfl

private theorem sqZeroDpow_snd {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] {I : Ideal R}
    (hI : DividedPowers I) (n : ℕ) (x : TrivSqZeroExt R M) :
    (sqZeroDpow hI n x).snd = match n with
      | 0 => 0
      | n + 1 => hI.dpow n x.1 • x.2 := by
  classical
  cases n with
  | zero =>
    simp only [sqZeroDpow]
    split <;> simp
  | succ n => rfl

private theorem sqZeroDpow_snd_of_ne_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] {I : Ideal R}
    (hI : DividedPowers I) {n : ℕ} (hn : n ≠ 0) (x : TrivSqZeroExt R M) :
    (sqZeroDpow hI n x).snd = hI.dpow (n - 1) x.1 • x.2 := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n => rfl

private theorem match_pred {M : Type*} [Zero M] (f : ℕ → M) (n : ℕ) :
    (match n with | 0 => 0 | n + 1 => f n) = if n = 0 then 0 else f (n - 1) := by
  cases n <;> simp

private theorem antidiag_shift_left {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : ℕ × ℕ → M) :
    (∑ p ∈ Finset.antidiagonal (n + 1),
      (if p.1 = 0 then 0 else f (p.1 - 1, p.2))) =
      ∑ p ∈ Finset.antidiagonal n, f p := by
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp

private theorem antidiag_shift_right {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : ℕ × ℕ → M) :
    (∑ p ∈ Finset.antidiagonal (n + 1),
      (if p.2 = 0 then 0 else f (p.1, p.2 - 1))) =
      ∑ p ∈ Finset.antidiagonal n, f p := by
  calc
    _ = ∑ p ∈ Finset.antidiagonal (n + 1),
        (if p.1 = 0 then 0 else f (p.2, p.1 - 1)) := by
          simpa using (Finset.Nat.sum_antidiagonal_swap
            (f := fun p : ℕ × ℕ ↦ if p.1 = 0 then 0 else f (p.2, p.1 - 1)) (n := n + 1))
    _ = ∑ p ∈ Finset.antidiagonal n, f p := by
      calc
        _ = ∑ p ∈ Finset.antidiagonal n, f p.swap := by
          simpa [Prod.swap] using antidiag_shift_left n (fun p ↦ f p.swap)
        _ = _ := by
          simpa [Prod.swap] using (Finset.Nat.sum_antidiagonal_swap (f := f) (n := n))

private noncomputable def sqZeroDpow_has_structure {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] {I : Ideal R}
    (hI : DividedPowers I) : DividedPowers (sqZeroIdeal (R := R) (M := M) I) := by
  classical
  refine ⟨sqZeroDpow hI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x hx
    change x.1 ∉ I at hx
    cases n with
    | zero => simp [sqZeroDpow, hx]
    | succ n =>
      apply TrivSqZeroExt.ext
      · exact hI.dpow_null hx
      · simp [sqZeroDpow, hI.dpow_null hx]
  · intro x hx
    change x.1 ∈ I at hx
    simp [sqZeroDpow, hx]
  · intro x hx
    change x.1 ∈ I at hx
    apply TrivSqZeroExt.ext
    · change hI.dpow 1 x.1 = x.1
      exact hI.dpow_one hx
    · change hI.dpow 0 x.1 • x.2 = x.2
      simp [hI.dpow_zero hx]
  · intro n x hn hx
    change (sqZeroDpow hI n x).1 ∈ I
    cases n with
    | zero => omega
    | succ n =>
      change hI.dpow (n + 1) x.1 ∈ I
      exact hI.dpow_mem (by omega) hx
  · intro n x y hx hy
    change x.1 ∈ I at hx
    change y.1 ∈ I at hy
    have hxy : (x + y).1 ∈ I := by
      change x.1 + y.1 ∈ I
      exact I.add_mem hx hy
    cases n with
    | zero =>
      apply TrivSqZeroExt.ext
      · simp [sqZeroDpow, TrivSqZeroExt.fst, hxy, hx, hy]
      · simp [sqZeroDpow, TrivSqZeroExt.snd, hxy, hx, hy]
    | succ n =>
      apply TrivSqZeroExt.ext
      · change hI.dpow (n + 1) (x.1 + y.1) = _
        rw [hI.dpow_add hx hy]
        change _ = TrivSqZeroExt.fst
          (∑ k ∈ Finset.antidiagonal (n + 1),
            sqZeroDpow hI k.1 x * sqZeroDpow hI k.2 y)
        rw [TrivSqZeroExt.fst_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [TrivSqZeroExt.fst_mul, sqZeroDpow_fst hI k.1 x hx,
          sqZeroDpow_fst hI k.2 y hy]
        rfl
      · change hI.dpow n (x.1 + y.1) • (x.2 + y.2) =
          TrivSqZeroExt.snd
            (∑ k ∈ Finset.antidiagonal (n + 1),
              sqZeroDpow hI k.1 x * sqZeroDpow hI k.2 y)
        rw [TrivSqZeroExt.snd_sum]
        simp_rw [TrivSqZeroExt.snd_mul, sqZeroDpow_fst hI _ x hx,
          sqZeroDpow_fst hI _ y hy, sqZeroDpow_snd hI, match_pred]
        rw [hI.dpow_add hx hy, Finset.sum_smul]
        simp_rw [smul_add]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_comm]
        congr 1
        · simpa [TrivSqZeroExt.fst, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
            (antidiag_shift_right n (fun p ↦
              (hI.dpow p.1 x.1 * hI.dpow p.2 y.1) • y.2)).symm
        · simpa [TrivSqZeroExt.fst, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
            (antidiag_shift_left n (fun p ↦
              (hI.dpow p.1 x.1 * hI.dpow p.2 y.1) • x.2)).symm
  · intro n a x hx
    change x.1 ∈ I at hx
    have hax : (a * x).1 ∈ I := by
      change a.1 * x.1 ∈ I
      exact I.mul_mem_left _ hx
    cases n with
    | zero =>
      apply TrivSqZeroExt.ext <;> simp [sqZeroDpow, hax, hx]
    | succ n =>
      apply TrivSqZeroExt.ext
      · simp only [sqZeroDpow]
        exact hI.dpow_mul hx
      · have hcomm : a.snd <• a.fst = a.fst •> a.snd := by
          simp [op_smul_eq_smul]
        have hcoef : x.1 * hI.dpow n x.1 = (n + 1 : R) * hI.dpow (n + 1) x.1 := by
          simpa [hI.dpow_one hx, add_comm] using (hI.mul_dpow (m := 1) (n := n) hx)
        simp only [sqZeroDpow_snd, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_pow]
        rw [TrivSqZeroExt.snd_pow_of_smul_comm a (n + 1) hcomm]
        rw [sqZeroDpow_fst hI (n + 1) x hx]
        change hI.dpow n (a.fst * x.fst) •> (a.fst •> x.snd + a.snd <• x.fst) =
          a.fst ^ (n + 1) •> hI.dpow n x.fst •> x.snd +
            (n + 1) •> a.fst ^ (n + 1).pred •> a.snd <• hI.dpow (n + 1) x.fst
        have hdpow : hI.dpow n (a.fst * x.fst) = a.fst ^ n * hI.dpow n x.fst :=
          hI.dpow_mul (a := a.fst) hx
        rw [hdpow]
        simp only [op_smul_eq_smul, smul_add, smul_smul, pow_succ]
        have hcoef' : hI.dpow n x.fst * x.fst =
            (n + 1 : R) * hI.dpow (n + 1) x.fst := by
          simpa [TrivSqZeroExt.fst, mul_comm] using hcoef
        simp_rw [mul_assoc, hcoef']
        have hpred : (n + 1).pred = n := by
          rw [Nat.pred_eq_sub_one]
          omega
        rw [hpred]
        module
  · intro m n x hx
    change x.1 ∈ I at hx
    cases m with
    | zero =>
      simp [sqZeroDpow, hx]
    | succ m =>
      cases n with
      | zero =>
        have hzero : sqZeroDpow hI 0 x = 1 := by simp [sqZeroDpow, hx]
        rw [hzero, Nat.add_zero, Nat.choose_self, Nat.cast_one, mul_one, one_mul]
      | succ n =>
        apply TrivSqZeroExt.ext
        · change hI.dpow (m + 1) x.1 * hI.dpow (n + 1) x.1 =
            (Nat.choose (m + 1 + (n + 1)) (m + 1) : R) *
              hI.dpow (m + 1 + (n + 1)) x.1
          exact hI.mul_dpow hx
        · change (sqZeroDpow hI (m + 1) x * sqZeroDpow hI (n + 1) x).snd =
            ((Nat.choose (m + 1 + (n + 1)) (m + 1) : TrivSqZeroExt R M) *
              sqZeroDpow hI (m + 1 + (n + 1)) x).snd
          rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_mul]
          simp only [TrivSqZeroExt.fst_natCast, TrivSqZeroExt.snd_natCast]
          rw [sqZeroDpow_fst hI (m + 1) x hx, sqZeroDpow_fst hI (n + 1) x hx]
          simp only [Nat.add_one, sqZeroDpow_snd]
          simp only [op_smul_eq_smul, smul_smul]
          rw [show x.fst = x.1 from rfl]
          have h₁ : hI.dpow (m + 1) x.1 * hI.dpow n x.1 =
              (Nat.choose (m + 1 + n) (m + 1) : R) * hI.dpow (m + 1 + n) x.1 :=
            hI.mul_dpow hx
          have hsum : m + (n + 1) = m + 1 + n := by omega
          have h₂ : hI.dpow m x.1 * hI.dpow (n + 1) x.1 =
              (Nat.choose (m + (n + 1)) m : R) * hI.dpow (m + 1 + n) x.1 := by
            simpa only [hsum] using (hI.mul_dpow (m := m) (n := n + 1) hx)
          simp only [smul_zero, add_zero]
          rw [h₁]
          rw [show hI.dpow (n + 1) x.1 * hI.dpow m x.1 =
              hI.dpow m x.1 * hI.dpow (n + 1) x.1 by ring, h₂]
          have hchoose :
              (Nat.choose (m + 1 + (n + 1)) (m + 1) : R) =
                (Nat.choose (m + 1 + n) (m + 1) : R) +
                  (Nat.choose (m + (n + 1)) m : R) := by
            have hN : Nat.choose (m + 1 + (n + 1)) (m + 1) =
                Nat.choose (m + 1 + n) (m + 1) + Nat.choose (m + (n + 1)) m := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_comm] using
                (Nat.choose_succ_succ (m + n + 1) m)
            simpa using congrArg (fun k : ℕ => (k : R)) hN
          rw [← add_smul, ← add_mul, hchoose]
          rw [show m.succ.add n = m.succ + n by rfl]
  · intro m n x hn hx
    change x.1 ∈ I at hx
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
      have hnpos : n + 1 ≠ 0 := by omega
      have hmem : hI.dpow (n + 1) x.1 ∈ I := hI.dpow_mem hnpos hx
      cases m with
      | zero =>
        simp [sqZeroDpow, hx, hmem, Nat.uniformBell_zero_left]
      | succ m =>
        have hprod : (m + 1) * (n + 1) - 1 = m * (n + 1) + n := by
          rw [Nat.succ_mul]
          omega
        have htop : m * (n + 1) + (n + 1) - 1 = m * (n + 1) + n := by omega
        have hchoose : Nat.choose (m * (n + 1) + (n + 1) - 1) n =
            Nat.choose (m * (n + 1) + n) (m * (n + 1)) := by
          rw [htop]
          exact (Nat.choose_symm_add).symm
        have hbell : (Nat.uniformBell (m + 1) (n + 1) : R) =
            (Nat.choose (m * (n + 1) + n) (m * (n + 1)) : R) *
              (Nat.uniformBell m (n + 1) : R) := by
          have h := Nat.uniformBell_succ_left m (n + 1)
          rw [Nat.succ_sub_one, hchoose] at h
          simpa only [Nat.cast_mul] using congrArg (fun k : ℕ => (k : R)) h
        have hmul : hI.dpow (m * (n + 1)) x.1 * hI.dpow n x.1 =
            (Nat.choose (m * (n + 1) + n) (m * (n + 1)) : R) *
              hI.dpow (m * (n + 1) + n) x.1 := by
          simpa only [Nat.add_sub_cancel_right] using
            (hI.mul_dpow (m := m * (n + 1)) (n := n) hx)
        apply TrivSqZeroExt.ext
        · change hI.dpow (m + 1) (hI.dpow (n + 1) x.1) =
            (Nat.uniformBell (m + 1) (n + 1) : R) *
              hI.dpow ((m + 1) * (n + 1)) x.1
          exact hI.dpow_comp hnpos hx
        · change (sqZeroDpow hI (m + 1) (sqZeroDpow hI (n + 1) x)).snd =
            ((Nat.uniformBell (m + 1) (n + 1) : TrivSqZeroExt R M) *
              sqZeroDpow hI ((m + 1) * (n + 1)) x).snd
          simp only [Nat.add_one, sqZeroDpow_snd]
          have hfst : (sqZeroDpow hI (n + 1) x).1 = hI.dpow (n + 1) x.1 := rfl
          have hsnd : (sqZeroDpow hI (n + 1) x).2 = hI.dpow n x.1 •> x.2 := rfl
          rw [hfst, hsnd]
          rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_natCast,
            TrivSqZeroExt.snd_natCast]
          rw [sqZeroDpow_snd_of_ne_zero hI (by positivity) x]
          simp only [smul_zero, add_zero, smul_smul]
          rw [hI.dpow_comp hnpos hx, mul_assoc, hmul, hprod, hbell]
          congr 1; ring

private noncomputable def sqZeroDividedPowerRing {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    {I : Ideal R} (hI : DividedPowers I) : DividedPowerRing :=
  .of (TrivSqZeroExt R M) (sqZeroIdeal (R := R) (M := M) I)
    (sqZeroDpow_has_structure hI)

attribute [local implicit_reducible] sqZeroDividedPowerRing

/-- A divided-power derivation is the second coordinate of a map to the corresponding
square-zero extension. -/
private noncomputable def sqZeroDPMorphismOfDerivation
    {A R M : Type*} [CommRing A] [CommRing R]
    (S : DividedPowerRing) {fA : A →+* (↑S)}
    [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    [Module (↑S) M] {I : Ideal R}
    (hI : DividedPowers I)
    (f : ↑S →+* R) (hf : S.dividedPowers.IsDPMorphism hI f)
    (D : DividedPowerDerivation A S fA M)
    (hsmul : ∀ (c : ↑S) (m : M), c • m = f c • m) :
    S.dividedPowers.DPMorphism
      (sqZeroDpow_has_structure (R := R) (M := M) hI) := by
  let φ : ↑S →+* TrivSqZeroExt R M :=
    { toFun := fun c ↦ (f c, D c)
      map_one' := by
        apply TrivSqZeroExt.ext
        · simp
        · change D 1 = 0
          exact D.map_one_eq_zero
      map_mul' := by
        intro c d
        apply TrivSqZeroExt.ext
        · change f (c * d) = f c * f d
          exact map_mul f c d
        · change D (c * d) = f c •> D d + D c <• f d
          rw [D.leibniz, op_smul_eq_smul]
          rw [← hsmul c (D d), ← hsmul d (D c)]
      map_zero' := by
        apply TrivSqZeroExt.ext
        · simp
        · change D 0 = 0
          exact D.map_zero
      map_add' := by
        intro c d
        apply TrivSqZeroExt.ext
        · change f (c + d) = f c + f d
          exact map_add f c d
        · change D (c + d) = D c + D d
          exact D.map_add c d }
  have hφ : S.dividedPowers.IsDPMorphism
      (sqZeroDpow_has_structure (R := R) (M := M) hI) φ := by
    rw [DividedPowers.isDPMorphism_iff]
    refine ⟨?_, ?_⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change f x ∈ I
      exact hf.ideal_comp (Ideal.mem_map_of_mem _ hx)
    · intro n hn x hx
      apply TrivSqZeroExt.ext
      · change (sqZeroDpow hI n (f x, D x)).fst = f (S.dividedPowers.dpow n x)
        rw [sqZeroDpow_fst hI n (f x, D x)
          (hf.ideal_comp (Ideal.mem_map_of_mem _ hx))]
        exact hf.dpow_comp x hx
      · have hfx : f x ∈ I := hf.ideal_comp (Ideal.mem_map_of_mem _ hx)
        cases n with
        | zero =>
          let y : TrivSqZeroExt R M := (f x, D x)
          change (sqZeroDpow hI 0 y).snd = D (S.dividedPowers.dpow 0 x)
          rw [sqZeroDpow_snd hI 0 y, S.dividedPowers.dpow_zero hx, D.map_one_eq_zero]
        | succ n =>
          change (sqZeroDpow hI (n + 1) (f x, D x)).snd =
            D (S.dividedPowers.dpow (n + 1) x)
          rw [sqZeroDpow_snd_of_ne_zero hI (by omega) (f x, D x)]
          change hI.dpow n (f x) • D x = D (S.dividedPowers.dpow (n + 1) x)
          rw [hf.dpow_comp (n := n) x hx, D.map_dpow (n + 1) (by omega) x hx]
          simp only [Nat.succ_sub_one, hsmul]
  exact DividedPowers.DPMorphism.mk' hφ


private noncomputable def sqZeroDPMorphismToDerivation
    {A : Type*} [CommRing A] (S : DividedPowerRing) [Algebra A (↑S)]
    {M : Type*} [AddCommGroup M] [Module (↑S) M]
    [Module (↑S)ᵐᵒᵖ M] [IsCentralScalar (↑S) M]
    (φ : S.dividedPowers.DPMorphism
      (sqZeroDpow_has_structure (R := (↑S)) (M := M) S.dividedPowers))
    (hfst : ∀ x, (φ x).fst = x)
    (hbase : ∀ a : A, (φ (algebraMap A (↑S) a)).snd = 0) :
    DividedPowerDerivation A S (algebraMap A (↑S)) M := by
  let s : (↑S) →+ M :=
    { toFun := fun x ↦ (φ x).snd
      map_zero' := by
        change (φ.toRingHom 0).snd = 0
        rw [map_zero φ.toRingHom]
        rfl
      map_add' := by
        intro x y
        change (φ.toRingHom (x + y)).snd = (φ.toRingHom x).snd + (φ.toRingHom y).snd
        rw [map_add φ.toRingHom]
        rfl }
  refine ⟨
    { toFun := s
      map_add' := s.map_add
      map_smul' := map_zsmul s
      map_one_eq_zero' := by
        change (φ.toRingHom 1).snd = 0
        rw [map_one φ.toRingHom]
        rfl
      leibniz' := ?_ }, ?_, ?_⟩
  · intro x y
    change (φ.toRingHom (x * y)).snd = x •> (φ.toRingHom y).snd +
      y •> (φ.toRingHom x).snd
    have hxfirst : (φ.toRingHom x).fst = x := hfst x
    have hyfirst : (φ.toRingHom y).fst = y := hfst y
    rw [map_mul φ.toRingHom, TrivSqZeroExt.snd_mul, hxfirst, hyfirst]
    simp only [op_smul_eq_smul]
  · exact hbase
  · intro n hn x hx
    have h := φ.dpow_comp (n := n) x hx
    have hs := congrArg TrivSqZeroExt.snd h
    change (φ.toRingHom (S.dividedPowers.dpow n x)).snd =
      S.dividedPowers.dpow (n - 1) x • (φ.toRingHom x).snd
    rw [← hs]
    change (sqZeroDpow S.dividedPowers n (φ.toRingHom x)).snd = _
    rw [sqZeroDpow_snd_of_ne_zero S.dividedPowers (Nat.ne_of_gt hn)
      (φ.toRingHom x)]
    have hxfirst : (φ.toRingHom x).1 = x := by
      simpa [TrivSqZeroExt.fst] using hfst x
    simp only [TrivSqZeroExt.snd]
    rw [hxfirst]


private theorem setIndexedDividedPowerDerivation_ext
    {A : Type u} [CommRing A] (W : Type w)
    {M : Type*} [AddCommGroup M]
    [Module (↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W)) M]
    [Module (↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W))ᵐᵒᵖ M]
    [IsCentralScalar (↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W)) M]
    (fA : A →+* ↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W))
    (D E : DividedPowerDerivation A
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W) fA M)
    (hcoeff : ∀ a : A,
      D (setIndexedDividedPowerPolynomialCoefficientDPMorphism
        (coefficientDividedPowerRing A) W a) =
        E (setIndexedDividedPowerPolynomialCoefficientDPMorphism
          (coefficientDividedPowerRing A) W a))
    (hvar : ∀ i : W,
      D (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i) =
        E (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)) :
    D = E := by
  classical
  let P := setIndexedDividedPowerPolynomialAlgebra A W
  let : CommRing P :=
    (DividedPowerAlgebra.ringCon A (W →₀ A)).instCommRingQuotient
  let J := dividedPowerPolynomialIdeal (⊥ : Ideal A) W
  let hJ := polynomialDividedPowers A W
  let S := setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W
  let : Module P M := (inferInstance : Module
    (↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W)) M)
  let : Module Pᵐᵒᵖ M := (inferInstance : Module
    (↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W))ᵐᵒᵖ M)
  let : IsCentralScalar P M := (inferInstance : IsCentralScalar
    (↑(setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W)) M)
  let T := sqZeroDividedPowerRing
    (R := P) (M := M) hJ
  let jD := sqZeroDPMorphismOfDerivation
    (A := A) (R := P) (M := M) S hJ (RingHom.id P)
    (DividedPowers.DPMorphism.id hJ).isDPMorphism D (by intro c m; rfl)
  let jE := sqZeroDPMorphismOfDerivation
    (A := A) (R := P) (M := M) S hJ (RingHom.id P)
    (DividedPowers.DPMorphism.id hJ).isDPMorphism E (by intro c m; rfl)
  have hcoeff :
      jD.comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism
        (coefficientDividedPowerRing A) W) =
      jE.comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism
        (coefficientDividedPowerRing A) W) := by
    ext a
    · rfl
    · change D (setIndexedDividedPowerPolynomialCoefficientDPMorphism
        (coefficientDividedPowerRing A) W a) =
      E (setIndexedDividedPowerPolynomialCoefficientDPMorphism
        (coefficientDividedPowerRing A) W a)
      exact hcoeff a
  have hvar_mem (i : W) :
      dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i ∈ J :=
    variable_mem_polynomialIdeal (coefficientDividedPowerRing A) i
  have hunique :=
    existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial
      (coefficientDividedPowerRing A) W T
      (jD.comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism
        (coefficientDividedPowerRing A) W))
      (fun i ↦ ⟨(dividedPowerPolynomialVariable
        (coefficientDividedPowerRing A) i,
        D (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)),
        hvar_mem i⟩)
  obtain ⟨φ, hφ, hφ_unique⟩ := hunique
  have hjD : jD = φ := hφ_unique jD ⟨rfl, fun i ↦ by
    simp [jD, sqZeroDPMorphismOfDerivation]
    rfl⟩
  have hjE : jE = φ := hφ_unique jE ⟨hcoeff.symm, fun i ↦ by
    apply TrivSqZeroExt.ext
    · rfl
    · exact (hvar i).symm⟩
  apply DividedPowerDerivation.ext
  intro x
  exact congrArg (fun ψ : DividedPowers.DPMorphism hJ
    (sqZeroDpow_has_structure (R := P) (M := M) hJ) ↦ (ψ x).snd) (hjD.trans hjE.symm)

private theorem polynomialVariableDerivationData
    {A : Type u} [CommRing A] (W : Type w) :
    ∃ D : DividedPowerDerivation A
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W)
      (algebraMap A (↑(setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W)))
      (W →₀ DividedPowerAlgebra (↑(coefficientDividedPowerRing A))
        (W →₀ ↑(coefficientDividedPowerRing A))),
      (∀ a : A, D (setIndexedDividedPowerPolynomialCoefficientDPMorphism
        (coefficientDividedPowerRing A) W a) = 0) ∧
      ∀ i : W, D (dividedPowerPolynomialVariable
        (coefficientDividedPowerRing A) i) = Finsupp.single i 1 := by
  classical
  let R := coefficientDividedPowerRing A
  let S := setIndexedDividedPowerPolynomialDividedPowerRing R W
  let P : Type (max u w) := ↑S
  let J := dividedPowerPolynomialIdeal R.ideal W
  let hJ := S.dividedPowers
  let M := W →₀ P
  let q : ↑R →+* P :=
    (RingCon.mkₐ (↑R) (DividedPowerAlgebra.ringCon (↑R) (W →₀ ↑R))).toRingHom.comp
      (MvPolynomial.C : ↑R →+* MvPolynomial (ℕ × (W →₀ ↑R)) ↑R)
  let c : A →+* ↑R := RingHom.id A
  let qStd : A →+* P := q.comp c
  let qS := algebraMap A (↑S)
  let : Algebra A (↑R) := c.toAlgebra
  let T := sqZeroDividedPowerRing
    (R := P) (M := M) hJ
  have hvar_mem (i : W) : dividedPowerPolynomialVariable R i ∈ J :=
    variable_mem_polynomialIdeal R i
  let D0 : DividedPowerDerivation A S qS M := 0
  let j0 := sqZeroDPMorphismOfDerivation
    (A := A) (R := P) (M := M) S hJ (RingHom.id P)
    (DividedPowers.DPMorphism.id hJ).isDPMorphism D0 (by
      intro x m
      rfl)
  let k : W → T.ideal := fun i ↦
    ⟨(dividedPowerPolynomialVariable R i, Finsupp.single i 1), by
      change dividedPowerPolynomialVariable R i ∈ J
      exact hvar_mem i⟩
  have hu := existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial
    R W T
    (j0.comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism R W)) k
  let φ := Classical.choose hu
  have hφ := (Classical.choose_spec hu).1
  have hφ_unique := (Classical.choose_spec hu).2
  let fst : T.dividedPowers.DPMorphism hJ := by
    refine DividedPowers.DPMorphism.mk' (f := (TrivSqZeroExt.fstHom P P M).toRingHom) ?_
    rw [DividedPowers.isDPMorphism_iff]
    refine ⟨?_, ?_⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact hx
    · intro n hn x hx
      change hJ.dpow n x.fst = (sqZeroDpow hJ n x).fst
      exact (sqZeroDpow_fst hJ n x (Ideal.mem_comap.mp hx)).symm
  have hfstj0 : fst.comp j0 = DividedPowers.DPMorphism.id hJ := by
    ext x
    rfl
  have hφfst : fst.comp φ = DividedPowers.DPMorphism.id hJ := by
    let huni := existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial
      R W S (setIndexedDividedPowerPolynomialCoefficientDPMorphism R W)
      (fun i ↦ ⟨dividedPowerPolynomialVariable R i, hvar_mem i⟩)
    obtain ⟨ψ, hψ, hψ_unique⟩ := huni
    have hprop :
        (fst.comp φ).comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism R W) =
          setIndexedDividedPowerPolynomialCoefficientDPMorphism R W ∧
        ∀ i : W,
          (fst.comp φ) (dividedPowerPolynomialVariable R i) =
            (dividedPowerPolynomialVariable R i : S) := by
      constructor
      · ext a
        have h₁ := congrArg
          (fun f : R.dividedPowers.DPMorphism T.dividedPowers => f a) hφ.1
        have h₂ := congrArg
          (fun f : DividedPowers.DPMorphism hJ hJ =>
            f (setIndexedDividedPowerPolynomialCoefficientDPMorphism R W a)) hfstj0
        change fst (φ (setIndexedDividedPowerPolynomialCoefficientDPMorphism R W a)) =
          setIndexedDividedPowerPolynomialCoefficientDPMorphism R W a
        exact (congrArg TrivSqZeroExt.fst h₁).trans h₂
      · intro i
        have hv := hφ.2 i
        change fst (φ (dividedPowerPolynomialVariable R i)) =
          dividedPowerPolynomialVariable R i
        rw [hv]
        rfl
    have hpropId :
        (DividedPowers.DPMorphism.id hJ).comp
          (setIndexedDividedPowerPolynomialCoefficientDPMorphism R W) =
          setIndexedDividedPowerPolynomialCoefficientDPMorphism R W ∧
        ∀ i : W,
          (DividedPowers.DPMorphism.id hJ) (dividedPowerPolynomialVariable R i) =
            (dividedPowerPolynomialVariable R i : S) := by
      constructor
      · ext a
        rfl
      · intro i
        rfl
    exact (hψ_unique (fst.comp φ) hprop).trans
      (hψ_unique (DividedPowers.DPMorphism.id hJ) hpropId).symm
  have hbase (a : A) : (φ (qStd a)).snd = 0 := by
    have h := congrArg
      (fun f : R.dividedPowers.DPMorphism T.dividedPowers => f a) hφ.1
    have hmap : setIndexedDividedPowerPolynomialCoefficientDPMorphism R W a = qStd a := by
      change (q.comp c) a = qStd a
      rfl
    calc
      (φ (qStd a)).snd =
          (φ (setIndexedDividedPowerPolynomialCoefficientDPMorphism R W a)).snd := by
            rw [hmap]
      _ = (j0 (setIndexedDividedPowerPolynomialCoefficientDPMorphism R W a)).snd :=
        congrArg TrivSqZeroExt.snd h
      _ = 0 := rfl
  let D := sqZeroDPMorphismToDerivation
    S φ (by
      intro x
      have h := congrArg
        (fun f : S.dividedPowers.DPMorphism hJ => f x) hφfst
      change (φ x).fst = x
      exact h) hbase
  refine ⟨D, ?_, ?_⟩
  · intro a
    change (φ (setIndexedDividedPowerPolynomialCoefficientDPMorphism
      (coefficientDividedPowerRing A) W a)).snd = 0
    exact hbase a
  · intro i
    have hv := hφ.2 i
    change (φ (dividedPowerPolynomialVariable
      (coefficientDividedPowerRing A) i)).snd = Finsupp.single i 1
    rw [hv]
    rfl

end OrdinaryExactness

end Crystalline

end
