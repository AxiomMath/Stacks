module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Ring.GeomSum
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.NilpotentMonodromyWeights
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Determinant

/-!
# Quasi-unipotence of local monodromy

Grothendieck's local monodromy theorem says that a continuous `ℓ`-adic representation of the
Galois group of a local field with finite residue field of characteristic `p ≠ ℓ` is
quasi-unipotent on inertia.  Its proof has a group-theoretic half (the representation factors,
on an open subgroup of inertia, through the `ℓ`-part `ℤ_ℓ(1)` of the tame quotient, on which
a Frobenius element acts by raising to the `q`-th power) and a linear-algebraic half, proved
here: an invertible endomorphism `A` conjugate to its own `q`-th power, `q ≥ 2`, has only roots
of unity as eigenvalues, so that a power of it is unipotent.

## Main results

* `Stacks.EtaleCohomology.isRoot_charpoly_pow_map`: if `z` is an eigenvalue of `A` (a root of
  its characteristic polynomial, read in any field), then `z ^ n` is one of `A ^ n`.
* `Stacks.EtaleCohomology.exists_pow_eq_one_of_mul_eq_pow_mul`: if `B * A = A ^ q * B` with `A`
  and `B` invertible and `q ≥ 2`, every eigenvalue of `A` is a root of unity.
* `Stacks.EtaleCohomology.exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul`: under the same
  hypotheses some positive power `A ^ m` is unipotent, `A ^ m - 1` being nilpotent.
* `Stacks.EtaleCohomology.nilEvalHom`: evaluation of a power series over `ℚ` at a nilpotent
  element of a `ℚ`-algebra, a ring homomorphism compatible with substitution
  (`Stacks.EtaleCohomology.nilEvalHom_subst`).
* `Stacks.EtaleCohomology.unipotentLog`: the logarithm of a unipotent element, inverse to
  `IsNilpotent.exp` (`Stacks.EtaleCohomology.exp_unipotentLog`,
  `Stacks.EtaleCohomology.unipotentLog_exp`), with `log (u ^ n) = n • log u`.
* `Stacks.EtaleCohomology.exists_monodromy_logarithm`: if `T * F = F * T ^ q` with `T`, `F`
  invertible and `q ≥ 2`, some `T ^ m` is unipotent and its logarithm `N` is nilpotent, has
  kernel the invariants of `T ^ m`, and satisfies `N F = q F N` — the monodromy operator that
  `Stacks.EtaleCohomology.exists_norm_sq_mul_pow_eq_of_monodromy` consumes.
* `Stacks.EtaleCohomology.unipotentLog_map_self` and
  `Stacks.EtaleCohomology.unipotentLog_dualMap_inv`: the logarithm of `u ⊗ u` is
  `N ⊗ 1 + 1 ⊗ N` and that of the contragredient `(u⁻¹)^∨` is `-N^∨`; with
  `Stacks.EtaleCohomology.unipotentLog_apply_eq_zero_iff` (the kernel of `log u` is the space of
  fixed vectors of `u`) they translate the hypotheses of the weight estimate into bounds on
  invariants.
* `Stacks.EtaleCohomology.exists_norm_sq_mul_pow_eq_of_tame_monodromy`: Weil II, 1.8.4, stated
  for the tame monodromy `T` itself: the eigenvalues of Frobenius on the invariants of `T` have
  absolute values `|q| ^ ((w - i) / 2)`, `i ∈ ℕ`, given the weak bounds on the invariants of
  `T ^ m ⊗ T ^ m` and of the contragredient.

## Implementation notes

The eigenvalues are the roots of the characteristic polynomial mapped along an arbitrary ring
homomorphism `φ : K →+* L`, as elsewhere in this chapter, where they are read in `ℂ`.  The
proof that they are roots of unity uses no splitting field: the finitely many roots are
permuted into themselves by `z ↦ z ^ q`, so two of the iterates `z ^ (q ^ i)` coincide.

The logarithm is defined by evaluating Mathlib's `PowerSeries.log` at the nilpotent `u - 1`
through its truncation; the identities `exp ∘ log = id` and `log ∘ exp = id` are the power
series identities `PowerSeries.subst_exp_log` and `PowerSeries.subst_log_exp_sub_one`
transported along this evaluation, which commutes with substitution of series without constant
term.

## References

* A. Grothendieck, appendix to J.-P. Serre and J. Tate, *Good reduction of abelian varieties*,
  Ann. of Math. 88 (1968).
* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.7.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

namespace Stacks.EtaleCohomology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The characteristic polynomial of a product of endomorphisms does not depend on the order of
the factors. -/
public theorem charpoly_mul_comm_end (f g : Module.End K V) :
    (f * g).charpoly = (g * f).charpoly := by
  let b := Module.Free.chooseBasis K V
  rw [← LinearMap.charpoly_toMatrix (f * g) b, ← LinearMap.charpoly_toMatrix (g * f) b,
    LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, Matrix.charpoly_mul_comm]

/-- If `z` is a root of the characteristic polynomial of `A`, read in `L` along `φ`, then
`z ^ n` is a root of that of `A ^ n`: `z ^ n - A ^ n` is divisible by `z - A`. -/
public theorem isRoot_charpoly_pow_map {L : Type*} [Field L] (φ : K →+* L) (A : Module.End K V)
    {z : L} (hz : (A.charpoly.map φ).IsRoot z) (n : ℕ) :
    ((A ^ n).charpoly.map φ).IsRoot (z ^ n) := by
  classical
  let b := Module.Free.chooseBasis K V
  set M := (LinearMap.toMatrix b b A).map φ with hMdef
  have hM : ∀ k : ℕ, (A ^ k).charpoly.map φ = (M ^ k).charpoly := fun k => by
    rw [← LinearMap.charpoly_toMatrix (A ^ k) b, ← LinearMap.toMatrix_pow, ← Matrix.charpoly_map,
      hMdef, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
  have h1 := hM 1
  rw [pow_one, pow_one] at h1
  rw [Polynomial.IsRoot, h1, Matrix.eval_charpoly] at hz
  rw [Polynomial.IsRoot, hM n, Matrix.eval_charpoly]
  have hcomm : Commute (Matrix.scalar _ z) M :=
    Matrix.scalar_commute z (fun _ => Commute.all _ _) M
  have hgeom := hcomm.geom_sum₂_mul n
  rw [show Matrix.scalar _ (z ^ n) = (Matrix.scalar _ z) ^ n from map_pow (Matrix.scalar _) z n,
    ← hgeom, Matrix.det_mul, hz, mul_zero]

/-- An invertible endomorphism has no zero eigenvalue, read along any `φ`. -/
public theorem not_isRoot_zero_charpoly_map_of_isUnit {L : Type*} [Field L] (φ : K →+* L)
    {A : Module.End K V} (hA : IsUnit A) : ¬ (A.charpoly.map φ).IsRoot 0 := by
  rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
    map_eq_zero]
  intro h0
  have hdet := LinearMap.det_eq_sign_charpoly_coeff A
  rw [h0, mul_zero] at hdet
  exact (LinearMap.isUnit_iff_isUnit_det A).1 hA |>.ne_zero hdet

/-- If `B * A = A ^ q * B` with `B` invertible, then `A` and `A ^ q` have the same
characteristic polynomial: `A ^ q = B A B⁻¹`. -/
public theorem charpoly_pow_eq_of_mul_eq_pow_mul {A B : Module.End K V} (hB : IsUnit B) {q : ℕ}
    (h : B * A = A ^ q * B) : (A ^ q).charpoly = A.charpoly := by
  obtain ⟨u, rfl⟩ := hB
  have hq : A ^ q = (u : Module.End K V) * (A * ↑u⁻¹) := by
    rw [← mul_assoc, h, mul_assoc, Units.mul_inv, mul_one]
  rw [hq, charpoly_mul_comm_end, mul_assoc, Units.inv_mul, mul_one]

/-- **The eigenvalues of local monodromy are roots of unity.**  If `A` and `B` are invertible
endomorphisms of a finite-dimensional vector space with `B * A = A ^ q * B` for some `q ≥ 2` —
`A` the image of a generator of tame inertia and `B` that of a Frobenius element, which acts on
tame inertia by raising to the power `q` — then every eigenvalue of `A`, read in any field
along any `φ`, is a root of unity. -/
public theorem exists_pow_eq_one_of_mul_eq_pow_mul {L : Type*} [Field L] (φ : K →+* L)
    {A B : Module.End K V} (hA : IsUnit A) (hB : IsUnit B) {q : ℕ} (hq : 2 ≤ q)
    (h : B * A = A ^ q * B) {z : L} (hz : (A.charpoly.map φ).IsRoot z) :
    ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  classical
  set P := A.charpoly.map φ with hP
  have hP0 : P ≠ 0 := (A.charpoly_monic.map φ).ne_zero
  have hstep : ∀ y : L, P.IsRoot y → P.IsRoot (y ^ q) := fun y hy => by
    have := isRoot_charpoly_pow_map φ A hy q
    rwa [charpoly_pow_eq_of_mul_eq_pow_mul hB h] at this
  have hiter : ∀ i : ℕ, P.IsRoot (z ^ (q ^ i)) := by
    intro i
    induction i with
    | zero => simpa using hz
    | succ i ih => rw [pow_succ, pow_mul]; exact hstep _ ih
  have hmem : ∀ i : ℕ, z ^ (q ^ i) ∈ P.roots.toFinset := fun i =>
    Multiset.mem_toFinset.2 ((Polynomial.mem_roots hP0).2 (hiter i))
  obtain ⟨i, j, hij, heq⟩ : ∃ i j : ℕ, i < j ∧ z ^ (q ^ i) = z ^ (q ^ j) := by
    by_contra hne
    push Not at hne
    have hinj : Function.Injective fun i : ℕ => (⟨z ^ (q ^ i), hmem i⟩ : P.roots.toFinset) := by
      intro i j hij'
      have hv : z ^ (q ^ i) = z ^ (q ^ j) := congrArg Subtype.val hij'
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · exact absurd hv (hne i j hlt)
      · rfl
      · exact absurd hv.symm (hne j i hgt)
    exact not_injective_infinite_finite _ hinj
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact not_isRoot_zero_charpoly_map_of_isUnit φ hA hz
  have hlt : q ^ i < q ^ j := Nat.pow_lt_pow_right (by omega) hij
  refine ⟨q ^ j - q ^ i, Nat.sub_pos_of_lt hlt, ?_⟩
  have hpow : z ^ (q ^ i) * z ^ (q ^ j - q ^ i) = z ^ (q ^ i) * 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, heq]
  exact mul_left_cancel₀ (pow_ne_zero _ hz0) hpow

/-- **Quasi-unipotence (the linear-algebraic half of Grothendieck's local monodromy
theorem).**  If `A` and `B` are invertible endomorphisms of a finite-dimensional vector space
with `B * A = A ^ q * B` for some `q ≥ 2`, then some positive power of `A` is unipotent:
`A ^ m - 1` is nilpotent. -/
public theorem exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul {A B : Module.End K V}
    (hA : IsUnit A) (hB : IsUnit B) {q : ℕ} (hq : 2 ≤ q) (h : B * A = A ^ q * B) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent (A ^ m - 1) := by
  classical
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  set P := A.charpoly.map φ with hP
  have hP0 : P ≠ 0 := (A.charpoly_monic.map φ).ne_zero
  have hord : ∀ z ∈ P.roots.toFinset, ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := fun z hz =>
    exists_pow_eq_one_of_mul_eq_pow_mul φ hA hB hq h
      ((Polynomial.mem_roots hP0).1 (Multiset.mem_toFinset.1 hz))
  choose! ord hordpos hordeq using hord
  set m := ∏ z ∈ P.roots.toFinset, ord z with hm
  have hmpos : 0 < m := Finset.prod_pos fun z hz => hordpos z hz
  have hzm : ∀ z ∈ P.roots, z ^ m = 1 := fun z hz => by
    have hz' := Multiset.mem_toFinset.2 hz
    obtain ⟨c, hc⟩ : ord z ∣ m := Finset.dvd_prod_of_mem _ hz'
    rw [hc, pow_mul, hordeq z hz', one_pow]
  refine ⟨m, hmpos, ?_⟩
  set d := Module.finrank K V
  have hcard : Multiset.card P.roots = P.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hdeg : P.natDegree = d := by
    rw [hP, Polynomial.natDegree_map, LinearMap.charpoly_natDegree]
  have hsplit : (P.roots.map fun a => X - C a).prod = P :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (A.charpoly_monic.map φ) hcard
  have hdvdL : P ∣ ((X ^ m - 1 : K[X]) ^ d).map φ := by
    rw [← hsplit, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, ← hdeg, ← hcard, ← Multiset.prod_replicate, ← Multiset.map_const']
    refine Multiset.prod_dvd_prod_of_dvd _ _ fun z hz => ?_
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, hzm z hz, sub_self]
  have hdvd : A.charpoly ∣ (X ^ m - 1 : K[X]) ^ d := (Polynomial.map_dvd_map' φ).1 hdvdL
  refine ⟨d, ?_⟩
  obtain ⟨c, hc⟩ := hdvd
  have := congrArg (Polynomial.aeval A) hc
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, map_pow,
    Polynomial.aeval_X, map_one] at this
  exact this

/-! ### Evaluating power series at nilpotent elements; the unipotent logarithm -/

section NilpotentEvaluation

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- A truncation to degree `< D` of a polynomial evaluates, at an element `x` with `x ^ D = 0`,
to the value of the polynomial itself. -/
public theorem aeval_trunc_coe_of_pow_eq_zero {x : A} {D : ℕ} (hx : x ^ D = 0) (p : ℚ[X]) :
    aeval x (PowerSeries.trunc D (p : PowerSeries ℚ)) = aeval x p := by
  obtain ⟨r, hr⟩ : (X : ℚ[X]) ^ D ∣ p - PowerSeries.trunc D (p : PowerSeries ℚ) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, ite_eq_left hd, Polynomial.coeff_coe,
      sub_self]
  have := congrArg (aeval x) hr
  rw [map_sub, map_mul, map_pow, aeval_X, hx, zero_mul, sub_eq_zero] at this
  exact this.symm

/-- Evaluation of power series over `ℚ` at an element `x` with `x ^ D = 0`, as a ring
homomorphism: the truncation to degree `< D`, evaluated at `x`. -/
public def nilEvalHom {x : A} {D : ℕ} (hx : x ^ D = 0) : PowerSeries ℚ →+* A where
  toFun f := aeval x (PowerSeries.trunc D f)
  map_one' := by
    have := aeval_trunc_coe_of_pow_eq_zero hx 1
    rw [Polynomial.coe_one] at this
    rw [this, map_one]
  map_mul' f g := by
    change aeval x (PowerSeries.trunc D (f * g)) =
      aeval x (PowerSeries.trunc D f) * aeval x (PowerSeries.trunc D g)
    rw [← PowerSeries.trunc_trunc_mul_trunc, ← Polynomial.coe_mul,
      aeval_trunc_coe_of_pow_eq_zero hx, map_mul]
  map_zero' := by simp only [map_zero]
  map_add' f g := by simp only [map_add]

/-- `nilEvalHom hx f` is the truncation of `f` to degree `< D`, evaluated at `x`. -/
public theorem nilEvalHom_apply {x : A} {D : ℕ} (hx : x ^ D = 0) (f : PowerSeries ℚ) :
    nilEvalHom hx f = aeval x (PowerSeries.trunc D f) := rfl

/-- On a polynomial, `nilEvalHom hx` is evaluation at `x`. -/
public theorem nilEvalHom_coe {x : A} {D : ℕ} (hx : x ^ D = 0) (p : ℚ[X]) :
    nilEvalHom hx (p : PowerSeries ℚ) = aeval x p :=
  aeval_trunc_coe_of_pow_eq_zero hx p

/-- `nilEvalHom hx` sends the variable `X` to `x`. -/
public theorem nilEvalHom_X {x : A} {D : ℕ} (hx : x ^ D = 0) :
    nilEvalHom hx PowerSeries.X = x := by
  have := nilEvalHom_coe hx Polynomial.X
  rwa [Polynomial.coe_X, aeval_X] at this

/-- The value at a nilpotent `x` of a power series without constant term is nilpotent, of
exponent at most that of `x`. -/
public theorem nilEvalHom_pow_eq_zero {x : A} {D : ℕ} (hx : x ^ D = 0) {g : PowerSeries ℚ}
    (hg : PowerSeries.constantCoeff g = 0) : (nilEvalHom hx g) ^ D = 0 := by
  obtain ⟨g', rfl⟩ := PowerSeries.X_dvd_iff.2 hg
  have hc : Commute x (nilEvalHom hx g') := by
    have := (Commute.all PowerSeries.X g').map (nilEvalHom hx)
    rwa [nilEvalHom_X] at this
  rw [map_mul, nilEvalHom_X, hc.mul_pow, hx, zero_mul]

/-- **Evaluation at a nilpotent element is compatible with substitution**: for `g` without
constant term, the value of `f ∘ g` at `x` is the value of `f` at the value of `g` at `x`. -/
public theorem nilEvalHom_subst {x : A} {D : ℕ} (hx : x ^ D = 0) {g : PowerSeries ℚ}
    (hg : PowerSeries.constantCoeff g = 0) (f : PowerSeries ℚ) :
    nilEvalHom hx (f.subst g) = nilEvalHom (nilEvalHom_pow_eq_zero hx hg) f := by
  have hs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  set Φ : PowerSeries ℚ →+* A :=
    (nilEvalHom hx).comp (PowerSeries.substAlgHom (S := ℚ) hs).toRingHom with hΦdef
  have hΦ : ∀ f, Φ f = nilEvalHom hx (f.subst g) := fun f => by
    simp only [hΦdef, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, PowerSeries.coe_substAlgHom]
  have hΦX : Φ PowerSeries.X = nilEvalHom hx g := by
    rw [hΦ, PowerSeries.subst_X hs]
  have hpoly : Φ.comp Polynomial.coeToPowerSeries.ringHom =
      (aeval (nilEvalHom hx g)).toRingHom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change ((Φ.comp Polynomial.coeToPowerSeries.ringHom).comp Polynomial.C) a =
        (((aeval (nilEvalHom hx g)).toRingHom).comp Polynomial.C) a
      rw [RingHom.ext_rat ((Φ.comp Polynomial.coeToPowerSeries.ringHom).comp Polynomial.C)
        (((aeval (nilEvalHom hx g)).toRingHom).comp Polynomial.C)]
    · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_X, hΦX, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rw [← hΦ, nilEvalHom_apply]
  conv_lhs => rw [PowerSeries.eq_X_pow_mul_shift_add_trunc D f]
  rw [map_add, map_mul, map_pow, hΦX, nilEvalHom_pow_eq_zero hx hg, zero_mul, zero_add]
  exact congrArg (fun φ : ℚ[X] →+* A => φ (PowerSeries.trunc D f)) hpoly

/-- The value at `x` of a power series without constant term is a multiple of `x`. -/
public theorem exists_nilEvalHom_eq_mul {x : A} {D : ℕ} (hx : x ^ D = 0) {g : PowerSeries ℚ}
    (hg : PowerSeries.constantCoeff g = 0) : ∃ w : A, nilEvalHom hx g = w * x := by
  obtain ⟨g', rfl⟩ := PowerSeries.X_dvd_iff.2 hg
  refine ⟨nilEvalHom hx g', ?_⟩
  rw [mul_comm, map_mul, nilEvalHom_X]

/-- The value of the exponential series at a nilpotent element is its nilpotent exponential. -/
public theorem exp_eq_nilEvalHom {x : A} {D : ℕ} (hx : x ^ D = 0) :
    IsNilpotent.exp x = nilEvalHom hx (PowerSeries.exp ℚ) := by
  rw [IsNilpotent.exp_eq_sum hx, nilEvalHom_apply, PowerSeries.trunc_apply, map_sum,
    Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_monomial, PowerSeries.coeff_exp, Algebra.smul_def, Algebra.algebraMap_self,
    RingHom.id_apply, one_div]

/-- The logarithm `log u = ∑_{n ≥ 1} (-1)^(n+1) (u - 1)^n / n` of an element `u` with `u - 1`
nilpotent, where the sum is finite. -/
public def unipotentLog (u : A) : A :=
  aeval (u - 1) (PowerSeries.trunc (nilpotencyClass (u - 1)) (PowerSeries.log ℚ))

/-- For any `D` with `(u - 1) ^ D = 0`, `unipotentLog u` is the logarithm series evaluated at
`u - 1` by `nilEvalHom`. -/
public theorem unipotentLog_eq {u : A} {D : ℕ} (hD : (u - 1) ^ D = 0) :
    unipotentLog u = nilEvalHom hD (PowerSeries.log ℚ) := by
  have hc : nilpotencyClass (u - 1) ≤ D := csInf_le' hD
  have hpc : (u - 1) ^ nilpotencyClass (u - 1) = 0 := pow_nilpotencyClass ⟨D, hD⟩
  rw [unipotentLog, nilEvalHom_apply, ← PowerSeries.trunc_trunc_of_le (PowerSeries.log ℚ) hc,
    aeval_trunc_coe_of_pow_eq_zero hpc]

/-- The logarithm of a unipotent element is nilpotent. -/
public theorem isNilpotent_unipotentLog {u : A} (hu : IsNilpotent (u - 1)) :
    IsNilpotent (unipotentLog u) := by
  obtain ⟨D, hD⟩ := hu
  exact ⟨D, by
    rw [unipotentLog_eq hD]; exact nilEvalHom_pow_eq_zero hD PowerSeries.constantCoeff_log⟩

/-- `exp (log u) = u` for unipotent `u`. -/
public theorem exp_unipotentLog {u : A} (hu : IsNilpotent (u - 1)) :
    IsNilpotent.exp (unipotentLog u) = u := by
  obtain ⟨D, hD⟩ := hu
  have hy := nilEvalHom_pow_eq_zero hD (PowerSeries.constantCoeff_log (A := ℚ))
  rw [unipotentLog_eq hD, exp_eq_nilEvalHom hy, ← nilEvalHom_subst hD PowerSeries.constantCoeff_log,
    PowerSeries.subst_exp_log, map_add, map_one, nilEvalHom_X, add_sub_cancel]

/-- `log (exp a) = a` for nilpotent `a`. -/
public theorem unipotentLog_exp {a : A} (ha : IsNilpotent a) :
    unipotentLog (IsNilpotent.exp a) = a := by
  obtain ⟨D, hD⟩ := ha
  have hg : PowerSeries.constantCoeff (PowerSeries.exp ℚ - 1) = 0 := by
    simp [PowerSeries.constantCoeff_exp]
  have he : IsNilpotent.exp a - 1 = nilEvalHom hD (PowerSeries.exp ℚ - 1) := by
    rw [map_sub, map_one, exp_eq_nilEvalHom hD]
  have hy := nilEvalHom_pow_eq_zero hD hg
  have hD' : (IsNilpotent.exp a - 1) ^ D = 0 := by rw [he]; exact hy
  rw [unipotentLog_eq hD', nilEvalHom_apply, he, ← nilEvalHom_apply hy, ← nilEvalHom_subst hD hg,
    PowerSeries.subst_log_exp_sub_one, nilEvalHom_X]

/-- `exp (n • a) = exp a ^ n` for nilpotent `a`. -/
public theorem exp_nsmul_of_isNilpotent {a : A} (ha : IsNilpotent a) (n : ℕ) :
    IsNilpotent.exp (n • a) = IsNilpotent.exp a ^ n := by
  induction n with
  | zero => simp [IsNilpotent.exp_zero]
  | succ n ih =>
    rw [succ_nsmul, IsNilpotent.exp_add_of_commute ((Commute.refl a).smul_left n) (ha.smul n) ha,
      ih, pow_succ]

/-- `log (u ^ n) = n • log u` for unipotent `u`. -/
public theorem unipotentLog_pow {u : A} (hu : IsNilpotent (u - 1)) (n : ℕ) :
    unipotentLog (u ^ n) = n • unipotentLog u := by
  have hL := isNilpotent_unipotentLog hu
  conv_lhs => rw [← exp_unipotentLog hu, ← exp_nsmul_of_isNilpotent hL]
  exact unipotentLog_exp (hL.smul n)

/-- If `a * F = F * b`, then `p(a) * F = F * p(b)` for every polynomial `p`. -/
public theorem aeval_mul_eq_mul_aeval {a b F : A} (h : a * F = F * b) (p : ℚ[X]) :
    aeval a p * F = F * aeval b p := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add, map_add, add_mul, mul_add, hp, hr]
  | monomial n c =>
    have hpow : a ^ n * F = F * b ^ n := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, ← pow_succ]
    rw [aeval_monomial, aeval_monomial, mul_assoc, hpow, ← mul_assoc, Algebra.commutes,
      mul_assoc]

/-- **The logarithm of unipotent monodromy.**  If `u` is unipotent and `u * F = F * u ^ q`
(`F` a geometric Frobenius, `u` a unipotent local monodromy operator, so that
`F⁻¹ u F = u ^ q`), then its logarithm `N = log u` satisfies `N F = q F N`. -/
public theorem unipotentLog_mul_eq_nsmul_mul {u F : A} (hu : IsNilpotent (u - 1)) {q : ℕ}
    (h : u * F = F * u ^ q) : unipotentLog u * F = q • (F * unipotentLog u) := by
  have hq : IsNilpotent (u ^ q - 1) := by
    rw [← exp_unipotentLog hu, ← exp_nsmul_of_isNilpotent (isNilpotent_unipotentLog hu)]
    exact IsNilpotent.isNilpotent_exp_sub_one ((isNilpotent_unipotentLog hu).smul q)
  obtain ⟨D, hD⟩ := hu
  obtain ⟨D', hD'⟩ := hq
  have hE : (u - 1) ^ (D + D') = 0 := pow_eq_zero_of_le (by omega) hD
  have hE' : (u ^ q - 1) ^ (D + D') = 0 := pow_eq_zero_of_le (by omega) hD'
  have h1 : (u - 1) * F = F * (u ^ q - 1) := by rw [sub_mul, mul_sub, h, one_mul, mul_one]
  have hlog := unipotentLog_pow ⟨D, hD⟩ q
  rw [unipotentLog_eq hE', unipotentLog_eq hE] at hlog
  rw [unipotentLog_eq hE, nilEvalHom_apply, aeval_mul_eq_mul_aeval h1, ← nilEvalHom_apply hE',
    hlog, mul_smul_comm, nilEvalHom_apply]

/-- If `T * F = F * T ^ q` and `T ^ m` is unipotent, the logarithm `N` of `T ^ m` satisfies
`N F = q F N`. -/
private theorem unipotentLog_pow_mul_eq_nsmul_mul {T F : A} {m q : ℕ}
    (hnil : IsNilpotent (T ^ m - 1)) (h : T * F = F * T ^ q) :
    unipotentLog (T ^ m) * F = q • (F * unipotentLog (T ^ m)) := by
  have hu : T ^ m * F = F * (T ^ m) ^ q := by
    have hs : SemiconjBy F ((T ^ q) ^ m) (T ^ m) := SemiconjBy.pow_right h.symm m
    rw [← pow_mul, mul_comm m q, pow_mul]
    exact hs.symm
  exact unipotentLog_mul_eq_nsmul_mul hnil hu

end NilpotentEvaluation

/-! ### Grothendieck's local monodromy theorem, linear-algebraic form -/

section Monodromy

variable [CharZero K]

/-- The `ℚ`-algebra structure of the endomorphisms of a vector space over a field of
characteristic zero, through `ℚ → K`; used locally to take logarithms of unipotent
endomorphisms. -/
@[instance_reducible]
public def endRatAlgebra (W : Type*) [AddCommGroup W] [Module K W] :
    Algebra ℚ (Module.End K W) :=
  Algebra.compHom _ (algebraMap ℚ K)

omit [CharZero K] in
/-- The logarithm of a unipotent endomorphism kills exactly its fixed vectors. -/
public theorem unipotentLog_apply_eq_zero_iff {W : Type*} [AddCommGroup W] [Module K W]
    [Algebra ℚ (Module.End K W)] {u : Module.End K W} (hu : IsNilpotent (u - 1)) (v : W) :
    unipotentLog u v = 0 ↔ u v = v := by
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨k, hk⟩ := isNilpotent_unipotentLog hu
    obtain ⟨w, hw⟩ := exists_nilEvalHom_eq_mul hk
      (g := PowerSeries.exp ℚ - 1) (by simp [PowerSeries.constantCoeff_exp])
    have he : u - 1 = nilEvalHom hk (PowerSeries.exp ℚ - 1) := by
      rw [map_sub, map_one, ← exp_eq_nilEvalHom hk, exp_unipotentLog hu]
    have := congrArg (fun φ : Module.End K W => φ v) (he.trans hw)
    simp only [LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, hv,
      map_zero] at this
    exact sub_eq_zero.1 this
  · obtain ⟨D, hD⟩ := hu
    obtain ⟨w, hw⟩ := exists_nilEvalHom_eq_mul hD PowerSeries.constantCoeff_log
    rw [unipotentLog_eq hD, hw, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hv, sub_self, map_zero]

/-- `f ↦ f ⊗ 1` as a ring homomorphism. -/
public def rTensorRingHom (W : Type*) [AddCommGroup W] [Module K W] :
    Module.End K V →+* Module.End K (V ⊗[K] W) where
  toFun f := f.rTensor W
  map_one' := LinearMap.rTensor_id W V
  map_mul' f g := LinearMap.rTensor_mul W f g
  map_zero' := LinearMap.rTensor_zero W
  map_add' f g := LinearMap.rTensor_add W f g

/-- `f ↦ 1 ⊗ f` as a ring homomorphism. -/
public def lTensorRingHom (W : Type*) [AddCommGroup W] [Module K W] :
    Module.End K V →+* Module.End K (W ⊗[K] V) where
  toFun f := f.lTensor W
  map_one' := LinearMap.lTensor_id W V
  map_mul' f g := LinearMap.lTensor_mul W f g
  map_zero' := LinearMap.lTensor_zero W
  map_add' f g := LinearMap.lTensor_add W f g

omit [FiniteDimensional K V] [CharZero K] in
/-- **The logarithm of `u ⊗ u` is `N ⊗ 1 + 1 ⊗ N`**, `N` the logarithm of the unipotent `u`;
and `u ⊗ u` is unipotent. -/
public theorem unipotentLog_map_self [Algebra ℚ (Module.End K V)]
    [Algebra ℚ (Module.End K (V ⊗[K] V))] {u : Module.End K V} (hu : IsNilpotent (u - 1)) :
    IsNilpotent (TensorProduct.map u u - 1) ∧
      unipotentLog (TensorProduct.map u u) =
        (unipotentLog u).rTensor V + (unipotentLog u).lTensor V := by
  set N := unipotentLog u
  have hN : IsNilpotent N := isNilpotent_unipotentLog hu
  have hr : IsNilpotent (N.rTensor V) := hN.map (rTensorRingHom V)
  have hl : IsNilpotent (N.lTensor V) := hN.map (lTensorRingHom V)
  have hc : Commute (N.rTensor V) (N.lTensor V) := by
    change (N.rTensor V).comp (N.lTensor V) = (N.lTensor V).comp (N.rTensor V)
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hmap : TensorProduct.map u u = IsNilpotent.exp (N.rTensor V + N.lTensor V) := by
    rw [IsNilpotent.exp_add_of_commute hc hr hl]
    have h1 : IsNilpotent.exp (N.rTensor V) = u.rTensor V := by
      rw [show N.rTensor V = rTensorRingHom V N from rfl, ← IsNilpotent.map_exp hN,
        exp_unipotentLog hu]
      rfl
    have h2 : IsNilpotent.exp (N.lTensor V) = u.lTensor V := by
      rw [show N.lTensor V = lTensorRingHom V N from rfl, ← IsNilpotent.map_exp hN,
        exp_unipotentLog hu]
      rfl
    rw [h1, h2]
    exact (LinearMap.rTensor_comp_lTensor (M := V) (N := V) u u).symm
  have hs : IsNilpotent (N.rTensor V + N.lTensor V) := hc.isNilpotent_add hr hl
  refine ⟨hmap ▸ IsNilpotent.isNilpotent_exp_sub_one hs, ?_⟩
  rw [hmap, unipotentLog_exp hs]

omit [CharZero K] in
/-- The transpose of a power is the power of the transpose. -/
public theorem dualMap_pow {W : Type*} [AddCommGroup W] [Module K W] (f : Module.End K W)
    (n : ℕ) : (f ^ n).dualMap = f.dualMap ^ n := by
  induction n with
  | zero => exact LinearMap.dualMap_id
  | succ n ih =>
    rw [pow_succ, pow_succ', ← ih]
    exact (LinearMap.dualMap_comp_dualMap f (f ^ n)).symm

omit [FiniteDimensional K V] in
/-- **The logarithm of the contragredient of a unipotent `u` is `-N^∨`**, `N = log u`; and the
contragredient `(u⁻¹)^∨` is unipotent. -/
public theorem unipotentLog_dualMap_inv [Algebra ℚ (Module.End K V)] {u u' : Module.End K V}
    (hu : IsNilpotent (u - 1)) (hu' : u' * u = 1) :
    IsNilpotent (u'.dualMap - 1) ∧ unipotentLog u'.dualMap = -(unipotentLog u).dualMap := by
  set N := unipotentLog u
  have hN : IsNilpotent N := isNilpotent_unipotentLog hu
  have hinv : u' = IsNilpotent.exp (-N) := by
    calc u' = u' * (u * IsNilpotent.exp (-N)) := by
          rw [← exp_unipotentLog hu, IsNilpotent.exp_mul_exp_neg_self hN, mul_one]
      _ = IsNilpotent.exp (-N) := by rw [← mul_assoc, hu', one_mul]
  obtain ⟨k, hk⟩ := hN
  have hnegd : (-N).dualMap = -N.dualMap := by
    rw [LinearMap.dualMap_def, map_neg, ← LinearMap.dualMap_def]
  have hk' : (-N.dualMap) ^ k = 0 := by
    rw [← hnegd, ← dualMap_pow, neg_pow, hk, mul_zero, LinearMap.dualMap_def, map_zero]
  have hkN : (-N) ^ k = 0 := by rw [neg_pow, hk, mul_zero]
  have hdual : u'.dualMap = IsNilpotent.exp (-N.dualMap) := by
    rw [hinv, IsNilpotent.exp_eq_sum hkN, IsNilpotent.exp_eq_sum hk', LinearMap.dualMap_def,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_rat_smul, ← LinearMap.dualMap_def, dualMap_pow, hnegd]
  have hs : IsNilpotent (-N.dualMap) := ⟨k, hk'⟩
  refine ⟨hdual ▸ IsNilpotent.isNilpotent_exp_sub_one hs, ?_⟩
  rw [hdual]
  convert unipotentLog_exp (A := Module.End K (Module.Dual K V)) hs using 3

/-- If `G * F = 1 = F * G` and `T * F = F * T ^ q`, then `G * T = T ^ q * G`. -/
private theorem inv_mul_eq_pow_mul_inv {M : Type*} [Monoid M] {T F G : M} {q : ℕ} (hGF : G * F = 1)
    (hFG : F * G = 1) (h : T * F = F * T ^ q) : G * T = T ^ q * G := by
  calc G * T = G * (T * F) * G := by rw [mul_assoc, mul_assoc, hFG, mul_one]
    _ = G * (F * T ^ q) * G := by rw [h]
    _ = T ^ q * G := by rw [← mul_assoc, hGF, one_mul]

/-- **Grothendieck's local monodromy theorem, linear-algebraic form.**  Let `T` and `F` be
invertible endomorphisms of a finite-dimensional vector space over a field of characteristic
zero with `T * F = F * T ^ q`, `q ≥ 2` — `T` the image of a topological generator of tame
inertia and `F` that of a geometric Frobenius, so that `F⁻¹ T F = T ^ q`.  Then there are
`m > 0` and a nilpotent `N` (the logarithm of the unipotent `T ^ m`) with `N F = q F N`, whose
kernel is the space of invariants of `T ^ m`.  This is the input `N` of the weight estimate
`Stacks.EtaleCohomology.exists_norm_sq_mul_pow_eq_of_monodromy` (Weil II, 1.8.4). -/
public theorem exists_monodromy_logarithm {T F : Module.End K V} (hT : IsUnit T)
    (hF : IsUnit F) {q : ℕ} (hq : 2 ≤ q) (h : T * F = F * T ^ q) :
    ∃ m : ℕ, 0 < m ∧ ∃ N : Module.End K V, IsNilpotent N ∧ N * F = (q : K) • (F * N) ∧
      ∀ v : V, N v = 0 ↔ (T ^ m) v = v := by
  let := endRatAlgebra (K := K) V
  obtain ⟨Fu, rfl⟩ := hF
  obtain ⟨m, hm, hnil⟩ := exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul hT Fu⁻¹.isUnit hq
    (inv_mul_eq_pow_mul_inv Fu.inv_mul Fu.mul_inv h)
  exact ⟨m, hm, unipotentLog (T ^ m), isNilpotent_unipotentLog hnil,
    (by rw [Nat.cast_smul_eq_nsmul]; exact unipotentLog_pow_mul_eq_nsmul_mul hnil h),
    unipotentLog_apply_eq_zero_iff hnil⟩

/-- **Inertia invariants of a pure local system are strongly mixed** (Weil II, Théorème 1.8.4,
in its linear-algebraic form).  Let `T` (the image of a generator of tame inertia) and `F` (a
geometric Frobenius) be invertible endomorphisms of a finite-dimensional vector space over a
field of characteristic zero, with inverses `S` and `G`, and `T * F = F * T ^ q`, `q ≥ 2`.
Suppose, for every `m > 0`, that every eigenvalue `c` of `F ⊗ F` on the invariants of
`T ^ m ⊗ T ^ m` (the local invariants of `ℱ ⊗ ℱ` after a finite extension) has `|ι c| ≤ Q`, and
every eigenvalue of the contragredient `G^∨ ⊗ G^∨` on the invariants of
`(S ^ m)^∨ ⊗ (S ^ m)^∨` has `|ι c| ≤ Q'`, where `Q Q' = 1`.  Then every eigenvalue `α` of `F` on
the invariants of `T` satisfies `|ι α|² |ι q|^i = Q` for a natural number `i`: with
`Q = q ^ w`, the invariants are mixed of the integer weights `w - i ≤ w`. -/
public theorem exists_norm_sq_mul_pow_eq_of_tame_monodromy (ι : K →+* ℂ)
    {T S F G : Module.End K V} (hST : S * T = 1) (hTS : T * S = 1) (hGF : G * F = 1)
    (hFG : F * G = 1) {q : ℕ} (hq : 2 ≤ q) (h : T * F = F * T ^ q) {Q Q' : ℝ}
    (hQQ' : Q * Q' = 1)
    (H : ∀ m : ℕ, 0 < m → ∀ (X : V ⊗[K] V) (c : K), X ≠ 0 →
      TensorProduct.map (T ^ m) (T ^ m) X = X → TensorProduct.map F F X = c • X → ‖ι c‖ ≤ Q)
    (H' : ∀ m : ℕ, 0 < m → ∀ (X : Module.Dual K V ⊗[K] Module.Dual K V) (c : K), X ≠ 0 →
      TensorProduct.map (S ^ m).dualMap (S ^ m).dualMap X = X →
        TensorProduct.map G.dualMap G.dualMap X = c • X → ‖ι c‖ ≤ Q')
    {v : V} {α : K} (hv0 : v ≠ 0) (hTv : T v = v) (hFv : F v = α • v) :
    ∃ i : ℕ, ‖ι α‖ ^ 2 * ‖ι (q : K)‖ ^ i = Q := by
  let := endRatAlgebra (K := K) V
  let := endRatAlgebra (K := K) (V ⊗[K] V)
  have hTu : IsUnit T := ⟨⟨T, S, hTS, hST⟩, rfl⟩
  have hGu : IsUnit G := ⟨⟨G, F, hGF, hFG⟩, rfl⟩
  obtain ⟨m, hm, hnil⟩ := exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul hTu hGu hq
    (inv_mul_eq_pow_mul_inv hGF hFG h)
  set N := unipotentLog (T ^ m)
  have hNF : N * F = (q : K) • (F * N) := by
    rw [Nat.cast_smul_eq_nsmul]; exact unipotentLog_pow_mul_eq_nsmul_mul hnil h
  have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpow : ∀ n : ℕ, (T ^ n) v = v := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, Module.End.mul_apply, hTv, ih]
  have hNv : N v = 0 := (unipotentLog_apply_eq_zero_iff hnil v).2 (hpow m)
  have hSm : S ^ m * T ^ m = 1 := by
    have hc : Commute S T := hST.trans hTS.symm
    rw [← hc.mul_pow, hST, one_pow]
  obtain ⟨htn, htlog⟩ := unipotentLog_map_self hnil
  obtain ⟨hdn, hdlog⟩ := unipotentLog_dualMap_inv hnil hSm
  obtain ⟨hddn, hddlog⟩ := unipotentLog_map_self hdn
  refine exists_norm_sq_mul_pow_eq_of_monodromy ι hQQ' hNF hq0 (isNilpotent_unipotentLog hnil)
    hGF hFG (fun X c hX hker hFX => ?_) (fun X c hX hker hFX => ?_) hv0 hNv hFv
  · rw [← htlog] at hker
    exact H m hm X c hX ((unipotentLog_apply_eq_zero_iff htn X).1 hker) hFX
  · rw [← hdlog, ← hddlog] at hker
    exact H' m hm X c hX ((unipotentLog_apply_eq_zero_iff hddn X).1 hker) hFX


end Monodromy

end Stacks.EtaleCohomology

end
