module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.DifferentIdeal
public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.DedekindCase
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# A finite map of nodal curves whose different is the unit ideal

Let `k` be a field, `A = k[x,y]/(xy)`, `B = k[u,v]/(uv)` and let `A → B` send `x ↦ uⁿ` and
`y ↦ vᵐ` with `n` and `m` prime to the characteristic of `k`.  Then `A_{x+y} → B_{x+y}` is
finite étale, so the Dedekind different of `A → B` is defined, and
`Trace_{L/K}(1) = (nx+my)/(x+y)` while `Trace_{L/K}(uⁱ) = Trace_{L/K}(vʲ) = 0` for
`1 ≤ i < n` and `1 ≤ j < m`.  Hence `1 ∈ L_{B/A}` exactly when `n` and `m` have the same image
in `k`, and in that case `L_{B/A} = B` and the Dedekind different is `B`.  The map is neither
flat nor unramified, so a unit different does not force either.

This file sets up the example and proves the statements about the map itself; the trace
values, the complementary module and the failure of flatness and unramifiedness are in the
sibling files `NodeExample.TraceValues`, `NodeExample.ComplementaryModule` and
`NodeExample.NotFlatNotUnramified`.

## Main definitions

* `Stacks.Discriminant.NodeExample.nodeRing` and
  `Stacks.Discriminant.NodeExample.targetNodeRing` present `k[x,y]/(xy)` and `k[u,v]/(uv)`.

## Main results

* `Stacks.Discriminant.NodeExample.exists_powerMap`: the branchwise power map exists.
* `Stacks.Discriminant.NodeExample.finite_away_node` and
  `Stacks.Discriminant.NodeExample.etale_away_node`: it is finite étale after inverting `x + y`.
* `Stacks.Discriminant.NodeExample.exists_dedekindDifferentSetup`: its Dedekind different is
  defined.

## Implementation notes

The source and the target use distinct index types, `Fin 2` and `Bool`, so that the two nodal
rings are distinct Lean types.  The map `A → B` is not defined but specified: every theorem
quantifies over a ring map with the prescribed values on `x`, `y` and `k`, and
`Stacks.Discriminant.NodeExample.exists_powerMap` shows one exists.  Likewise the hypotheses
making the Dedekind different available are the class
`Stacks.Discriminant.DedekindDifferentSetup`, over which the theorems quantify, and
`Stacks.Discriminant.NodeExample.exists_dedekindDifferentSetup` constructs one.

## References

* [Stacks Project, Tag 0BWP](https://stacks.math.columbia.edu/tag/0BWP)
* [Stacks Project, Tag 0BWM](https://stacks.math.columbia.edu/tag/0BWM)
* [Stacks Project, Tag 0BWN](https://stacks.math.columbia.edu/tag/0BWN)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Discriminant.NodeExample

universe u

variable (k : Type u) [Field k]

/-- The union of two affine lines meeting at the origin. -/
abbrev nodeRing :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span
    {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1}

/-- A second presentation of the node, with a distinct Lean type. -/
abbrev targetNodeRing :=
  MvPolynomial Bool k ⧸ Ideal.span
    {(MvPolynomial.X false : MvPolynomial Bool k) * MvPolynomial.X true}

/-- The first coordinate of the node. -/
def x : nodeRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The second coordinate of the node. -/
def y : nodeRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The first coordinate of the target node. -/
def u : targetNodeRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X false)

/-- The second coordinate of the target node. -/
def v : targetNodeRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X true)

lemma targetNode_uv_zero : u k * v k = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

lemma targetNode_power_relation (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    u k ^ n * v k ^ m = 0 := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  calc
    u k ^ n'.succ * v k ^ m'.succ =
        (u k ^ n' * u k) * (v k ^ m' * v k) := by
      simp only [pow_succ]
    _ = (u k ^ n' * v k ^ m') * (u k * v k) := by ac_rfl
    _ = 0 := by rw [targetNode_uv_zero, mul_zero]

private noncomputable def powerMapHom (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    nodeRing k →+* targetNodeRing k := by
  let g : MvPolynomial (Fin 2) k →+* targetNodeRing k :=
    MvPolynomial.eval₂Hom (algebraMap k (targetNodeRing k))
      (fun i => if i = 0 then u k ^ n else v k ^ m)
  refine Ideal.Quotient.lift
    (Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1}) g ?_
  intro p hp
  have hgen : g ((MvPolynomial.X 0 : MvPolynomial (Fin 2) k) *
      MvPolynomial.X 1) = 0 := by
    simp [g, targetNode_power_relation k n m hn hm]
  rw [Ideal.mem_span_singleton] at hp
  obtain ⟨q, rfl⟩ := hp
  simp [map_mul, hgen]

private lemma powerMapHom_eq_of_spec (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k,
      f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    f = powerMapHom k n m hn hm := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, powerMapHom, Ideal.Quotient.lift_mk,
      MvPolynomial.eval₂Hom_C]
    exact hk a
  · intro i
    fin_cases i
    · simpa [RingHom.comp_apply, powerMapHom, x, MvPolynomial.eval₂Hom_X'] using hx
    · simpa [RingHom.comp_apply, powerMapHom, y, MvPolynomial.eval₂Hom_X'] using hy

private lemma targetNode_adjoin_coordinates (f : nodeRing k →+* targetNodeRing k)
    (hk : ∀ a : k,
      f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
    Algebra.adjoin (nodeRing k) ({u k, v k} : Set (targetNodeRing k)) = ⊤ := by
  let : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
  apply top_unique
  intro b _
  refine Quotient.inductionOn' b ?_
  intro p
  change Ideal.Quotient.mk _ p ∈
    Algebra.adjoin (nodeRing k) ({u k, v k} : Set (targetNodeRing k))
  induction p using MvPolynomial.induction_on with
  | C a =>
      change algebraMap k (targetNodeRing k) a ∈ _
      rw [← hk a]
      change algebraMap (nodeRing k) (targetNodeRing k) (algebraMap k (nodeRing k) a) ∈ _
      exact (Algebra.adjoin (nodeRing k) ({u k, v k} : Set (targetNodeRing k))).algebraMap_mem _
  | add p q hp hq =>
      simpa only [map_add] using (Algebra.adjoin (nodeRing k)
        ({u k, v k} : Set (targetNodeRing k))).add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]
      apply (Algebra.adjoin (nodeRing k)
        ({u k, v k} : Set (targetNodeRing k))).mul_mem hp
      cases i
      · change u k ∈ Algebra.adjoin (nodeRing k) ({u k, v k} : Set _)
        exact Algebra.subset_adjoin (by simp)
      · change v k ∈ Algebra.adjoin (nodeRing k) ({u k, v k} : Set _)
        exact Algebra.subset_adjoin (by simp)

private lemma nodeMap_finite (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k,
      f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    f.Finite := by
  let A := nodeRing k
  let B := targetNodeRing k
  let : Algebra A B := f.toAlgebra
  let : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (hk a).symm)
  have hgen := targetNode_adjoin_coordinates k f hk
  have hu : IsIntegral A (u k) := by
    apply IsIntegral.of_pow hn
    rw [← hx]
    exact isIntegral_algebraMap
  have hv : IsIntegral A (v k) := by
    apply IsIntegral.of_pow hm
    rw [← hy]
    exact isIntegral_algebraMap
  have hI : Algebra.IsIntegral A (Algebra.adjoin A ({u k, v k} : Set B)) :=
    Algebra.IsIntegral.adjoin (R := A) (hS := by rintro z (rfl | rfl) <;> assumption)
  let : IsScalarTower A A B := ⟨fun r s z => by
    calc
      (r * s) • z = algebraMap A B (r * s) * z := by rw [Algebra.smul_def]
      _ = algebraMap A B r * (algebraMap A B s * z) := by rw [map_mul]; ac_rfl
      _ = r • (s • z) := by rw [Algebra.smul_def, Algebra.smul_def]⟩
  have hItop : Algebra.IsIntegral A B := by
    constructor
    intro b
    have hb : b ∈ Algebra.adjoin A ({u k, v k} : Set B) := by
      rw [hgen]
      trivial
    exact (hI.isIntegral ⟨b, hb⟩).map (Algebra.adjoin A ({u k, v k} : Set B)).val
  have hft : Algebra.FiniteType A B :=
    Algebra.FiniteType.of_restrictScalars_finiteType k A B
  exact (Algebra.finite_iff_isIntegral_and_finiteType).2 ⟨hItop, hft⟩

/-- Distinct indeterminates do not divide each other. -/
private lemma not_X_dvd_X {k σ : Type*} [Field k] {i j : σ} (hij : i ≠ j) :
    ¬ (MvPolynomial.X i : MvPolynomial σ k) ∣ MvPolynomial.X j :=
  fun h => hij (MvPolynomial.X_dvd_X.mp h)

lemma node_coordinate_syzygy (a b : nodeRing k)
    (h : x k * a + y k * b = 0) :
    ∃ c d : nodeRing k, a = y k * c ∧ b = x k * d := by
  classical
  let I := Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1}
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hmem : p * MvPolynomial.X 0 + q * MvPolynomial.X 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk I (p * MvPolynomial.X 0 + q * MvPolynomial.X 1) = 0
    change Ideal.Quotient.mk I (MvPolynomial.X 0) * Ideal.Quotient.mk I p +
      Ideal.Quotient.mk I (MvPolynomial.X 1) * Ideal.Quotient.mk I q = 0 at h
    rw [map_add, map_mul, map_mul]
    simpa only [mul_comm] using h
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨r, hr⟩ := hmem
  have hrel : p * MvPolynomial.X 0 + q * MvPolynomial.X 1 =
      r * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hr
  have hdivp : MvPolynomial.X 1 ∣ p * MvPolynomial.X 0 := by
    refine ⟨r * MvPolynomial.X 0 - q, ?_⟩
    calc
      p * MvPolynomial.X 0 =
          (p * MvPolynomial.X 0 + q * MvPolynomial.X 1) - q * MvPolynomial.X 1 := by ring
      _ = r * (MvPolynomial.X 0 * MvPolynomial.X 1) - q * MvPolynomial.X 1 := by
        rw [hrel]
      _ = MvPolynomial.X 1 * (r * MvPolynomial.X 0 - q) := by ring
  have hdivq : MvPolynomial.X 0 ∣ q * MvPolynomial.X 1 := by
    refine ⟨r * MvPolynomial.X 1 - p, ?_⟩
    calc
      q * MvPolynomial.X 1 =
          (p * MvPolynomial.X 0 + q * MvPolynomial.X 1) - p * MvPolynomial.X 0 := by ring
      _ = r * (MvPolynomial.X 0 * MvPolynomial.X 1) - p * MvPolynomial.X 0 := by
        rw [hrel]
      _ = MvPolynomial.X 0 * (r * MvPolynomial.X 1 - p) := by ring
  have hp : MvPolynomial.X 1 ∣ p :=
    (MvPolynomial.X_prime.dvd_mul.mp hdivp).resolve_right (not_X_dvd_X (by decide))
  have hq : MvPolynomial.X 0 ∣ q :=
    (MvPolynomial.X_prime.dvd_mul.mp hdivq).resolve_right (not_X_dvd_X (by decide))
  obtain ⟨c, rfl⟩ := hp
  obtain ⟨d, rfl⟩ := hq
  refine ⟨Ideal.Quotient.mk I c, Ideal.Quotient.mk I d, ?_, ?_⟩
  · change Ideal.Quotient.mk I (MvPolynomial.X 1 * c) =
      Ideal.Quotient.mk I (MvPolynomial.X 1) * Ideal.Quotient.mk I c
    simp only [map_mul]
  · change Ideal.Quotient.mk I (MvPolynomial.X 0 * d) =
      Ideal.Quotient.mk I (MvPolynomial.X 0) * Ideal.Quotient.mk I d
    simp only [map_mul]

/-- The branchwise power map, specified on the two coordinates. -/
@[stacks 0BWP "power map"]
theorem exists_powerMap (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∃ f : nodeRing k →+* targetNodeRing k,
      f (x k) = u k ^ n ∧ f (y k) = v k ^ m ∧
        ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a := by
  refine ⟨powerMapHom k n m hn hm, ?_, ?_, ?_⟩
  · simp [powerMapHom, x, MvPolynomial.eval₂Hom_X']
  · simp [powerMapHom, y, MvPolynomial.eval₂Hom_X']
  · intro a
    change (Ideal.Quotient.lift _ _ _) (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      Ideal.Quotient.mk _ (MvPolynomial.C a)
    rw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C, ← Ideal.Quotient.mk_algebraMap k
      (Ideal.span {(MvPolynomial.X false : MvPolynomial Bool k) * MvPolynomial.X true}) a]
    rfl

/-- A natural number that is a unit in a nontrivial ring is positive. -/
private lemma pos_of_isUnit_natCast {R : Type*} [Semiring R] [Nontrivial R] {n : ℕ}
    (h : IsUnit (n : R)) : 0 < n :=
  Nat.pos_of_ne_zero fun h' => h.ne_zero (by simp [h'])

/-- The localized branchwise power map is finite. -/
@[stacks 0BWP "finite localization"]
theorem finite_away_node
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI : Algebra (Localization.Away (x k + y k))
        (Localization.Away (f (x k + y k))) :=
      (IsLocalization.Away.map (Localization.Away (x k + y k))
        (Localization.Away (f (x k + y k))) f (x k + y k)).toAlgebra
    Module.Finite (Localization.Away (x k + y k))
      (Localization.Away (f (x k + y k))) := by
  exact RingHom.localization_away_map_finite (nodeRing k) (targetNodeRing k)
    (Localization.Away (x k + y k)) (Localization.Away (f (x k + y k))) f (x k + y k)
    (nodeMap_finite k n m (pos_of_isUnit_natCast hn) (pos_of_isUnit_natCast hm) f hx hy hk)

section

open Polynomial

private def powerEtalePair {R : Type*} [CommRing R] (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : R)) (a : R) : StandardEtalePair R where
  f := X ^ n - C a
  monic_f := monic_X_pow_sub_C a (Nat.ne_of_gt hn)
  g := X
  cond := by
    refine ⟨C (((hunit.unit⁻¹ : Rˣ) : R)) * X, 0, n, ?_⟩
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, mul_zero, add_zero]
    calc
      (C (n : R) * X ^ (n - 1)) * (C (((hunit.unit⁻¹ : Rˣ) : R)) * X) =
          C ((n : R) * ((hunit.unit⁻¹ : Rˣ) : R)) * X ^ ((n - 1) + 1) := by
        rw [map_mul, pow_succ]
        ring
      _ = X ^ n := by
        rw [Nat.sub_add_cancel hn]
        simp

def branchCoord (k : Type*) [Field k] (i : Bool) : targetNodeRing k :=
  if i then v k else u k

def baseCoord (k : Type*) [Field k] (i : Bool) : nodeRing k :=
  if i then y k else x k

lemma baseCoord_mul_not (k : Type*) [Field k] (i : Bool) :
    baseCoord k i * baseCoord k (!i) = 0 := by
  have h : x k * y k = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (by simp))
  cases i <;> simpa [baseCoord, mul_comm] using h

lemma branchCoord_mul_not (k : Type*) [Field k] (i : Bool) :
    branchCoord k i * branchCoord k (!i) = 0 := by
  cases i <;> simpa [branchCoord, mul_comm] using targetNode_uv_zero k

-- The explicit inverse maps cross polynomial quotients and localizations.
private lemma branch_etale (k : Type*) [Field k] (d : Bool → ℕ)
    (hd : ∀ i, IsUnit (d i : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hf : ∀ i, f (baseCoord k i) = branchCoord k i ^ d i)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a)
    (i : Bool) (T : Type*) [CommRing T] [Algebra (targetNodeRing k) T]
    [IsLocalization.Away (branchCoord k i) T] :
    ((algebraMap (targetNodeRing k) T).comp f).Etale := by
  let A := nodeRing k
  let B := targetNodeRing k
  let : Algebra A B := f.toAlgebra
  have : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := A) (A := B) fun a => (hk a).symm
  let : Algebra A T := ((algebraMap B T).comp f).toAlgebra
  have : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq
    (R := A) (S := B) (A := T) fun _ => rfl
  let n := d i
  have hdpos (j : Bool) : 0 < d j := pos_of_isUnit_natCast (hd j)
  have hn : 0 < n := hdpos i
  have hnA : IsUnit (n : A) := by simpa using (hd i).map (algebraMap k A)
  let P := powerEtalePair n hn hnA (baseCoord k i)
  have hroot : P.X ^ n = algebraMap A P.Ring (baseCoord k i) := by
    have h := P.hasMap_X.1
    change aeval P.X (X ^ n - C (baseCoord k i)) = 0 at h
    simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using h
  have hunit : IsUnit P.X := by
    have h := P.hasMap_X.2
    change IsUnit (aeval P.X X) at h
    simpa using h
  have hother : algebraMap A P.Ring (baseCoord k (!i)) = 0 := by
    apply (hunit.pow n).mul_left_cancel
    rw [mul_zero, hroot, ← map_mul, baseCoord_mul_not, map_zero]
  let g : B →+* P.Ring := Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom ((algebraMap A P.Ring).comp (algebraMap k A))
      (fun j => if j = i then P.X else 0)) (by
      intro p hp
      rw [Ideal.mem_span_singleton] at hp
      obtain ⟨q, rfl⟩ := hp
      cases i <;> simp)
  have hg (j : Bool) : g (branchCoord k j) = if j = i then P.X else 0 := by
    cases j <;> change (Ideal.Quotient.lift _ _ _) (Ideal.Quotient.mk _ _) = _
    all_goals rw [Ideal.Quotient.lift_mk]; simp
  have hgk (a : k) : g (algebraMap k B a) = algebraMap A P.Ring (algebraMap k A a) := by
    change (Ideal.Quotient.lift _ _ _) (Ideal.Quotient.mk _ (MvPolynomial.C a)) = _
    rw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]
    rfl
  have hgf : g.comp f = algebraMap A P.Ring := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change g (f (algebraMap k A a)) = _
      rw [hk, hgk]
      rfl
    · intro j
      fin_cases j
      · change g (f (baseCoord k false)) = algebraMap A P.Ring (baseCoord k false)
        rw [hf, map_pow, hg]
        cases i
        · simpa using hroot
        · simpa [(hdpos false).ne'] using hother.symm
      · change g (f (baseCoord k true)) = algebraMap A P.Ring (baseCoord k true)
        rw [hf, map_pow, hg]
        cases i
        · simpa [(hdpos true).ne'] using hother.symm
        · simpa using hroot
  have hug : IsUnit (g (branchCoord k i)) := by simpa [hg] using hunit
  let φ : T →ₐ[A] P.Ring :=
    { __ := IsLocalization.Away.lift (branchCoord k i) hug
      commutes' := by
        intro a
        change (IsLocalization.Away.lift (branchCoord k i) hug) (algebraMap B T (f a)) = _
        rw [IsLocalization.Away.lift_eq]
        exact RingHom.congr_fun hgf a }
  have hφ (b : B) : φ (algebraMap B T b) = g b :=
    IsLocalization.Away.lift_eq (branchCoord k i) hug b
  have hmap : P.HasMap (algebraMap B T (branchCoord k i)) := by
    constructor
    · simp only [P, powerEtalePair, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero]
      change algebraMap B T (branchCoord k i) ^ n = algebraMap B T (f (baseCoord k i))
      rw [hf, map_pow]
    · simpa [P, powerEtalePair] using IsLocalization.Away.algebraMap_isUnit (branchCoord k i)
  let ψ : P.Ring →ₐ[A] T := P.lift _ hmap
  have hφψ : φ.comp ψ = AlgHom.id A P.Ring := by
    apply P.hom_ext
    change φ (ψ P.X) = P.X
    simp only [ψ, StandardEtalePair.lift_X]
    rw [hφ, hg, ite_eq_left rfl]
  have hψφ : ψ.comp φ = AlgHom.id A T := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (branchCoord k i))
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change ψ (φ (algebraMap B T (algebraMap k B a))) = algebraMap B T (algebraMap k B a)
      rw [hφ, hgk]
      rw [ψ.commutes]
      change algebraMap B T (f (algebraMap k A a)) = algebraMap B T (algebraMap k B a)
      rw [hk]
    · intro j
      have hjdef : Ideal.Quotient.mk _ (MvPolynomial.X j) = branchCoord k j := by
        cases j <;> rfl
      change ψ (φ (algebraMap B T (Ideal.Quotient.mk _ (MvPolynomial.X j)))) =
        algebraMap B T (Ideal.Quotient.mk _ (MvPolynomial.X j))
      rw [hjdef, hφ, hg]
      by_cases hji : j = i
      · subst j
        simp [ψ]
      · have hj : j = !i := by cases j <;> cases i <;> simp_all
        rw [ite_eq_right hji, map_zero, hj]
        apply ((IsLocalization.Away.algebraMap_isUnit (branchCoord k i)).mul_left_cancel)
        rw [mul_zero, ← map_mul, branchCoord_mul_not]
        simp
  let e : P.Ring ≃ₐ[A] T :=
    { __ := ψ
      invFun := φ
      left_inv := fun a => AlgHom.congr_fun hφψ a
      right_inv := fun a => AlgHom.congr_fun hψφ a }
  rw [show ((algebraMap B T).comp f) = algebraMap A T from rfl, RingHom.etale_algebraMap]
  exact Algebra.Etale.of_equiv e

private lemma away_of_pow {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (r : R) (n : ℕ) (hn : 0 < n) [IsLocalization.Away (r ^ n) S] :
    IsLocalization.Away r S := by
  apply IsLocalization.Away.mk
  · have hu := IsLocalization.Away.algebraMap_isUnit (S := S) (r ^ n)
    rw [map_pow] at hu
    exact (isUnit_pow_iff (Nat.ne_of_gt hn)).mp hu
  · intro z
    obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (r ^ n) z
    exact ⟨n * m, a, by simpa [map_pow, pow_mul] using ha⟩
  · intro a b hab
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (r ^ n) hab
    exact ⟨n * m, by simpa [pow_mul] using hm⟩

private lemma mul_pow_zero {R : Type*} [CommRing R] {a b : R}
    (h : a * b = 0) (n : ℕ) (hn : 0 < n) : a * b ^ n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ', ← mul_assoc, h, zero_mul]

private lemma node_etale_localized (k : Type*) [Field k] (d : Bool → ℕ)
    (hd : ∀ i, IsUnit (d i : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hf : ∀ i, f (baseCoord k i) = branchCoord k i ^ d i)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    ((algebraMap (targetNodeRing k) (Localization.Away (f (x k + y k)))).comp f).Etale := by
  let A := nodeRing k
  let B := targetNodeRing k
  let s := f (x k + y k)
  let S := Localization.Away s
  let : Algebra A B := f.toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq
    (R := k) (S := A) (A := B) fun a => (hk a).symm
  have hdpos (i : Bool) : 0 < d i := pos_of_isUnit_natCast (hd i)
  have hs : s = branchCoord k false ^ d false + branchCoord k true ^ d true := by
    dsimp [s]
    rw [map_add]
    exact congrArg₂ (· + ·) (hf false) (hf true)
  let coords : Set S := Set.range fun i => algebraMap B S (branchCoord k i)
  have hspan : Ideal.span coords = ⊤ := by
    refine Ideal.eq_top_of_isUnit_mem _ ?_ (IsLocalization.Away.algebraMap_isUnit (S := S) s)
    have hmaps := congrArg (algebraMap B S) hs
    simp only [map_add, map_pow] at hmaps
    rw [hmaps]
    refine Ideal.add_mem _ ?_ ?_ <;>
      exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self _)) _ (hdpos _)
  apply RingHom.Etale.ofLocalizationSpanTarget _ coords hspan
  intro r
  obtain ⟨i, hi⟩ := r.property
  change algebraMap B S (branchCoord k i) = (r : S) at hi
  let U := Localization.Away (r : S)
  have : IsLocalization.Away (algebraMap B S (branchCoord k i)) U := by
    rw [hi]
    infer_instance
  have : IsLocalization.Away (branchCoord k i * s) U :=
    IsLocalization.Away.mul S U s (branchCoord k i)
  have hprod : branchCoord k i * s = branchCoord k i ^ (d i + 1) := by
    have hi : s = branchCoord k i ^ d i + branchCoord k (!i) ^ d (!i) := by
      cases i <;> simpa [add_comm] using hs
    rw [hi, mul_add, mul_pow_zero (branchCoord_mul_not k i) _ (hdpos (!i)), add_zero,
      pow_succ']
  have : IsLocalization.Away (branchCoord k i ^ (d i + 1)) U := hprod ▸ inferInstance
  have : IsLocalization.Away (branchCoord k i) U :=
    away_of_pow (branchCoord k i) (d i + 1) (Nat.succ_pos _)
  convert branch_etale k d hd f hf hk i U using 1

end

/-- The localized branchwise power map is étale. -/
@[stacks 0BWP "étale localization"]
theorem etale_away_node
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI : Algebra (Localization.Away (x k + y k))
        (Localization.Away (f (x k + y k))) :=
      (IsLocalization.Away.map (Localization.Away (x k + y k))
        (Localization.Away (f (x k + y k))) f (x k + y k)).toAlgebra
    Algebra.Etale (Localization.Away (x k + y k))
      (Localization.Away (f (x k + y k))) := by
  let A := nodeRing k
  let B := targetNodeRing k
  let R := Localization.Away (x k + y k)
  let S := Localization.Away (f (x k + y k))
  let : Algebra A B := f.toAlgebra
  let : Algebra R S := (IsLocalization.Away.map R S f (x k + y k)).toAlgebra
  have : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq
    (R := A) (S := R) (A := S) fun a => by
      change algebraMap B S (f a) = (IsLocalization.Away.map R S f (x k + y k)) (algebraMap A R a)
      exact (IsLocalization.map_eq (S := R) (Q := S) (g := f)
        (hy := show Submonoid.powers (x k + y k) ≤
          (Submonoid.powers (f (x k + y k))).comap f from by
            rintro _ ⟨j, rfl⟩
            exact ⟨j, by simp⟩) a).symm
  have : Algebra.Etale A S := by
    rw [← RingHom.etale_algebraMap]
    exact node_etale_localized k (fun i => if i then m else n)
      (fun i => by cases i <;> assumption) f (fun i => by cases i <;> assumption) hk
  have : Algebra.Etale A R := Algebra.Etale.of_isLocalizationAway (x k + y k)
  exact Algebra.Etale.of_restrictScalars A R S

lemma nodal_pow_sum_regular {k σ : Type*} [Field k]
    (i j : σ) (hij : i ≠ j) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X i : MvPolynomial σ k) * MvPolynomial.X j})
      ((MvPolynomial.X i) ^ n + (MvPolynomial.X j) ^ m) ∈
        nonZeroDivisors (MvPolynomial σ k ⧸ Ideal.span
          {(MvPolynomial.X i : MvPolynomial σ k) * MvPolynomial.X j}) := by
  classical
  let I := Ideal.span {(MvPolynomial.X i : MvPolynomial σ k) * MvPolynomial.X j}
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hdiv : (MvPolynomial.X i * MvPolynomial.X j) ∣
      p * ((MvPolynomial.X i) ^ n + (MvPolynomial.X j) ^ m) := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rwa [map_mul]
  have hnoti : ¬ (MvPolynomial.X i : MvPolynomial σ k) ∣
      (MvPolynomial.X i) ^ n + (MvPolynomial.X j) ^ m := by
    intro h
    have hpow : (MvPolynomial.X i : MvPolynomial σ k) ∣ (MvPolynomial.X j) ^ m :=
      (dvd_add_right (dvd_pow_self _ (Nat.ne_of_gt hn))).mp h
    exact not_X_dvd_X hij (MvPolynomial.X_prime.dvd_of_dvd_pow hpow)
  have hnotj : ¬ (MvPolynomial.X j : MvPolynomial σ k) ∣
      (MvPolynomial.X i) ^ n + (MvPolynomial.X j) ^ m := by
    intro h
    have hpow : (MvPolynomial.X j : MvPolynomial σ k) ∣ (MvPolynomial.X i) ^ n :=
      (dvd_add_left (dvd_pow_self _ (Nat.ne_of_gt hm))).mp h
    exact not_X_dvd_X hij.symm (MvPolynomial.X_prime.dvd_of_dvd_pow hpow)
  have hip : MvPolynomial.X i ∣ p :=
    (MvPolynomial.X_prime.dvd_mul.mp ((dvd_mul_right _ _).trans hdiv)).resolve_right hnoti
  have hjp : MvPolynomial.X j ∣ p :=
    (MvPolynomial.X_prime.dvd_mul.mp ((dvd_mul_left _ _).trans hdiv)).resolve_right hnotj
  obtain ⟨q, rfl⟩ := hip
  have hjq : MvPolynomial.X j ∣ q :=
    (MvPolynomial.X_prime.dvd_mul.mp hjp).resolve_left (not_X_dvd_X hij.symm)
  obtain ⟨r, rfl⟩ := hjq
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨r, by ring⟩)

private lemma flat_localization_preserves_nonZeroDivisors
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Flat A C] (hC : Function.Injective (algebraMap B C))
    (a : A) (ha : a ∈ nonZeroDivisors A) :
    algebraMap A B a ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  apply hC
  rw [map_zero]
  apply (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := C) ha)
  change a • algebraMap B C b = a • (0 : C)
  rw [smul_zero, Algebra.smul_def, IsScalarTower.algebraMap_apply A B C,
    ← map_mul, mul_comm, hb, map_zero]

private lemma etale_tensor_of_etale_away
    {A B K : Type*} [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] (s : A) (hs : IsUnit (algebraMap A K s))
    [Algebra.Etale A (Localization.Away (algebraMap A B s))] :
    Algebra.Etale K (K ⊗[A] B) := by
  let T := K ⊗[A] B
  let z : T := (1 : K) ⊗ₜ[A] algebraMap A B s
  have heq : z = algebraMap K T (algebraMap A K s) := by
    change (1 : K) ⊗ₜ[A] algebraMap A B s = algebraMap A K s ⊗ₜ[A] (1 : B)
    simpa only [Algebra.smul_def, mul_one] using
      (TensorProduct.smul_tmul (R := A) s (1 : K) (1 : B)).symm
  have hz : IsUnit z := heq ▸ hs.map (algebraMap K T)
  let e := IsLocalization.Away.tensorProductEquivTMulRight A K
    (algebraMap A B s) (Localization.Away (algebraMap A B s))
  have : Algebra.Etale K (Localization.Away z) := Algebra.Etale.of_equiv e
  exact Algebra.Etale.of_equiv
    ((IsLocalization.atUnit T (Localization.Away z) z hz).restrictScalars K).symm

/-- This finite map satisfies the standing hypotheses for its Dedekind different. -/
@[stacks 0BWP "Dedekind setup"]
theorem exists_dedekindDifferentSetup
    (n m : ℕ) (hn : IsUnit (n : k)) (hm : IsUnit (m : k))
    (f : nodeRing k →+* targetNodeRing k)
    (hx : f (x k) = u k ^ n) (hy : f (y k) = v k ^ m)
    (hk : ∀ a : k, f (algebraMap k (nodeRing k) a) = algebraMap k (targetNodeRing k) a) :
    letI : Algebra (nodeRing k) (targetNodeRing k) := f.toAlgebra
    Nonempty (DedekindDifferentSetup (nodeRing k) (targetNodeRing k)) := by
  let A := nodeRing k
  let B := targetNodeRing k
  let S := Localization.Away (f (x k + y k))
  let K := FractionRing A
  let : Algebra A B := f.toAlgebra
  have hnpos : 0 < n := pos_of_isUnit_natCast hn
  have hmpos : 0 < m := pos_of_isUnit_natCast hm
  have : Module.Finite A B := nodeMap_finite k n m hnpos hmpos f hx hy hk
  have : Algebra.Etale A S := by
    rw [← RingHom.etale_algebraMap]
    exact node_etale_localized k (fun i => if i then m else n)
      (fun i => by cases i <;> assumption) f (fun i => by cases i <;> assumption) hk
  have hregA : x k + y k ∈ nonZeroDivisors A := by
    simpa only [pow_one, map_add, x, y] using
      nodal_pow_sum_regular (k := k) (0 : Fin 2) 1 (by decide) 1 1 (by decide) (by decide)
  have hregB : f (x k + y k) ∈ nonZeroDivisors B := by
    rw [map_add, hx, hy]
    simpa only [map_add, map_pow, u, v] using
      nodal_pow_sum_regular (k := k) false true (by decide) n m hnpos hmpos
  have hinj : Function.Injective (algebraMap B S) :=
    IsLocalization.injective S (Submonoid.powers_le.mpr hregB)
  have hpres (a : A) (ha : a ∈ nonZeroDivisors A) :
      algebraMap A B a ∈ nonZeroDivisors B :=
    flat_localization_preserves_nonZeroDivisors hinj a ha
  have : Algebra.Etale K (K ⊗[A] B) := etale_tensor_of_etale_away
    (x k + y k) (IsLocalization.map_units K ⟨x k + y k, hregA⟩)
  let : Algebra K (B ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.Etale K (B ⊗[A] K) :=
    Algebra.Etale.of_equiv (R := K) (A := K ⊗[A] B) (Algebra.TensorProduct.commRight A K B)
  exact ⟨{ maps_nonZeroDivisors := hpres }⟩

end Stacks.Discriminant.NodeExample

end
