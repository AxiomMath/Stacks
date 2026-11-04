module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import StacksFrontier.LinearAlgebra.Matrix.CharSeriesTraceDetection

/-!
# The torsion hypothesis for group algebras over `ℤ/ℓ^M`

For a finite group `G`, the additive commutator quotient of the group algebra `ℤ/ℓ^M[G]` is free
over `ℤ/ℓ^M` on the conjugacy classes: the class sums `σ_c` kill commutators, and an element all
of whose class sums vanish is a sum of commutators. Hence if `k • [s] = 0` then every class sum of
`s` is divisible by `ℓ^(M - v_ℓ(k))`. This gives the torsion hypothesis `(H_N)` of
`Stacks.CharSeriesTraceDetection.TraceDetectionHypothesis` for any ring map `φ` out of `ℤ/ℓ^M[G]`
that kills `ℓ^a`, as soon as `M ≥ a + log_ℓ N`.

## Main results

* `Stacks.CharSeriesTraceDetection.traceDetectionHypothesis_zmod_monoidAlgebra`.
-/

@[expose] public noncomputable section

open CategoryTheory.FilteredDerived
open scoped BigOperators

universe u v

namespace Stacks.CharSeriesTraceDetection

/-! ### Sums of commutators -/

section Commutators

variable {R : Type u} [Ring R]

/-- An element of the additive commutator subgroup is a finite sum of commutators. -/
theorem exists_sum_commutators {x : R} (hx : x ∈ additiveCommutatorSubgroup R) :
    ∃ (J : ℕ) (a b : Fin J → R), x = ∑ j, (a j * b j - b j * a j) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    exact ⟨1, fun _ => a, fun _ => b, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨J, a, b, rfl⟩ := hx
    obtain ⟨J', a', b', rfl⟩ := hy
    refine ⟨J + J', Fin.append a a', Fin.append b b', ?_⟩
    rw [Fin.sum_univ_add]
    simp
  | neg x _ hx =>
    obtain ⟨J, a, b, rfl⟩ := hx
    exact ⟨J, b, a, by rw [← Finset.sum_neg_distrib]; simp⟩

/-- An element whose class in `R^♮` vanishes is a finite sum of commutators. -/
theorem exists_sum_commutators_of_q_eq_zero {x : R} (hx : q R x = 0) :
    ∃ (J : ℕ) (a b : Fin J → R), x = ∑ j, (a j * b j - b j * a j) :=
  exists_sum_commutators ((QuotientAddGroup.eq_zero_iff _).1 hx)

end Commutators

/-! ### Class sums in a group algebra -/

section ClassSums

variable {k₀ : Type u} [CommRing k₀] {G : Type v} [Group G] [Fintype G]

open Classical in
/-- The class sum `σ_c(s) = ∑_{g ∈ c} s(g)` of an element of the group algebra. -/
def classSum (c : ConjClasses G) : MonoidAlgebra k₀ G →+ k₀ where
  toFun s := ∑ g : G, if ConjClasses.mk g = c then s.coeff g else 0
  map_zero' := by simp
  map_add' s s' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> simp [MonoidAlgebra.coeff_add]

open Classical in
/-- The class sum `σ_c(s)` is the sum of the coefficients of `s` over the elements of `c`. -/
theorem classSum_apply (c : ConjClasses G) (s : MonoidAlgebra k₀ G) :
    classSum c s = ∑ g : G, if ConjClasses.mk g = c then s.coeff g else 0 := rfl

/-- The class sum of `r • g` is `r` if `g` lies in `c`, and `0` otherwise. -/
theorem classSum_single (c : ConjClasses G) (g : G) (r : k₀) [Decidable (ConjClasses.mk g = c)] :
    classSum c (MonoidAlgebra.single g r) = if ConjClasses.mk g = c then r else 0 := by
  classical
  rw [classSum_apply, Finset.sum_eq_single g]
  · simp [MonoidAlgebra.coeff_single]
  · intro h _ hh
    simp [MonoidAlgebra.coeff_single, Ne.symm hh]
  · simp

/-- A class sum takes the same value on `x * y` and on `y * x`. -/
theorem classSum_mul_comm (c : ConjClasses G) (x y : MonoidAlgebra k₀ G) :
    classSum c (x * y) = classSum c (y * x) := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp [add_mul, mul_add, hx, hx']
  | single g r =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp [add_mul, mul_add, hy, hy']
    | single h r' =>
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, classSum_single,
        classSum_single, mul_comm r r']
      have : ConjClasses.mk (g * h) = ConjClasses.mk (h * g) :=
        ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨g⁻¹, by group⟩)
      rw [this]

/-- The class sums factor through `R^♮`. -/
def classSumQuot (c : ConjClasses G) :
    AdditiveCommutatorQuotient (MonoidAlgebra k₀ G) →+ k₀ :=
  QuotientAddGroup.lift _ (classSum c) (by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      rw [AddMonoidHom.mem_ker, map_sub, classSum_mul_comm, sub_self]
    | zero => exact AddMonoidHom.mem_ker.2 (map_zero _)
    | add x y _ _ hx hy =>
      rw [AddMonoidHom.mem_ker] at hx hy ⊢
      rw [map_add, hx, hy, add_zero]
    | neg x _ hx =>
      rw [AddMonoidHom.mem_ker] at hx ⊢
      rw [map_neg, hx, neg_zero])

/-- On the class of `s` in `R^♮`, the factored class sum is the class sum of `s`. -/
theorem classSumQuot_q (c : ConjClasses G) (s : MonoidAlgebra k₀ G) :
    classSumQuot c (q _ s) = classSum c s := rfl

/-- A chosen representative of a conjugacy class. -/
def rep (c : ConjClasses G) : G := c.exists_rep.choose

omit [Fintype G] in
/-- The chosen representative of a conjugacy class lies in that class. -/
theorem mk_rep (c : ConjClasses G) : ConjClasses.mk (rep c) = c := c.exists_rep.choose_spec

omit [Fintype G] in
/-- Conjugate group elements with the same coefficient have the same class in `R^♮`. -/
theorem q_single_of_isConj {g g' : G} (h : IsConj g g') (r : k₀) :
    q (MonoidAlgebra k₀ G) (MonoidAlgebra.single g r) =
      q (MonoidAlgebra k₀ G) (MonoidAlgebra.single g' r) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [show MonoidAlgebra.single (c * g * c⁻¹) r = MonoidAlgebra.single c (1 : k₀) *
      (MonoidAlgebra.single g r * MonoidAlgebra.single c⁻¹ 1) by
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, one_mul, mul_one,
      mul_assoc], q_mul_comm, mul_assoc, MonoidAlgebra.single_mul_single, inv_mul_cancel,
    mul_one, MonoidAlgebra.single_mul_single, mul_one, mul_one]

omit [Fintype G] in
/-- In `R^♮`, a group element may be replaced by the chosen representative of its conjugacy
class. -/
theorem q_single_eq_q_single_rep (g : G) (r : k₀) :
    q (MonoidAlgebra k₀ G) (MonoidAlgebra.single g r) =
      q (MonoidAlgebra k₀ G) (MonoidAlgebra.single (rep (ConjClasses.mk g)) r) :=
  q_single_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.1 (mk_rep (ConjClasses.mk g)).symm) r

/-- An element of the group algebra all of whose class sums vanish is zero in `R^♮`. -/
theorem q_eq_zero_of_classSum (x : MonoidAlgebra k₀ G) (hx : ∀ c, classSum c x = 0) :
    q (MonoidAlgebra k₀ G) x = 0 := by
  classical
  have hx' : x = ∑ g : G, MonoidAlgebra.single g (x.coeff g) := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
    rw [Finsupp.sum_fintype]
    simp
  rw [hx', map_sum, Finset.sum_congr rfl fun g _ => q_single_eq_q_single_rep g _]
  rw [← Finset.sum_fiberwise_of_maps_to (g := ConjClasses.mk)
    (t := Finset.univ.image ConjClasses.mk)
    (fun g _ => Finset.mem_image_of_mem _ (Finset.mem_univ g))]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Finset.sum_congr rfl (g := fun g => q (MonoidAlgebra k₀ G)
    (MonoidAlgebra.single (rep c) (x.coeff g)))
    (fun g hg => by rw [(Finset.mem_filter.1 hg).2]), ← map_sum]
  rw [show (∑ g ∈ Finset.univ.filter (fun g => ConjClasses.mk g = c),
      MonoidAlgebra.single (rep c) (x.coeff g)) = MonoidAlgebra.single (rep c)
        (∑ g ∈ Finset.univ.filter (fun g => ConjClasses.mk g = c), x.coeff g) from
    (map_sum (MonoidAlgebra.singleAddHom (R := k₀) (rep c)) _ _).symm]
  have : ∑ g ∈ Finset.univ.filter (fun g => ConjClasses.mk g = c), x.coeff g = classSum c x := by
    rw [classSum_apply, Finset.sum_filter]
  rw [this, hx c, MonoidAlgebra.single_zero, map_zero]

end ClassSums

/-! ### Torsion in `ℤ/ℓ^M` -/

section ZModTorsion

/-- If `k • x = 0` in `ℤ/ℓ^M` then `x` is a multiple of `ℓ ^ (M - v_ℓ(k))`. -/
theorem exists_eq_pow_mul_of_nsmul_eq_zero {ℓ M k : ℕ} [hℓ : Fact ℓ.Prime] (hk : k ≠ 0)
    {x : ZMod (ℓ ^ M)} (h : k • x = 0) :
    ∃ y : ZMod (ℓ ^ M), x = (ℓ ^ (M - k.factorization ℓ) : ZMod (ℓ ^ M)) * y := by
  set v := k.factorization ℓ
  have hk' : ℓ ^ v * (k / ℓ ^ v) = k := Nat.ordProj_mul_ordCompl_eq_self k ℓ
  have hcop : Nat.Coprime ((k / ℓ ^ v)) (ℓ ^ M) :=
    Nat.Coprime.pow_right _ (Nat.coprime_ordCompl hℓ.out hk).symm
  have h1 : (ℓ ^ v : ZMod (ℓ ^ M)) * x = 0 := by
    have h' : (((k / ℓ ^ v) : ℕ) : ZMod (ℓ ^ M)) * ((ℓ ^ v : ZMod (ℓ ^ M)) * x) = 0 := by
      rw [← mul_assoc, ← Nat.cast_pow, ← Nat.cast_mul, mul_comm ((k / ℓ ^ v)), hk',
        ← nsmul_eq_mul, h]
    have hu := (ZMod.unitOfCoprime _ hcop).isUnit
    rw [ZMod.coe_unitOfCoprime] at hu
    exact (hu.mul_right_eq_zero).1 h'
  have : NeZero (ℓ ^ M) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  rcases le_or_gt v M with hvM | hvM
  · have h2 : ℓ ^ M ∣ ℓ ^ v * x.val := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id,
        Nat.cast_pow, h1]
    obtain ⟨y, hy⟩ : ℓ ^ (M - v) ∣ x.val := by
      have h2' : ℓ ^ v * ℓ ^ (M - v) ∣ ℓ ^ v * x.val := by
        rwa [← pow_add, Nat.add_sub_cancel' hvM]
      exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hℓ.out.pos _) h2'
    refine ⟨(y : ZMod (ℓ ^ M)), ?_⟩
    rw [← ZMod.natCast_zmod_val x, hy, Nat.cast_mul, Nat.cast_pow]
  · exact ⟨x, by rw [show M - v = 0 by omega, pow_zero, one_mul]⟩

end ZModTorsion

/-! ### The torsion hypothesis for `ℤ/ℓ^M[G]` -/

section GroupAlgebra

variable {G : Type v} [Group G] [Fintype G] {Λ : Type*} [CommRing Λ] {r : ℕ}

/-- **`(H_N)` for `ℤ/ℓ^M[G]`.** A ring map out of the group algebra `ℤ/ℓ^M[G]` to matrices over a
commutative ring in which `ℓ ^ a = 0` satisfies the torsion hypothesis `(H_N)` as soon as
`M ≥ a + log_ℓ N`. -/
theorem traceDetectionHypothesis_zmod_monoidAlgebra (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (M a N : ℕ)
    (φ : MonoidAlgebra (ZMod (ℓ ^ M)) G →+* Matrix (Fin r) (Fin r) Λ)
    (hΛ : (ℓ : Λ) ^ a = 0) (hM : a + Nat.log ℓ N ≤ M) :
    TraceDetectionHypothesis φ N := by
  classical
  intro k hk hkN s hks
  set v := k.factorization ℓ
  have hvN : v ≤ Nat.log ℓ N :=
    Nat.le_log_of_pow_le hℓ.out.one_lt ((Nat.le_of_dvd hk (Nat.ordProj_dvd k ℓ)).trans hkN)
  have hσ : ∀ c : ConjClasses G, k • classSum c s = 0 := fun c => by
    have := congrArg (classSumQuot c) hks
    rwa [map_nsmul, classSumQuot_q, map_zero] at this
  choose y hy using fun c => exists_eq_pow_mul_of_nsmul_eq_zero hk.ne' (hσ c)
  set e := M - v
  let t' : MonoidAlgebra (ZMod (ℓ ^ M)) G :=
    ∑ g : G, if g = rep (ConjClasses.mk g) then MonoidAlgebra.single g (y (ConjClasses.mk g))
      else 0
  let t : MonoidAlgebra (ZMod (ℓ ^ M)) G := (ℓ ^ e) • t'
  have hclass : ∀ c, classSum c t = classSum c s := by
    intro c
    rw [map_nsmul, hy c, map_sum]
    have : ∀ g : G, classSum c (if g = rep (ConjClasses.mk g) then
        MonoidAlgebra.single g (y (ConjClasses.mk g)) else 0) =
        if g = rep c then y c else 0 := by
      intro g
      split_ifs with h1 h2 h2
      · rw [classSum_single, if_pos (by rw [h2, mk_rep]), h2, mk_rep]
      · rw [classSum_single, if_neg]
        intro h3
        exact h2 (h3 ▸ h1)
      · exact absurd (h2 ▸ (mk_rep c).symm ▸ rfl : g = rep (ConjClasses.mk g)) h1
      · exact map_zero _
    rw [Finset.sum_congr rfl fun g _ => this g, Finset.sum_ite_eq' Finset.univ (rep c),
      if_pos (Finset.mem_univ _), nsmul_eq_mul, Nat.cast_pow]
  obtain ⟨J, a', b', hab⟩ := exists_sum_commutators_of_q_eq_zero
    (q_eq_zero_of_classSum (s - t) fun c => by rw [map_sub, hclass, sub_self])
  refine ⟨J, a', b', t, by rw [← hab, sub_add_cancel], ?_, fun i hi => ?_⟩
  · rw [map_nsmul, ← Nat.cast_smul_eq_nsmul Λ, Nat.cast_pow,
      show e = a + (e - a) by omega, pow_add, hΛ, zero_mul, zero_smul]
  · have hti : k • t ^ i = 0 := by
      rw [smul_pow, smul_smul]
      have hdvd : ℓ ^ M ∣ k * (ℓ ^ e) ^ i := by
        refine Dvd.dvd.trans ?_ (Nat.mul_dvd_mul (Nat.ordProj_dvd k ℓ) dvd_rfl)
        rw [← pow_mul, ← pow_add]
        have : e ≤ e * i := Nat.le_mul_of_pos_right _ hi
        exact pow_dvd_pow _ (by omega)
      rw [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ M)), (ZMod.natCast_eq_zero_iff _ _).2 hdvd,
        zero_smul]
    rw [← map_nsmul, hti, map_zero]

end GroupAlgebra

end Stacks.CharSeriesTraceDetection
