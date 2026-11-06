module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.NumberTheory.Padics.RingHoms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalMonodromyQuasiUnipotent
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Local monodromy: the group-theoretic half

Let `I` be the inertia group of a henselian discretely valued field with separably closed
residue field of characteristic `p`, `P ⊆ I` its wild inertia (a pro-`p` group), and `φ` a
Frobenius element, which acts on the tame quotient `I / P` by raising to the power `q`.  For a
continuous representation `ρ : G → GL_r(ℤ_ℓ)`, `ℓ ≠ p`, Grothendieck's argument runs:

* the congruence subgroup `U = 1 + ℓ M_r(ℤ_ℓ)` is open and normal, and has no nontrivial
  element `x` with `x ^ (p ^ n) → 1`: for `m` prime to `ℓ`, `x ^ m - 1` and `x - 1` are divisible
  by exactly the same powers of `ℓ`;
* hence on the open normal subgroup `K = ρ⁻¹(U)`, `ρ` kills `P ∩ K`, and for `σ ∈ I ∩ K` the
  relation `φ σ φ⁻¹ ≡ σ ^ q (mod P)` becomes `ρ(φ) ρ(σ) ρ(φ)⁻¹ = ρ(σ) ^ q`, to which the
  linear-algebraic half (`Stacks.EtaleCohomology.exists_monodromy_logarithm`) applies.

The wild inertia enters only through the property of its elements that is used: every open
subgroup contains some power `h ^ m` with `m` prime to `ℓ`, which holds in every pro-`p` group
(`m` a power of `p`) and for the kernel of the `ℓ`-adic tame character.

## Main results

* `Stacks.EtaleCohomology.dvd_sub_one_of_dvd_pow_sub_one`: if `x ≡ 1 (mod ℓ)` and `m` is prime
  to `ℓ`, then `ℓ ^ (k + 1) ∣ x ^ m - 1` implies `ℓ ^ (k + 1) ∣ x - 1`.
* `Stacks.EtaleCohomology.eq_one_of_forall_exists_coprime_pow`: an element of
  `1 + ℓ M_r(ℤ_ℓ)` with powers `x ^ m ≡ 1 (mod ℓ ^ n)`, `m` prime to `ℓ`, for every `n` is `1`.
* `Stacks.EtaleCohomology.congruenceSubgroup`: the open normal subgroups `Γ(ℓ ^ n)` of
  `GL_r(ℤ_ℓ)`.
* `Stacks.EtaleCohomology.map_eq_one_of_forall_exists_coprime_pow_mem`: a continuous `ρ` kills
  the pro-prime-to-`ℓ` elements of `ρ⁻¹(Γ(ℓ))`.
* `Stacks.EtaleCohomology.map_mul_eq_pow_mul_of_tame`: on `ρ⁻¹(Γ(ℓ))`, Frobenius acts on
  `ρ(inertia)` by the `q`-th power.
* `Stacks.EtaleCohomology.mulVec_eq_of_tame`: on a compact subgroup `J` of inertia on whose
  `ℓ`-adic tame character `t` the representation factors, with `t J ⊆ ℤ_ℓ · t T`, the
  `J`-invariants are the invariants of `ρ T`.
* `Stacks.EtaleCohomology.exists_monodromy_logarithm_of_tame`: Grothendieck's theorem for one
  element of inertia: a power of its image is unipotent with logarithm `N`, `N F = q F N`.

## References

* A. Grothendieck, appendix to J.-P. Serre and J. Tate, *Good reduction of abelian varieties*,
  Ann. of Math. 88 (1968).
* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.7.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open Filter Topology Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

/-- `(1 + y) ^ m = 1 + m • y + y * y * w` for some `w`. -/
public theorem exists_one_add_pow_eq {R : Type*} [Ring R] (y : R) (m : ℕ) :
    ∃ w : R, (1 + y) ^ m = 1 + m • y + y * y * w := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨w + (m : R) + y * w, ?_⟩
    rw [pow_succ', hw]
    simp only [nsmul_eq_mul, Nat.cast_succ]
    have hc : y * (m : R) = (m : R) * y := (Nat.cast_commute m y).symm.eq
    simp only [mul_add, add_mul, one_mul, mul_one, mul_assoc]
    have hc' : y * (y * (m : R)) = (m : R) * (y * y) := by
      rw [hc, ← mul_assoc, ← mul_assoc, hc]
    have hc'' : y * ((m : R) * y) = (m : R) * (y * y) := by rw [← mul_assoc, hc, mul_assoc]
    rw [hc', hc'']
    abel

/-- A natural number prime to `ℓ` is not divisible by `ℓ` in `ℤ_ℓ`. -/
public theorem not_dvd_natCast_of_coprime {m : ℕ} (hm : ℓ.Coprime m) :
    ¬ (ℓ : ℤ_[ℓ]) ∣ (m : ℤ_[ℓ]) := by
  rw [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_eq_one_iff.2 hm]
  exact lt_irrefl 1

/-- **Powers prime to `ℓ` do not move `x ≡ 1 (mod ℓ)` closer to `1`.**  If every entry of
`x - 1` is divisible by `ℓ` and `m` is prime to `ℓ`, then `ℓ ^ (k + 1)` divides every entry of
`x - 1` as soon as it divides every entry of `x ^ m - 1`. -/
public theorem dvd_sub_one_of_dvd_pow_sub_one {x : Matrix (Fin r) (Fin r) ℤ_[ℓ]}
    (hx : ∀ i j, (ℓ : ℤ_[ℓ]) ∣ (x - 1) i j) {m : ℕ} (hm : ℓ.Coprime m) (k : ℕ)
    (hk : ∀ i j, (ℓ : ℤ_[ℓ]) ^ (k + 1) ∣ (x ^ m - 1) i j) :
    ∀ i j, (ℓ : ℤ_[ℓ]) ^ (k + 1) ∣ (x - 1) i j := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have hy := ih fun i j => (pow_dvd_pow _ (by omega)).trans (hk i j)
    set y := x - 1 with hydef
    choose z hz using hy
    set Z : Matrix (Fin r) (Fin r) ℤ_[ℓ] := Matrix.of z
    have hyZ : y = ((ℓ : ℤ_[ℓ]) ^ (k + 1)) • Z := by
      ext i j
      simp [Z, hz i j]
    obtain ⟨w, hw⟩ := exists_one_add_pow_eq y m
    have hxy : x = 1 + y := by rw [hydef, add_sub_cancel]
    have hxm : x ^ m - 1 = m • y + ((ℓ : ℤ_[ℓ]) ^ (k + 1) * (ℓ : ℤ_[ℓ]) ^ (k + 1)) •
        (Z * Z * w) := by
      rw [hxy, hw, add_assoc, add_sub_cancel_left]
      congr 1
      rw [hyZ, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_smul]
    intro i j
    have h1 := hk i j
    rw [hxm, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, hyZ, Matrix.smul_apply,
      smul_eq_mul, smul_eq_mul, nsmul_eq_mul] at h1
    have h2 : (ℓ : ℤ_[ℓ]) ^ (k + 1 + 1) ∣
        (ℓ : ℤ_[ℓ]) ^ (k + 1) * (ℓ : ℤ_[ℓ]) ^ (k + 1) * (Z * Z * w) i j :=
      Dvd.dvd.mul_right (by rw [← pow_add]; exact pow_dvd_pow _ (by omega)) _
    have h3 := (dvd_add_left h2).1 h1
    rw [show (m : ℤ_[ℓ]) * ((ℓ : ℤ_[ℓ]) ^ (k + 1) * Z i j) =
      (ℓ : ℤ_[ℓ]) ^ (k + 1) * ((m : ℤ_[ℓ]) * Z i j) by ring, pow_succ] at h3
    have h4 := (mul_dvd_mul_iff_left (pow_ne_zero _ (Nat.cast_ne_zero.2
      (Fact.out : ℓ.Prime).ne_zero))).1 h3
    have h5 : (ℓ : ℤ_[ℓ]) ∣ Z i j :=
      (PadicInt.prime_p.dvd_or_dvd h4).resolve_left (not_dvd_natCast_of_coprime hm)
    rw [hyZ, Matrix.smul_apply, smul_eq_mul, pow_succ]
    exact mul_dvd_mul_left _ h5

/-- An element of `ℤ_ℓ` divisible by every power of `ℓ` is zero. -/
public theorem eq_zero_of_forall_pow_dvd {a : ℤ_[ℓ]} (h : ∀ n : ℕ, (ℓ : ℤ_[ℓ]) ^ n ∣ a) :
    a = 0 := by
  by_contra ha
  have := (PadicInt.mem_span_pow_iff_le_valuation a ha (a.valuation + 1)).1
    (Ideal.mem_span_singleton.2 (h _))
  omega

/-- `ℓ ^ n ∣ a` in `ℤ_ℓ` exactly when `‖a‖ ≤ ℓ ^ (-n)`. -/
public theorem pow_dvd_iff_norm_le (a : ℤ_[ℓ]) (n : ℕ) :
    (ℓ : ℤ_[ℓ]) ^ n ∣ a ↔ ‖a‖ ≤ (ℓ : ℝ) ^ (-n : ℤ) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

/-- The locus where a continuous `ℤ_ℓ`-valued function is divisible by `ℓ ^ n` is clopen. -/
private theorem isClopen_setOf_pow_dvd {X : Type*} [TopologicalSpace X] {f : X → ℤ_[ℓ]}
    (hf : Continuous f) (n : ℕ) : IsClopen {x | (ℓ : ℤ_[ℓ]) ^ n ∣ f x} := by
  have hℓ : (0 : ℝ) < ℓ := Nat.cast_pos.2 (Fact.out : ℓ.Prime).pos
  have : {x | (ℓ : ℤ_[ℓ]) ^ n ∣ f x} = f ⁻¹' Metric.closedBall 0 ((ℓ : ℝ) ^ (-n : ℤ)) := by
    ext x
    simp [pow_dvd_iff_norm_le]
  rw [this]
  exact (IsUltrametricDist.isClopen_closedBall 0 (zpow_pos hℓ _).ne').preimage hf

/-- **No element `≢ 1` of `1 + ℓ M_r(ℤ_ℓ)` is pro-prime-to-`ℓ`.**  If `x ≡ 1 (mod ℓ)` and for
every `n` some power `x ^ m` with `m` prime to `ℓ` is `≡ 1 (mod ℓ ^ n)`, then `x = 1`. -/
public theorem eq_one_of_forall_exists_coprime_pow {x : Matrix (Fin r) (Fin r) ℤ_[ℓ]}
    (hx : ∀ i j, (ℓ : ℤ_[ℓ]) ∣ (x - 1) i j)
    (h : ∀ n : ℕ, ∃ m : ℕ, ℓ.Coprime m ∧ ∀ i j, (ℓ : ℤ_[ℓ]) ^ n ∣ (x ^ m - 1) i j) : x = 1 := by
  have hall : ∀ k : ℕ, ∀ i j, (ℓ : ℤ_[ℓ]) ^ (k + 1) ∣ (x - 1) i j := fun k => by
    obtain ⟨m, hm, hmk⟩ := h (k + 1)
    exact dvd_sub_one_of_dvd_pow_sub_one hx hm k hmk
  refine Matrix.ext fun i j => ?_
  have : (x - 1) i j = 0 :=
    eq_zero_of_forall_pow_dvd fun n => (pow_dvd_pow _ (Nat.le_succ n)).trans (hall n i j)
  rwa [Matrix.sub_apply, sub_eq_zero] at this

/-- The entries of a product are divisible by `c` when those of the left factor are. -/
public theorem dvd_mul_apply_of_dvd_left {c : ℤ_[ℓ]} {A B : Matrix (Fin r) (Fin r) ℤ_[ℓ]}
    (hA : ∀ i j, c ∣ A i j) (i j : Fin r) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => (hA i k).mul_right _

/-- The entries of a product are divisible by `c` when those of the right factor are. -/
public theorem dvd_mul_apply_of_dvd_right {c : ℤ_[ℓ]} {A B : Matrix (Fin r) (Fin r) ℤ_[ℓ]}
    (hB : ∀ i j, c ∣ B i j) (i j : Fin r) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => (hB k j).mul_left _

variable (ℓ r) in
/-- The principal congruence subgroup `Γ(ℓ ^ n) = ker (GL_r(ℤ_ℓ) → GL_r(ℤ / ℓ ^ n))`. -/
public def congruenceSubgroup (n : ℕ) : Subgroup (GL (Fin r) ℤ_[ℓ]) where
  carrier := {g | ∀ i j, (ℓ : ℤ_[ℓ]) ^ n ∣ ((g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) i j}
  one_mem' := by simp
  mul_mem' {g h} hg hh i j := by
    have : ((g * h : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1 =
        ((g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) * ((h : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) +
          ((g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) + ((h : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [this, Matrix.add_apply, Matrix.add_apply]
    exact dvd_add (dvd_add (dvd_mul_apply_of_dvd_left hg i j) (hg i j)) (hh i j)
  inv_mem' {g} hg i j := by
    have : ((g⁻¹ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1 =
        -(((g⁻¹ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *
          ((g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [this, Matrix.neg_apply, dvd_neg]
    exact dvd_mul_apply_of_dvd_right hg i j

/-- `g ∈ Γ(ℓ ^ n)` exactly when `ℓ ^ n` divides every entry of `g - 1`. -/
public theorem mem_congruenceSubgroup {n : ℕ} {g : GL (Fin r) ℤ_[ℓ]} :
    g ∈ congruenceSubgroup ℓ r n ↔
      ∀ i j, (ℓ : ℤ_[ℓ]) ^ n ∣ ((g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) i j := Iff.rfl

/-- The congruence subgroups are normal. -/
public theorem congruenceSubgroup_normal (n : ℕ) : (congruenceSubgroup ℓ r n).Normal where
  conj_mem g hg h i j := by
    have : ((h * g * h⁻¹ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1 =
        (h : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * ((g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) *
          ((h⁻¹ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) := by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, ← Units.val_mul h h⁻¹,
        mul_inv_cancel, Units.val_one]
    rw [this]
    exact dvd_mul_apply_of_dvd_left (dvd_mul_apply_of_dvd_right hg) i j

/-- The congruence subgroups are open. -/
public theorem isOpen_congruenceSubgroup (n : ℕ) :
    IsOpen (congruenceSubgroup ℓ r n : Set (GL (Fin r) ℤ_[ℓ])) := by
  have hset : (congruenceSubgroup ℓ r n : Set (GL (Fin r) ℤ_[ℓ])) =
      ⋂ i, ⋂ j, {g : GL (Fin r) ℤ_[ℓ] |
        (ℓ : ℤ_[ℓ]) ^ n ∣ ((g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_congruenceSubgroup, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isClopen_setOf_pow_dvd
    ((Units.continuous_val.sub continuous_const).matrix_elem i j) n).isOpen

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] {ρ : G →* GL (Fin r) ℤ_[ℓ]}

/-- **A continuous `ℓ`-adic representation kills the pro-prime-to-`ℓ` elements of the open
normal subgroup `ρ⁻¹(1 + ℓ M_r(ℤ_ℓ))`.**  If `ρ σ ≡ 1 (mod ℓ)` and every open subgroup of `G`
contains a power `σ ^ m` with `m` prime to `ℓ`, then `ρ σ = 1`. -/
public theorem map_eq_one_of_forall_exists_coprime_pow_mem (hρ : Continuous ρ) {σ : G}
    (h1 : ρ σ ∈ congruenceSubgroup ℓ r 1)
    (hσ : ∀ U : OpenSubgroup G, ∃ m : ℕ, ℓ.Coprime m ∧ σ ^ m ∈ U) : ρ σ = 1 := by
  refine Units.ext (eq_one_of_forall_exists_coprime_pow (fun i j => by simpa using h1 i j)
    fun n => ?_)
  let U : OpenSubgroup G :=
    { toSubgroup := (congruenceSubgroup ℓ r n).comap ρ
      isOpen' := (isOpen_congruenceSubgroup n).preimage hρ }
  obtain ⟨m, hm, hmU⟩ := hσ U
  refine ⟨m, hm, fun i j => ?_⟩
  have : ρ (σ ^ m) ∈ congruenceSubgroup ℓ r n := hmU
  rw [map_pow, mem_congruenceSubgroup, Units.val_pow_eq_pow_val] at this
  exact this i j

/-- **The tame relation on the image of inertia.**  Let `T, Fr ∈ G` with `ρ T ≡ 1 (mod ℓ)` and
`τ = Fr T Fr⁻¹ T^{-q}` pro-prime-to-`ℓ` in the sense of
`Stacks.EtaleCohomology.map_eq_one_of_forall_exists_coprime_pow_mem`. Then
`ρ(Fr) ρ(T) = ρ(T) ^ q ρ(Fr)`. -/
public theorem map_mul_eq_pow_mul_of_tame (hρ : Continuous ρ) {T Fr : G} {q : ℕ}
    (hT : ρ T ∈ congruenceSubgroup ℓ r 1)
    (hτ : ∀ U : OpenSubgroup G, ∃ m : ℕ, ℓ.Coprime m ∧ (Fr * T * Fr⁻¹ * (T ^ q)⁻¹) ^ m ∈ U) :
    ρ Fr * ρ T = ρ T ^ q * ρ Fr := by
  have hmem : ρ (Fr * T * Fr⁻¹ * (T ^ q)⁻¹) ∈ congruenceSubgroup ℓ r 1 := by
    rw [map_mul, map_inv, map_pow]
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hT q))
    rw [map_mul, map_mul, map_inv]
    exact (congruenceSubgroup_normal 1).conj_mem _ hT _
  have h := map_eq_one_of_forall_exists_coprime_pow_mem hρ hmem hτ
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, mul_inv_eq_one] at h
  rw [← h, mul_assoc, inv_mul_cancel, mul_one]

/-- **Grothendieck's local monodromy theorem** for one element of inertia.  Let `ρ : G → GL_r(ℤ_ℓ)`
be continuous, `T ∈ G` with `ρ T ≡ 1 (mod ℓ)`, and `Fr ∈ G` with `Fr T Fr⁻¹ T^{-q}`
pro-prime-to-`ℓ`, `q ≥ 2`.  Then on `ℚ_ℓ^r`, with `T'` the action of `T` and `F` that of the
geometric Frobenius `Fr⁻¹`, some `T' ^ m`, `m > 0`, is unipotent, and its logarithm `N` is
nilpotent, satisfies `N F = q F N`, and has kernel the vectors fixed by `T' ^ m`. -/
public theorem exists_monodromy_logarithm_of_tame (hρ : Continuous ρ) {T Fr : G} {q : ℕ}
    (hq : 2 ≤ q) (hT : ρ T ∈ congruenceSubgroup ℓ r 1)
    (hτ : ∀ U : OpenSubgroup G, ∃ m : ℕ, ℓ.Coprime m ∧ (Fr * T * Fr⁻¹ * (T ^ q)⁻¹) ^ m ∈ U) :
    let φ : Matrix (Fin r) (Fin r) ℤ_[ℓ] →ₐ[ℤ_[ℓ]] Module.End ℚ_[ℓ] (Fin r → ℚ_[ℓ]) :=
      (Matrix.toLinAlgEquiv' (R := ℚ_[ℓ]) (n := Fin r)).toAlgHom.restrictScalars ℤ_[ℓ] |>.comp
        (AlgHom.mapMatrix (Algebra.ofId ℤ_[ℓ] ℚ_[ℓ]))
    ∃ m : ℕ, 0 < m ∧ ∃ N : Module.End ℚ_[ℓ] (Fin r → ℚ_[ℓ]), IsNilpotent N ∧
      N * φ (ρ Fr⁻¹ : GL (Fin r) ℤ_[ℓ]) = (q : ℚ_[ℓ]) • (φ (ρ Fr⁻¹ : GL (Fin r) ℤ_[ℓ]) * N) ∧
      ∀ v, N v = 0 ↔ (φ (ρ T : GL (Fin r) ℤ_[ℓ]) ^ m) v = v := by
  intro φ
  have hrel := map_mul_eq_pow_mul_of_tame hρ hT hτ
  have hrel' : ρ T * ρ Fr⁻¹ = ρ Fr⁻¹ * ρ T ^ q := by
    rw [map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, hrel, mul_assoc, mul_inv_cancel, mul_one]
  have hT' : IsUnit (φ (ρ T : GL (Fin r) ℤ_[ℓ])) := (Units.isUnit _).map φ
  have hF' : IsUnit (φ (ρ Fr⁻¹ : GL (Fin r) ℤ_[ℓ])) := (Units.isUnit _).map φ
  refine exists_monodromy_logarithm hT' hF' hq ?_
  rw [← map_mul, ← map_pow, ← map_mul, ← Units.val_mul, ← Units.val_pow_eq_pow_val,
    ← Units.val_mul, hrel']

/-- **The tame image is topologically generated by one element.**  Let `J` be a compact subgroup of
`G`, `t : J → ℤ_ℓ` a continuous homomorphism whose kernel `ρ` kills, and `T ∈ J` with
`t σ ∈ ℤ_ℓ · t T` for all `σ ∈ J`.  Then every `ρ σ` is `ℓ`-adically approximated by powers of
`ρ T`: for each `N` there is `k` with `ρ (σ T⁻ᵏ) ∈ Γ(ℓ ^ N)`. -/
public theorem exists_pow_mul_mem_congruenceSubgroup (hρ : Continuous ρ) {J : Subgroup G}
    [CompactSpace J] (t : J →* Multiplicative ℤ_[ℓ]) (ht : Continuous t)
    (hker : ∀ τ : J, t τ = 1 → ρ τ = 1) (T σ : J) (c : ℤ_[ℓ])
    (hc : Multiplicative.toAdd (t σ) = c * Multiplicative.toAdd (t T)) (N : ℕ) :
    ∃ k : ℕ, ρ ((σ * T⁻¹ ^ k : J) : G) ∈ congruenceSubgroup ℓ r N := by
  have hopen : IsOpen ((congruenceSubgroup ℓ r N).comap (ρ.comp J.subtype) : Set J) :=
    (isOpen_congruenceSubgroup N).preimage (hρ.comp continuous_subtype_val)
  set C : ℕ → Set J := fun n =>
    {τ | (ℓ : ℤ_[ℓ]) ^ n ∣ Multiplicative.toAdd (t τ)} ∩
      ((congruenceSubgroup ℓ r N).comap (ρ.comp J.subtype) : Set J)ᶜ with hCdef
  have hclosed : ∀ n, IsClosed (C n) := fun n => by
    exact (isClopen_setOf_pow_dvd (continuous_toAdd.comp ht) n).isClosed.inter
      hopen.isClosed_compl
  have hempty : ∃ n, C n = ∅ := by
    by_contra hne
    push Not at hne
    obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      (fun n τ hτ => ⟨(pow_dvd_pow _ (Nat.le_succ n)).trans hτ.1, hτ.2⟩)
      hne (hclosed 0).isCompact hclosed
    rw [Set.mem_iInter] at hτ
    have h0 : Multiplicative.toAdd (t τ) = 0 := eq_zero_of_forall_pow_dvd fun n => (hτ n).1
    have h1 : ρ τ = 1 := hker τ (by simpa using congrArg Multiplicative.ofAdd h0)
    exact (hτ 0).2 (by simp [h1])
  obtain ⟨n, hn⟩ := hempty
  refine ⟨PadicInt.appr c n, ?_⟩
  have hdvd : (ℓ : ℤ_[ℓ]) ^ n ∣ Multiplicative.toAdd (t (σ * T⁻¹ ^ PadicInt.appr c n)) := by
    rw [map_mul, map_pow, map_inv, toAdd_mul, toAdd_pow, toAdd_inv, hc, smul_neg, nsmul_eq_mul,
      ← sub_eq_add_neg, ← sub_mul]
    exact (Ideal.mem_span_singleton.1 (PadicInt.appr_spec n c)).mul_right _
  by_contra hmem
  have : σ * T⁻¹ ^ PadicInt.appr c n ∈ C n := ⟨hdvd, hmem⟩
  rw [hn] at this
  exact this

/-- A matrix `g` approximated by powers of `h`, `g h⁻ᵏ ∈ Γ(ℓ ^ N)` for every `N`, fixes every
integral vector fixed by `h`. -/
public theorem mulVec_eq_of_forall_exists_mul_pow_mem {g h : GL (Fin r) ℤ_[ℓ]}
    (hgh : ∀ N : ℕ, ∃ k : ℕ, g * h⁻¹ ^ k ∈ congruenceSubgroup ℓ r N) {v : Fin r → ℤ_[ℓ]}
    (hv : (h : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v) :
    (g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v := by
  have hinv : ((h⁻¹ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v := by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hpow : ∀ k : ℕ, ((h⁻¹ ^ k : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v :=
    fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, hinv, ih]
  have : (g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v - v = 0 := by
    funext i
    refine eq_zero_of_forall_pow_dvd fun N => ?_
    obtain ⟨k, hk⟩ := hgh N
    have hrw : (g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v - v =
        (((g * h⁻¹ ^ k : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) *ᵥ v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Units.val_mul, ← Matrix.mulVec_mulVec, hpow]
    rw [hrw, Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum fun j _ => (hk i j).mul_right _
  exact sub_eq_zero.1 this

/-- **Invariants of tame inertia are the invariants of one element.**  In the situation of
`Stacks.EtaleCohomology.exists_pow_mul_mem_congruenceSubgroup`, every integral vector fixed by
`ρ T` is fixed by `ρ σ` for every `σ ∈ J`. -/
public theorem mulVec_eq_of_tame (hρ : Continuous ρ) {J : Subgroup G} [CompactSpace J]
    (t : J →* Multiplicative ℤ_[ℓ]) (ht : Continuous t) (hker : ∀ τ : J, t τ = 1 → ρ τ = 1)
    (T : J) (hgen : ∀ σ : J, ∃ c : ℤ_[ℓ], Multiplicative.toAdd (t σ) =
      c * Multiplicative.toAdd (t T))
    {v : Fin r → ℤ_[ℓ]} (hv : ((ρ T : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v)
    (σ : J) : ((ρ σ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v := by
  obtain ⟨c, hc⟩ := hgen σ
  refine mulVec_eq_of_forall_exists_mul_pow_mem (h := ρ T) (fun N => ?_) hv
  obtain ⟨k, hk⟩ := exists_pow_mul_mem_congruenceSubgroup hρ t ht hker T σ c hc N
  refine ⟨k, ?_⟩
  simpa [map_mul, map_pow, map_inv] using hk

end Group

end Stacks.EtaleCohomology

end
