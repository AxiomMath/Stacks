module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Nat.Choose.Sum
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksCore.Tactic.StacksAttribute

/-!
# Chern classes of a twist by an invertible module

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42, let `ℰ` be a
finite locally free `𝒪_X`-module of rank `r` and let `ℒ` be invertible.
[Stacks, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD) computes the Chern classes of the
twist:

  `c_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j}(ℰ) c₁(ℒ)^j`.

This file proves that identity **componentwise, as an identity between cap products on Chow
groups**: the right-hand side is the binomial transform of
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.BinomialInversion` along `c₁(ℒ) ∩ -`, so for an
`n`-cycle `α` on `X` the statement reads

  `c_m(ℰ ⊗ ℒ) ∩ α = binomialTransform (c₁(ℒ) ∩ -) r (j ↦ c_j(ℰ) ∩ α) m`,  `m ≤ r`,

in `A_{n-m}(X)`. That is the shape in which Stacks 02UH consumes the formula; see
`Stacks.Chow.chernClassCapExt_succ_eq_add_firstChernCap`.

## Why componentwise, and not in `A^*(X)`

The source states the identity in the bivariant ring `A^*(X)`. There is no such ring here:
`Stacks.Chow.chowCohomology` carries no multiplication, the product being composition of
bivariant classes, which is unproved in this repository — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ChowCohomology`. The source's own proof
reduces the identity in `A^*(X)` to the cap products on cycles, by Stacks 02UC, and it is at
that level that everything below is stated; the same reduction is what
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation` performs for Stacks 02UH.

## The argument, and what is carried

Write `(π : P ⟶ X, 𝒪_P(1))` for the projective bundle of `ℰ`. By Stacks 02NC the projective
bundle of `ℰ ⊗ ℒ` is `P` again, by an isomorphism over `X` carrying `𝒪_{𝐏(ℰ ⊗ ℒ)}(1)` to
`𝒪_P(1) ⊗ π^*ℒ`; so the relation of Stacks 02U6 for `ℰ ⊗ ℒ`, transported to `P`, is the relation
for `ℰ` with `c₁(𝒪_P(1)) ∩ -` replaced by `c₁(𝒪_P(1)) ∩ - + c₁(π^*ℒ) ∩ -`. The right-hand side
of the displayed formula solves that transported relation — the content is the single binomial
identity `∑_{j=0}^{k} (-1)^j binom(k, j) (ξ + x)^j x^{k-j} = ξ^k`, the binomial theorem applied
to `((ξ + x) + (-x))^k` — and the transported relation has at most one solution by the
injectivity half of Stacks 02TX. That is the whole proof, and
`Stacks.Chow.eq_binomialTransform_of_towerRelations` is it.

Five inputs are hypotheses, each a tag this repository does not prove, and each already carried
the same way by the declarations composed here:

* the two relations of Stacks 02U6, `hrelE` and `hrelEL`. That a family of cap products satisfies
  the relation is Stacks 02U5 together with the surjectivity half of Stacks 02TX, recorded as
  absent in `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation`;
  `hrelEL` is moreover the relation **already transported** along the comparison of Stacks 02NC,
  which is the one place the geometry of the twist enters.
* `huniq`, uniqueness of the solution of the transported relation. This is Stacks 02U6
  uniqueness — `Stacks.Chow.eq_of_isChernCapFamily` — read at the transported bundle, and rests
  on the injectivity half of Stacks 02TX.
* `hcomm`, that the two first Chern class cap operators on `P` commute: Stacks 02UA.
* `hpull`, that flat pullback along `π` carries `c₁(ℒ) ∩ -` to `c₁(π^*ℒ) ∩ -`: Stacks 02SS and
  Stacks 02RD.
* `h0`, that the two zeroth cap products agree, both being the class of `α`. This is clause (1)
  of Stacks 02U5 at `j = 0`; `Stacks.Chow.ChernClassCycleRule`, the datum of Stacks 02U0 the cap
  products are read off, carries no normalization in degree zero.

The first Chern classes on `P` enter as `Stacks.Chow.ChernCapOperator`s rather than as invertible
modules, exactly as in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation`: `𝒪_P(1)` has no
name in this repository, and an operator is what an invertible module provides once Stacks 02SO
and Stacks 02TI are available.

## Main definitions

* `Stacks.Chow.towerShift` — a graded family `G i ⟶ G (i + 1)` read as an endomorphism of the
  product `∏_i G i`, whose `s`-th power is `Stacks.Chow.descentTower` at offset `s`. This is
  what turns the graded bookkeeping of the relation into algebra in a ring.
* `Stacks.Chow.towerPullback` — a graded family `G i ⟶ H i` read as a map of products.
* `Stacks.Chow.alternatingTowerSum` — the alternating sum `∑_{i=0}^{r} (-1)^i ξ^i(e_{r-i})` in
  which the relation of Stacks 02U6 is written.
* `Stacks.Chow.ChernCapOperator.towerStep` — `c₁ ∩ -` for a first Chern class cap operator, read
  between the Chow groups in which cap products of consecutive degrees land.
* `Stacks.Chow.bundleRelationDegree`, `Stacks.Chow.projectiveBundleTowerPullback` — the degrees in
  which the relation of Stacks 02U6 is read on the bundle, and flat pullback along the projection
  of the bundle read between the corresponding two graded families.

## Main results

* `Stacks.Chow.eq_binomialTransform_of_towerRelations` — the algebraic heart: a graded sequence
  solving the shifted relation is the binomial transform of one solving the unshifted relation.
* `Stacks.Chow.chernCapFamily_tensorObj_eq_binomialTransform` — **Stacks 02UD**, the binomial
  formula for the Chern class cap products of `ℰ ⊗ ℒ`.

## References

* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset

universe u

namespace Stacks.Chow

/-! ### Graded towers as endomorphisms of a product -/

section Tower

variable {G H : ℕ → Type*} [∀ i, AddCommGroup (G i)] [∀ i, AddCommGroup (H i)]

/-- One step of a graded tower, read on the product `∏_i G i`: in degree `i + 1` it is `τ i` of
the entry in degree `i`, and in degree `0` it is zero. -/
def towerShiftFun (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ i, G i) : ∀ i, G i
  | 0 => 0
  | i + 1 => τ i (e i)

/-- A graded family of degree-raising maps `G i ⟶ G (i + 1)`, read as an endomorphism of the
product `∏_i G i`. Its `s`-th power is `Stacks.Chow.descentTower` at offset `s`, so mixed powers
of two such families are products in a ring and the binomial theorem applies to their sum. -/
def towerShift (τ : ∀ i, G i →+ G (i + 1)) : Module.End ℤ (∀ i, G i) :=
  (AddMonoidHom.mk' (towerShiftFun τ) fun e e' => by
    funext i
    cases i with
    | zero => simp [towerShiftFun]
    | succ n => simp [towerShiftFun]).toIntLinearMap

/-- A graded tower carries nothing into degree `0`: the degree-`0` entry of its value is zero. -/
@[simp]
theorem towerShift_apply_zero (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ i, G i) :
    (towerShift τ • e) 0 = 0 :=
  rfl

/-- In degree `i + 1` a graded tower is the degree-raising map `τ i` applied to the entry in
degree `i`. -/
@[simp]
theorem towerShift_apply_succ (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ i, G i) (i : ℕ) :
    (towerShift τ • e) (i + 1) = τ i (e i) :=
  rfl

/-- The `s`-th power of a graded tower is the tower of `Stacks.Chow.descentTower` at offset `s`:
in degree `i` it is `τ^s` applied to the entry in degree `i - s`. -/
theorem towerShift_pow_apply (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ i, G i) (s : ℕ) :
    ∀ i, s ≤ i → ((towerShift τ ^ s) • e) i = descentTower τ e i (i - s) := by
  induction s with
  | zero => exact fun i _ => by simp
  | succ s ih =>
      intro i hi
      obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
      rw [pow_succ', mul_smul, towerShift_apply_succ, ih n (by omega),
        show n + 1 - (s + 1) = n - s from by omega,
        descentTower_succ_of_le τ e (show n - s ≤ n from by omega)]

/-- The tower of a pointwise sum of two graded families is the sum of their towers. -/
theorem towerShift_add (τ σ : ∀ i, G i →+ G (i + 1)) :
    towerShift (fun i => τ i + σ i) = towerShift τ + towerShift σ := by
  refine LinearMap.ext fun e => funext fun i => ?_
  cases i <;> simp [towerShift, towerShiftFun]

/-- Two graded families whose steps commute have commuting towers. -/
theorem towerShift_commute (ξ υ : ∀ i, H i →+ H (i + 1))
    (h : ∀ i, (ξ (i + 1)).comp (υ i) = (υ (i + 1)).comp (ξ i)) :
    Commute (towerShift ξ) (towerShift υ) := by
  have key : towerShift ξ * towerShift υ = towerShift υ * towerShift ξ := by
    refine LinearMap.ext fun e => funext fun i => ?_
    match i with
    | 0 => rfl
    | 1 =>
        change ξ 0 ((towerShift υ • e) 0) = υ 0 ((towerShift ξ • e) 0)
        simp only [towerShift_apply_zero, map_zero]
    | (n + 2) =>
        change ξ (n + 1) ((towerShift υ • e) (n + 1)) = υ (n + 1) ((towerShift ξ • e) (n + 1))
        simp only [towerShift_apply_succ]
        exact DFunLike.congr_fun (h n) (e n)
  exact key

/-- A graded family of maps `G i ⟶ H i`, read as a map of products. -/
def towerPullback (p : ∀ i, G i →+ H i) : (∀ i, G i) →+ (∀ i, H i) :=
  AddMonoidHom.mk' (fun e i => p i (e i)) fun e e' => by funext i; simp

/-- A graded family of maps acts degreewise on the products: in degree `i` its value is `p i`
applied to the entry in degree `i`. -/
@[simp]
theorem towerPullback_apply (p : ∀ i, G i →+ H i) (e : ∀ i, G i) (i : ℕ) :
    towerPullback p e i = p i (e i) :=
  rfl

/-- A graded family intertwining two graded towers intertwines the towers on the products. -/
theorem towerPullback_towerShift (τ : ∀ i, G i →+ G (i + 1)) (υ : ∀ i, H i →+ H (i + 1))
    (p : ∀ i, G i →+ H i) (h : ∀ i, (p (i + 1)).comp (τ i) = (υ i).comp (p i)) (e : ∀ i, G i) :
    towerPullback p (towerShift τ • e) = towerShift υ • towerPullback p e := by
  funext i
  cases i with
  | zero => simp only [towerPullback_apply, towerShift_apply_zero, map_zero]
  | succ n => exact DFunLike.congr_fun (h n) (e n)

/-- The same intertwining, read degreewise on the towers themselves. -/
theorem towerPullback_descentTower (τ : ∀ i, G i →+ G (i + 1)) (υ : ∀ i, H i →+ H (i + 1))
    (p : ∀ i, G i →+ H i) (h : ∀ i, (p (i + 1)).comp (τ i) = (υ i).comp (p i)) (e : ∀ i, G i)
    {m j : ℕ} (hj : j ≤ m) :
    p m (descentTower τ e m j) = descentTower υ (towerPullback p e) m j := by
  induction m, hj using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
      rw [descentTower_succ_of_le τ e hm, descentTower_succ_of_le υ (towerPullback p e) hm, ← ih]
      exact DFunLike.congr_fun (h m) (descentTower τ e m j)

/-- **The relation of Stacks 02U6, as a single element.** The alternating sum
`∑_{i=0}^{r} (-1)^i ξ^i(e_{r-i})` in degree `r`, which the relation of Stacks 02U6 asserts to
vanish for the pullbacks to the bundle of the Chern class cap products. -/
def alternatingTowerSum (ξ : ∀ i, H i →+ H (i + 1)) (r : ℕ) (e : ∀ j, H j) : H r :=
  ∑ i ∈ range (r + 1), (-1 : ℤ) ^ i • descentTower ξ e r (r - i)

/-- The alternating sum, written out. -/
theorem alternatingTowerSum_def (ξ : ∀ i, H i →+ H (i + 1)) (r : ℕ) (e : ∀ j, H j) :
    alternatingTowerSum ξ r e =
      ∑ i ∈ range (r + 1), (-1 : ℤ) ^ i • descentTower ξ e r (r - i) :=
  rfl

/-- The alternating sum, written through the tower on the product. -/
theorem alternatingTowerSum_eq (ξ : ∀ i, H i →+ H (i + 1)) (r : ℕ) (e : ∀ j, H j) :
    alternatingTowerSum ξ r e =
      (∑ i ∈ range (r + 1), (-1 : ℤ) ^ i • ((towerShift ξ ^ i) • e)) r := by
  rw [alternatingTowerSum_def, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Pi.smul_apply, towerShift_pow_apply ξ e i r (mem_range_succ_iff.mp hi)]

/-- The alternating sum is additive in its graded sequence. -/
theorem alternatingTowerSum_sub (ξ : ∀ i, H i →+ H (i + 1)) (r : ℕ) (e e' : ∀ j, H j) :
    alternatingTowerSum ξ r (e - e') =
      alternatingTowerSum ξ r e - alternatingTowerSum ξ r e' := by
  rw [alternatingTowerSum_eq, alternatingTowerSum_eq, alternatingTowerSum_eq, ← Pi.sub_apply,
    ← Finset.sum_sub_distrib]
  exact congrFun (Finset.sum_congr rfl fun i _ => by rw [smul_sub, smul_sub]) r

end Tower

/-! ### The algebra of the substitution -/

section Algebra

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- A power of a negated ring element, with the sign pulled out as an integer scalar. -/
private theorem neg_pow_eq_zsmul_pow (u : R) (k : ℕ) : (-u) ^ k = ((-1 : ℤ) ^ k) • u ^ k := by
  rw [neg_pow, zsmul_eq_mul]
  push_cast
  rfl

/-- **The binomial theorem for `x = (x + u) + (-u)`**, for `u` commuting with `x`: the
alternating binomial sum of the mixed powers `(x + u)^i u^{k-i}` collapses to `x^k`. -/
private theorem sum_choose_zsmul_pow {x u : R} (h : Commute x u) (k : ℕ) :
    ∑ i ∈ range (k + 1), ((-1 : ℤ) ^ i * (k.choose i : ℤ)) • ((x + u) ^ i * u ^ (k - i)) =
      ((-1 : ℤ) ^ k) • x ^ k := by
  have hc : Commute (x + u) (-u) := (h.add_left (Commute.refl u)).neg_right
  have hx : x + u + -u = x := by abel
  have key := hc.add_pow k
  rw [hx] at key
  rw [key, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := mem_range_succ_iff.mp hi
  have hsign : (-1 : ℤ) ^ k * (-1 : ℤ) ^ (k - i) = (-1 : ℤ) ^ i := by
    rw [← pow_add, show k + (k - i) = i + 2 * (k - i) from by omega, pow_add, pow_mul]
    simp
  rw [neg_pow_eq_zsmul_pow u (k - i), mul_smul_comm, smul_mul_assoc,
    (Nat.cast_commute (k.choose i) ((x + u) ^ i * u ^ (k - i))).symm.eq, ← nsmul_eq_mul,
    ← natCast_zsmul, smul_smul, smul_smul, hsign]

/-- The same identity, applied to a module element. -/
private theorem sum_choose_zsmul_pow_smul {x u : R} (h : Commute x u) (k : ℕ) (m : M) :
    ∑ i ∈ range (k + 1), ((-1 : ℤ) ^ i * (k.choose i : ℤ)) • ((x + u) ^ i • (u ^ (k - i) • m)) =
      ((-1 : ℤ) ^ k) • (x ^ k • m) := by
  have h' := congrArg (fun z : R => z • m) (sum_choose_zsmul_pow h k)
  simpa only [Finset.sum_smul, smul_assoc, mul_smul] using h'

/-- **The substitution `x ↦ x + u` in an alternating sum of a twisted family.** Let `u` commute
with `x` and let `a : ℕ → M`. Replacing `a_k` by the binomial twist
`∑_{j ≤ k} binom(N - k + j, j) u^j a_{k-j}` turns the alternating sum of the `(x + u)^i a_{N-i}`
into the alternating sum of the `x^i a_{N-i}`.

Summing over the diagonal `k = i + j` identifies the double sum with an alternating binomial sum
in each `a_{N-k}` separately, and those collapse by `sum_choose_zsmul_pow_smul`. -/
private theorem sum_alternating_tower_twist {x u : R} (h : Commute x u) (a : ℕ → M) (N : ℕ) :
    ∑ i ∈ range (N + 1), ((-1 : ℤ) ^ i) • ((x + u) ^ i •
          ∑ j ∈ range (N - i + 1), (i + j).choose j • (u ^ j • a (N - i - j))) =
      ∑ k ∈ range (N + 1), ((-1 : ℤ) ^ k) • (x ^ k • a (N - k)) := by
  classical
  set F : ℕ → ℕ → M := fun i k =>
    ((-1 : ℤ) ^ i * (k.choose i : ℤ)) • ((x + u) ^ i • (u ^ (k - i) • a (N - k))) with hF
  have step1 : ∀ i ∈ range (N + 1),
      ((-1 : ℤ) ^ i) • ((x + u) ^ i •
          ∑ j ∈ range (N - i + 1), (i + j).choose j • (u ^ j • a (N - i - j)))
        = ∑ k ∈ Finset.Ico i (N + 1), F i k := by
    intro i hi
    have hiN : i ≤ N := mem_range_succ_iff.mp hi
    rw [Finset.sum_Ico_eq_sum_range, Finset.smul_sum, Finset.smul_sum,
      show N + 1 - i = N - i + 1 from by omega]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hF]
    rw [show i + j - i = j from by omega, show N - (i + j) = N - i - j from by omega,
      Nat.choose_symm_add, smul_comm ((x + u) ^ i) ((i + j).choose j), ← natCast_zsmul,
      smul_smul]
  have step3 : ∀ k ∈ range (N + 1),
      ∑ i ∈ range (k + 1), F i k = ((-1 : ℤ) ^ k) • (x ^ k • a (N - k)) := by
    intro k _
    simp only [hF]
    exact sum_choose_zsmul_pow_smul h k (a (N - k))
  rw [Finset.sum_congr rfl step1, Finset.range_eq_Ico,
    Finset.sum_Ico_Ico_comm 0 (N + 1) F, ← Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.range_eq_Ico]
  exact step3 k hk

end Algebra

/-! ### The binomial formula from the two relations -/

section Formula

variable {G H : ℕ → Type*} [∀ i, AddCommGroup (G i)] [∀ i, AddCommGroup (H i)]

/-- In degree zero a binomial transform is its graded sequence. -/
theorem binomialTransform_apply_zero (τ : ∀ i, G i →+ G (i + 1)) (r : ℕ) (e : ∀ j, G j) :
    binomialTransform τ r e 0 = e 0 := by
  simp [binomialTransform_eq]

/-- The pullback of a binomial transform is the twisted family the substitution lemma expects:
in degree `m ≤ r` it is `∑_{s ≤ m} binom(r - m + s, s) υ^s(p e)` read in degree `m`. -/
private theorem towerPullback_binomialTransform (τ : ∀ i, G i →+ G (i + 1))
    (υ : ∀ i, H i →+ H (i + 1)) (p : ∀ i, G i →+ H i)
    (h : ∀ i, (p (i + 1)).comp (τ i) = (υ i).comp (p i)) (r : ℕ) (e : ∀ j, G j) {m : ℕ}
    (hm : m ≤ r) :
    towerPullback p (binomialTransform τ r e) m =
      (∑ s ∈ range (m + 1), (r - m + s).choose s •
        ((towerShift υ ^ s) • towerPullback p e)) m :=
  calc towerPullback p (binomialTransform τ r e) m
      = ∑ j ∈ range (m + 1), (r - j).choose (m - j) •
          descentTower υ (towerPullback p e) m j := by
        rw [towerPullback_apply, binomialTransform_eq, map_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [map_nsmul,
          towerPullback_descentTower τ υ p h e (mem_range_succ_iff.mp hj)]
    _ = ∑ s ∈ range (m + 1), (r - m + s).choose s •
          descentTower υ (towerPullback p e) m (m - s) := by
        rw [← Finset.sum_range_reflect (fun j => (r - j).choose (m - j) •
          descentTower υ (towerPullback p e) m j) (m + 1)]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hsm : s ≤ m := mem_range_succ_iff.mp hs
        rw [show m + 1 - 1 - s = m - s from by omega,
          show m - (m - s) = s from by omega, show r - (m - s) = r - m + s from by omega]
    _ = (∑ s ∈ range (m + 1), (r - m + s).choose s •
          ((towerShift υ ^ s) • towerPullback p e)) m := by
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [Pi.smul_apply, towerShift_pow_apply υ (towerPullback p e) s m
          (mem_range_succ_iff.mp hs)]

/-- **The binomial formula from the two relations.** Let `τ`, `ξ`, `υ` be graded towers with `ξ`
and `υ` commuting, and let `p` intertwine `τ` with `υ`. If `c` solves the alternating relation
for `ξ`, and `a` solves the relation for `ξ + υ`, agrees with `c` in degree zero, and the
solution of the latter relation is unique, then `a` is the binomial transform of `c` at `r`:

  `a_m = ∑_{j=0}^{m} binom(r - m + j, j) τ^j(c_{m-j})`,  `m ≤ r`.

This is the formal content of Stacks 02UD: the transform pulls back to a solution of the shifted
relation by `sum_alternating_tower_twist`, and uniqueness identifies it with `a`. -/
theorem eq_binomialTransform_of_towerRelations (τ : ∀ i, G i →+ G (i + 1))
    (ξ υ : ∀ i, H i →+ H (i + 1)) (p : ∀ i, G i →+ H i)
    (hcomm : ∀ i, (ξ (i + 1)).comp (υ i) = (υ (i + 1)).comp (ξ i))
    (hpull : ∀ i, (p (i + 1)).comp (τ i) = (υ i).comp (p i)) (r : ℕ) (c a : ∀ j, G j)
    (h0 : a 0 = c 0) (hrelE : alternatingTowerSum ξ r (towerPullback p c) = 0)
    (hrelF : alternatingTowerSum (fun j => ξ j + υ j) r (towerPullback p a) = 0)
    (huniq : ∀ d : (∀ j, G j), d 0 = 0 →
      alternatingTowerSum (fun j => ξ j + υ j) r (towerPullback p d) = 0 → ∀ m ≤ r, d m = 0)
    {m : ℕ} (hm : m ≤ r) :
    a m = binomialTransform τ r c m := by
  have hsum := towerShift_add ξ υ
  have hcom : Commute (towerShift ξ) (towerShift υ) := towerShift_commute ξ υ hcomm
  have hrelB : alternatingTowerSum (fun j => ξ j + υ j) r
      (towerPullback p (binomialTransform τ r c)) = 0 := by
    have htwist : (∑ i ∈ range (r + 1), ((-1 : ℤ) ^ i) •
          (((towerShift ξ + towerShift υ) ^ i) • ∑ s ∈ range (r - i + 1),
            (i + s).choose s • ((towerShift υ ^ s) • towerPullback p c)))
        = ∑ k ∈ range (r + 1), ((-1 : ℤ) ^ k) • ((towerShift ξ ^ k) • towerPullback p c) :=
      sum_alternating_tower_twist hcom (fun _ : ℕ => towerPullback p c) r
    have key : ∀ i ∈ range (r + 1),
        (-1 : ℤ) ^ i • descentTower (fun j => ξ j + υ j)
            (towerPullback p (binomialTransform τ r c)) r (r - i) =
          (((-1 : ℤ) ^ i) • (((towerShift ξ + towerShift υ) ^ i) •
            ∑ s ∈ range (r - i + 1),
              (i + s).choose s • ((towerShift υ ^ s) • towerPullback p c))) r := by
      intro i hi
      have hir : i ≤ r := mem_range_succ_iff.mp hi
      have hagree : towerPullback p (binomialTransform τ r c) (r - i) =
          (∑ s ∈ range (r - i + 1),
            (i + s).choose s • ((towerShift υ ^ s) • towerPullback p c)) (r - i) := by
        rw [towerPullback_binomialTransform τ υ p hpull r c (show r - i ≤ r from by omega)]
        exact congrFun (Finset.sum_congr rfl fun s _ => by
          rw [show r - (r - i) + s = i + s from by omega]) (r - i)
      rw [descentTower_congr (fun j => ξ j + υ j)
          (towerPullback p (binomialTransform τ r c)) _ (r - i) hagree r (by omega),
        Pi.smul_apply, ← hsum, towerShift_pow_apply (fun j => ξ j + υ j) _ i r hir]
    refine Eq.trans ?_ hrelE
    rw [alternatingTowerSum_def, alternatingTowerSum_eq, ← htwist, Finset.sum_apply]
    exact Finset.sum_congr rfl key
  have hzero : (a - binomialTransform τ r c) 0 = 0 := by
    rw [Pi.sub_apply, h0, binomialTransform_apply_zero, sub_self]
  have hrel : alternatingTowerSum (fun j => ξ j + υ j) r
      (towerPullback p (a - binomialTransform τ r c)) = 0 := by
    rw [map_sub, alternatingTowerSum_sub, hrelF, hrelB, sub_zero]
  have hd := huniq _ hzero hrel m hm
  rw [Pi.sub_apply, sub_eq_zero] at hd
  exact hd

end Formula

/-! ### The Chern class cap products of a twist -/

section Chow

/-- **Stacks 02SO and 02TI.** Intersection with the first Chern class of a first Chern class cap
operator, read as a map `A_{d-i}(Y) ⟶ A_{d-(i+1)}(Y)` between the Chow groups in which cap
products of degree `i` and of degree `i + 1` land. This is `Stacks.Chow.firstChernCapStep` for an
operator in place of an invertible module. -/
def ChernCapOperator.towerStep (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] (O : ChernCapOperator C q) (d : ℤ) (i : ℕ) :
    chowGroup C q (d - (i : ℤ)) →+ chowGroup C q (d - ((i + 1 : ℕ) : ℤ)) :=
  chowGroupDegreeCast C q (show d - (i : ℤ) = d - ((i + 1 : ℕ) : ℤ) + 1 from by omega)
    (ChernCapOperator.capOnChow C q O (d - ((i + 1 : ℕ) : ℤ)))

/-- The degrees on the bundle in which the relation of Stacks 02U6 is read for an `n`-cycle on
the base: the `i`-th summand `c₁(𝒪_P(1))^i ∩ π^*(c_{r-i}(ℰ) ∩ α)` of the relation is built from
`π^*(c_{r-i}(ℰ) ∩ α)` in degree `n + (r - 1) - (r - i)`, so the graded family carrying the
relation is `i ↦ A_{n+(r-1)-i}(P)`. -/
def bundleRelationDegree (r : ℕ) (n : ℤ) : ℤ :=
  n + ((r - 1 : ℕ) : ℤ)

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hfacπ : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)

/-- **Stacks 0FVK** along the projection of the bundle, read between the graded families in which
the relation of Stacks 02U6 lives: `π^* : A_{n-i}(X) ⟶ A_{n+(r-1)-i}(P)`. -/
def projectiveBundleTowerPullback (n : ℤ) (i : ℕ) :
    chowGroup C sX (n - (i : ℤ)) →+ chowGroup C sP (bundleRelationDegree r n - (i : ℤ)) :=
  (chowGroupCast C sP (show n - (i : ℤ) + ((r - 1 : ℕ) : ℤ) = bundleRelationDegree r n - (i : ℤ)
      from by simp only [bundleRelationDegree]; ring)).toAddMonoidHom.comp
    (projectiveBundlePullback C sX sP π hsP r hπ hfacπ (n - (i : ℤ)))

/-- **Stacks 02UD.** Let `ℰ` be a finite locally free `𝒪_X`-module of rank `r`, let `ℒ` be
invertible and let `α` be an `n`-cycle on `X`. Then for every `m ≤ r`

  `c_m(ℰ ⊗ ℒ) ∩ α = ∑_{j=0}^{m} binom(r - m + j, j) c₁(ℒ)^j ∩ (c_{m-j}(ℰ) ∩ α)`

in `A_{n-m}(X)`, the right-hand side being the binomial transform of the Chern class cap products
of `ℰ` along `c₁(ℒ) ∩ -`.

The relation of Stacks 02U6 on the projective bundle of `ℰ` is carried for `ℰ` and, transported
along the comparison `𝐏(ℰ) ≅ 𝐏(ℰ ⊗ ℒ)` of Stacks 02NC, for `ℰ ⊗ ℒ`; so is its uniqueness, which
is the injectivity half of Stacks 02TX. See the module documentation. -/
@[stacks 02UD "the two relations of Stacks 02U6 are hypotheses, hrelEL being the one already \
  transported along the comparison of projective bundles of Stacks 02NC, and so is their \
  uniqueness (the injectivity half of Stacks 02TX); the conclusion is the identity capped with \
  an arbitrary cycle, the source's identity in the ring A^*(X) being unstateable here (there is \
  no multiplication on bivariant classes) and the source itself reducing it to this form by \
  Stacks 02UC. Carried besides: hcomm (commutativity of the two first Chern class cap operators \
  on the bundle, Stacks 02UA), hpull (flat pullback carries c_1(L) to c_1(pi^*L), Stacks 02SS \
  and 02RD), h0 (the zeroth cap products of E and of E tensor L both being the class of alpha, \
  Stacks 02U5 (1) at j = 0), the Stacks 02U0 data chernE and chernEL, the rank of E tensor L, \
  and Stacks 02TI for c_1(L) as hfac"]
theorem chernCapFamily_tensorObj_eq_binomialTransform (twist twistL : ChernCapOperator C sP)
    (n : ℤ) (E L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hrankE : PullbackPreservesRank E r)
    (hrankEL : PullbackPreservesRank (Scheme.Modules.tensorObjRingedSpace X E L) r)
    (chernE chernEL : ChernClassCycleRule C r) (hfac : InvertibleChernCapDescends C sX L)
    (α : CycleGroup C sX n)
    (hcomm : ∀ i,
      (ChernCapOperator.towerStep C sP twist (bundleRelationDegree r n) (i + 1)).comp
          (ChernCapOperator.towerStep C sP twistL (bundleRelationDegree r n) i) =
        (ChernCapOperator.towerStep C sP twistL (bundleRelationDegree r n) (i + 1)).comp
          (ChernCapOperator.towerStep C sP twist (bundleRelationDegree r n) i))
    (hpull : ∀ i,
      (projectiveBundleTowerPullback C sX sP π hsP r hπ hfacπ n (i + 1)).comp
          (firstChernCapStep C sX n L hfac i) =
        (ChernCapOperator.towerStep C sP twistL (bundleRelationDegree r n) i).comp
          (projectiveBundleTowerPullback C sX sP π hsP r hπ hfacπ n i))
    (h0 : chernCapFamily C sX n (Scheme.Modules.tensorObjRingedSpace X E L) r hrankEL chernEL α 0 =
      chernCapFamily C sX n E r hrankE chernE α 0)
    (hrelE : alternatingTowerSum
      (ChernCapOperator.towerStep C sP twist (bundleRelationDegree r n)) r
      (towerPullback (projectiveBundleTowerPullback C sX sP π hsP r hπ hfacπ n)
        (chernCapFamily C sX n E r hrankE chernE α)) = 0)
    (hrelEL : alternatingTowerSum
      (fun j => ChernCapOperator.towerStep C sP twist (bundleRelationDegree r n) j +
        ChernCapOperator.towerStep C sP twistL (bundleRelationDegree r n) j) r
      (towerPullback (projectiveBundleTowerPullback C sX sP π hsP r hπ hfacπ n)
        (chernCapFamily C sX n (Scheme.Modules.tensorObjRingedSpace X E L) r hrankEL
          chernEL α)) = 0)
    (huniq : ∀ d : (∀ j : ℕ, chowGroup C sX (n - (j : ℤ))), d 0 = 0 →
      alternatingTowerSum
          (fun j => ChernCapOperator.towerStep C sP twist (bundleRelationDegree r n) j +
            ChernCapOperator.towerStep C sP twistL (bundleRelationDegree r n) j) r
          (towerPullback (projectiveBundleTowerPullback C sX sP π hsP r hπ hfacπ n) d) = 0 →
        ∀ m ≤ r, d m = 0)
    {m : ℕ} (hm : m ≤ r) :
    chernCapFamily C sX n (Scheme.Modules.tensorObjRingedSpace X E L) r hrankEL chernEL α m =
      binomialTransform (firstChernCapStep C sX n L hfac) r
        (chernCapFamily C sX n E r hrankE chernE α) m :=
  eq_binomialTransform_of_towerRelations (G := fun j : ℕ => chowGroup C sX (n - (j : ℤ)))
    (H := fun j : ℕ => chowGroup C sP (bundleRelationDegree r n - (j : ℤ)))
    (firstChernCapStep C sX n L hfac)
    (ChernCapOperator.towerStep C sP twist (bundleRelationDegree r n))
    (ChernCapOperator.towerStep C sP twistL (bundleRelationDegree r n))
    (projectiveBundleTowerPullback C sX sP π hsP r hπ hfacπ n) hcomm hpull r _ _ h0 hrelE hrelEL
    huniq hm

end Chow

end Stacks.Chow

end
