module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Perm.Basic
public import StacksFrontier.RingTheory.PowerSeries.LogDerivative

/-!
# The Euler product of a permutation with finitely many periodic points of each period

Let `σ` be a permutation of a set `S` such that for every `m ≥ 1` only finitely many points are
fixed by `σ^[m]`. Write `A d` for the number of `σ`-invariant finitely supported functions
`D : S →₀ ℕ` of degree `∑ₓ D x = d`, and `N m` for the number of points fixed by `σ^[m]`.
Then `A 0 = 1` and

`T d/dT log (∑_d A d T ^ d) = ∑_{m ≥ 1} N m T ^ m`,

i.e. `∑_d A d T ^ d = exp (∑_{m ≥ 1} N m T ^ m / m)`. This is the combinatorial half of the
rationality of the zeta function of a curve over a finite field: for `S` the closed points of
`C_{𝔽̄_q}` and `σ` the Frobenius, the invariant functions are the effective divisors defined over
`𝔽_q` and `N m` is the number of `𝔽_{q^m}`-points.

The proof is the Euler product over the finite orbits. On a finite `σ`-stable set `F` the
generating series of the invariant functions supported in `F` is multiplicative in disjoint
unions (`Stacks.Zeta.invariantSeries_union`), and for a single orbit of length `e` it is the
geometric series `∑_n T ^ (n e)`, whose logarithmic derivative is `e ∑_{e ∣ m, m ≥ 1} T ^ m`
(`Stacks.Zeta.coeff_logDerivative_invariantSeries_orbit`). Peeling off orbits one at a time gives
the formula on `F` (`Stacks.Zeta.coeff_logDerivative_invariantSeries`); and the coefficient of
`T ^ m` only involves the points of period at most `m`, a finite stable set.

## Main definitions

* `Stacks.Zeta.invariantFinsupps`: the invariant functions supported in a finite set `F`, of
  given degree.
* `Stacks.Zeta.invariantSeries`: their generating series.
* `Stacks.Zeta.invariantCount`: the number `A d`.

## Main results

* `Stacks.Zeta.coeff_logDerivative_invariantSeries`: the formula on a finite stable set.
* `Stacks.Zeta.natCard_invariant_eq_card`, `Stacks.Zeta.invariantCount_zero` and
  `Stacks.Zeta.coeff_logDerivative_invariantCount`: the formula on `S`.
-/

@[expose] public noncomputable section

open PowerSeries Finset Function

namespace Stacks.Zeta

variable {S : Type*} (σ : Equiv.Perm S)

open scoped Classical in
/-- The `σ`-invariant finitely supported functions `D : S →₀ ℕ` with support in `F` and total
mass `∑_{x ∈ F} D x = d`. -/
def invariantFinsupps (F : Finset S) (d : ℕ) : Finset (S →₀ ℕ) :=
  (F.finsuppAntidiag d).filter fun D => ∀ y, D (σ y) = D y

variable {σ} in
/-- `D` lies in `invariantFinsupps σ F d` if and only if `∑_{x ∈ F} D x = d`, the support of `D`
is contained in `F`, and `D` is `σ`-invariant. -/
theorem mem_invariantFinsupps {F : Finset S} {d : ℕ} {D : S →₀ ℕ} :
    D ∈ invariantFinsupps σ F d ↔ F.sum D = d ∧ D.support ⊆ F ∧ ∀ y, D (σ y) = D y := by
  classical
  simp [invariantFinsupps, and_assoc]

/-- The generating series `∑_d #(invariantFinsupps σ F d) T ^ d`. -/
def invariantSeries (F : Finset S) : ℤ⟦X⟧ :=
  PowerSeries.mk fun d => ((invariantFinsupps σ F d).card : ℤ)

/-- The coefficient of `T ^ d` in `invariantSeries σ F` is `#(invariantFinsupps σ F d)`. -/
theorem coeff_invariantSeries (F : Finset S) (d : ℕ) :
    coeff d (invariantSeries σ F) = ((invariantFinsupps σ F d).card : ℤ) :=
  coeff_mk _ _

/-- A finitely supported function vanishes outside any set containing its support. -/
private theorem apply_eq_zero_of_notMem {F : Finset S} {D : S →₀ ℕ} (hsupp : D.support ⊆ F)
    {x : S} (hx : x ∉ F) : D x = 0 :=
  Finsupp.notMem_support_iff.1 fun h => hx (hsupp h)

/-- The only invariant function of mass `0` is `0`. -/
theorem invariantFinsupps_zero (F : Finset S) : invariantFinsupps σ F 0 = {0} := by
  ext D
  rw [mem_invariantFinsupps, Finset.mem_singleton]
  constructor
  · rintro ⟨h0, hsupp, -⟩
    ext x
    by_cases hx : x ∈ F
    · exact (Finset.sum_eq_zero_iff.1 h0) x hx
    · exact apply_eq_zero_of_notMem hsupp hx
  · rintro rfl
    simp

/-- The constant coefficient of `invariantSeries σ F` is `1`. -/
theorem constantCoeff_invariantSeries (F : Finset S) :
    constantCoeff (invariantSeries σ F) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invariantSeries, invariantFinsupps_zero]
  simp

/-- A set `F` is `σ`-stable if `σ` maps it into itself. -/
def IsStable (F : Finset S) : Prop := ∀ y ∈ F, σ y ∈ F

variable {σ}

/-- A stable finite set is also stable under `σ⁻¹`: `σ` permutes it. -/
theorem IsStable.mem_of_apply_mem {F : Finset S} (hF : IsStable σ F) {y : S} (hy : σ y ∈ F) :
    y ∈ F := by
  classical
  have heq : F.image σ = F := Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.2 hF)
    (Finset.card_image_of_injective _ σ.injective).ge
  rw [← heq] at hy
  obtain ⟨w, hw, hwy⟩ := Finset.mem_image.1 hy
  exact σ.injective hwy ▸ hw

/-- A stable finite set is stable under every iterate `σ^[n]`. -/
theorem IsStable.iterate_mem {F : Finset S} (hF : IsStable σ F) {y : S} (hy : y ∈ F) (n : ℕ) :
    (⇑σ)^[n] y ∈ F := by
  induction n with
  | zero => exact hy
  | succ n ih =>
    rw [iterate_succ_apply']
    exact hF _ ih

/-- Every point of a stable finite set is periodic. -/
theorem IsStable.mem_periodicPts {F : Finset S} (hF : IsStable σ F) {y : S} (hy : y ∈ F) :
    y ∈ periodicPts σ := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨(⇑σ)^[n] y, hF.iterate_mem hy n⟩ : F))
  simp only [Subtype.mk.injEq] at h
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · refine mk_mem_periodicPts (n := j - i) (by omega) ?_
    refine (σ.injective.iterate i) ?_
    rw [← iterate_add_apply, Nat.add_sub_cancel' hlt.le, h]
  · refine mk_mem_periodicPts (n := i - j) (by omega) ?_
    refine (σ.injective.iterate j) ?_
    rw [← iterate_add_apply, Nat.add_sub_cancel' hlt.le, h]

/-! ### Disjoint unions -/

section Union

/-- The restriction to a stable set `F₁` of an invariant function supported in the disjoint union
of `F₁` and a second stable set is invariant. -/
theorem filter_invariant [DecidableEq S] {F₁ F₂ : Finset S} (h₁ : IsStable σ F₁)
    (h₂ : IsStable σ F₂) (hdisj : Disjoint F₁ F₂) {D : S →₀ ℕ} (hsupp : D.support ⊆ F₁ ∪ F₂)
    (hD : ∀ y, D (σ y) = D y) (y : S) :
    D.filter (· ∈ F₁) (σ y) = D.filter (· ∈ F₁) y := by
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases hy : y ∈ F₁
  · rw [ite_eq_left (h₁ y hy), ite_eq_left hy, hD]
  by_cases hy₂ : y ∈ F₂
  · have : σ y ∉ F₁ := fun h => Finset.disjoint_left.1 hdisj h (h₂ y hy₂)
    rw [ite_eq_right this, ite_eq_right hy]
  · have h0 := apply_eq_zero_of_notMem hsupp (Finset.notMem_union.2 ⟨hy, hy₂⟩)
    have : σ y ∉ F₁ := fun h => hy (h₁.mem_of_apply_mem h)
    rw [ite_eq_right this, ite_eq_right hy]

/-- The restriction of `D` to `F₁` has the same sum over `F₁` as `D`. -/
theorem sum_filter_eq {F₁ : Finset S} [DecidablePred (· ∈ F₁)] (D : S →₀ ℕ) :
    F₁.sum (D.filter (· ∈ F₁)) = F₁.sum D :=
  Finset.sum_congr rfl fun x hx => by simp [hx]

/-- The restriction of `D` to `F₁` sums to `0` over a set `F₂` disjoint from `F₁`. -/
theorem sum_filter_eq_zero {F₁ F₂ : Finset S} [DecidablePred (· ∈ F₁)] (hdisj : Disjoint F₁ F₂)
    (D : S →₀ ℕ) : F₂.sum (D.filter (· ∈ F₁)) = 0 :=
  Finset.sum_eq_zero fun x hx => by
    simp [Finset.disjoint_right.1 hdisj hx]

/-- **The count on a disjoint union of stable sets** is the convolution of the counts. -/
theorem card_invariantFinsupps_union [DecidableEq S] {F₁ F₂ : Finset S} (h₁ : IsStable σ F₁)
    (h₂ : IsStable σ F₂) (hdisj : Disjoint F₁ F₂) (d : ℕ) :
    (invariantFinsupps σ (F₁ ∪ F₂) d).card = ∑ p ∈ antidiagonal d,
      (invariantFinsupps σ F₁ p.1).card * (invariantFinsupps σ F₂ p.2).card := by
  have H : ((invariantFinsupps σ (F₁ ∪ F₂) d : Finset (S →₀ ℕ)) : Set (S →₀ ℕ)).MapsTo
      (fun D : S →₀ ℕ => (F₁.sum ⇑D, F₂.sum ⇑D)) (antidiagonal d) := fun D hD => by
    obtain ⟨hs, -, -⟩ := mem_invariantFinsupps.1 (Finset.mem_coe.1 hD)
    simpa [mem_antidiagonal, ← Finset.sum_union hdisj] using hs
  rw [Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.card_product]
  refine Finset.card_nbij' (fun D => (D.filter (· ∈ F₁), D.filter (· ∈ F₂)))
    (fun E => E.1 + E.2) ?_ ?_ ?_ ?_
  · intro D hD
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hD
    obtain ⟨hD, hp'⟩ := hD
    obtain ⟨-, hsupp, hinv⟩ := mem_invariantFinsupps.1 hD
    have hp1 : F₁.sum D = p.1 := congrArg Prod.fst hp'
    have hp2 : F₂.sum D = p.2 := congrArg Prod.snd hp'
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_invariantFinsupps]
    refine ⟨⟨by rw [sum_filter_eq, hp1], fun x hx => by
          simp only [Finsupp.support_filter, Finset.mem_filter] at hx
          exact hx.2,
        filter_invariant h₁ h₂ hdisj hsupp hinv⟩,
      ⟨by rw [sum_filter_eq, hp2], fun x hx => by
          simp only [Finsupp.support_filter, Finset.mem_filter] at hx
          exact hx.2,
        filter_invariant h₂ h₁ hdisj.symm (by rwa [Finset.union_comm]) hinv⟩⟩
  · rintro ⟨D₁, D₂⟩ hE
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_invariantFinsupps] at hE
    obtain ⟨⟨hs₁, hsupp₁, hinv₁⟩, ⟨hs₂, hsupp₂, hinv₂⟩⟩ := hE
    have hz₁ : ∀ x ∈ F₂, D₁ x = 0 := fun x hx =>
      apply_eq_zero_of_notMem hsupp₁ (Finset.disjoint_right.1 hdisj hx)
    have hz₂ : ∀ x ∈ F₁, D₂ x = 0 := fun x hx =>
      apply_eq_zero_of_notMem hsupp₂ (Finset.disjoint_left.1 hdisj hx)
    have e₁ : F₁.sum (D₁ + D₂) = p.1 := by
      rw [Finsupp.coe_add, show F₁.sum (⇑D₁ + ⇑D₂) = ∑ x ∈ F₁, (D₁ x + D₂ x) from rfl,
        Finset.sum_add_distrib, Finset.sum_eq_zero hz₂, hs₁, add_zero]
    have e₂ : F₂.sum (D₁ + D₂) = p.2 := by
      rw [Finsupp.coe_add, show F₂.sum (⇑D₁ + ⇑D₂) = ∑ x ∈ F₂, (D₁ x + D₂ x) from rfl,
        Finset.sum_add_distrib, Finset.sum_eq_zero hz₁, hs₂, zero_add]
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_invariantFinsupps]
    refine ⟨⟨?_, ?_, fun y => by simp [hinv₁, hinv₂]⟩, Prod.ext e₁ e₂⟩
    · rw [Finset.sum_union hdisj, e₁, e₂]
      exact mem_antidiagonal.1 hp
    · exact Finsupp.support_add.trans (Finset.union_subset_union hsupp₁ hsupp₂)
  · intro D hD
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hD
    obtain ⟨hsupp, -⟩ := (mem_invariantFinsupps.1 hD.1).2
    ext x
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.filter_apply]
    by_cases hx₁ : x ∈ F₁
    · have : x ∉ F₂ := Finset.disjoint_left.1 hdisj hx₁
      simp [hx₁, this]
    by_cases hx₂ : x ∈ F₂
    · simp [hx₁, hx₂]
    · have := apply_eq_zero_of_notMem hsupp (Finset.notMem_union.2 ⟨hx₁, hx₂⟩)
      simp [hx₁, hx₂, this]
  · rintro ⟨D₁, D₂⟩ hE
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_invariantFinsupps] at hE
    obtain ⟨⟨-, hsupp₁, -⟩, ⟨-, hsupp₂, -⟩⟩ := hE
    refine Prod.ext ?_ ?_
    · ext x
      simp only [Finsupp.filter_apply, Finsupp.coe_add, Pi.add_apply]
      by_cases hx : x ∈ F₁
      · have := apply_eq_zero_of_notMem hsupp₂ (Finset.disjoint_left.1 hdisj hx)
        simp [hx, this]
      · have := apply_eq_zero_of_notMem hsupp₁ hx
        simp [hx, this]
    · ext x
      simp only [Finsupp.filter_apply, Finsupp.coe_add, Pi.add_apply]
      by_cases hx : x ∈ F₂
      · have := apply_eq_zero_of_notMem hsupp₁ (Finset.disjoint_right.1 hdisj hx)
        simp [hx, this]
      · have := apply_eq_zero_of_notMem hsupp₂ hx
        simp [hx, this]

/-- **The generating series is multiplicative in disjoint unions of stable sets.** -/
theorem invariantSeries_union [DecidableEq S] {F₁ F₂ : Finset S} (h₁ : IsStable σ F₁)
    (h₂ : IsStable σ F₂) (hdisj : Disjoint F₁ F₂) :
    invariantSeries σ (F₁ ∪ F₂) = invariantSeries σ F₁ * invariantSeries σ F₂ := by
  ext d
  rw [coeff_mul, coeff_invariantSeries, card_invariantFinsupps_union h₁ h₂ hdisj d]
  push_cast
  exact Finset.sum_congr rfl fun p _ => by rw [coeff_invariantSeries, coeff_invariantSeries]

end Union

/-! ### A single orbit -/

section Orbit

variable (σ) in
/-- The orbit `{σ^[i] x : i < e}` of a point, `e` its minimal period. -/
def orbitFinset [DecidableEq S] (x : S) : Finset S :=
  (Finset.range (minimalPeriod σ x)).image fun i => (⇑σ)^[i] x

variable [DecidableEq S] {x : S}

/-- `y` lies in the orbit of `x` if and only if `y = σ^[i] x` for some `i` less than the minimal
period of `x`. -/
theorem mem_orbitFinset {y : S} :
    y ∈ orbitFinset σ x ↔ ∃ i < minimalPeriod σ x, (⇑σ)^[i] x = y := by
  simp [orbitFinset]

/-- The orbit of `x` has as many elements as the minimal period of `x`. -/
theorem card_orbitFinset : (orbitFinset σ x).card = minimalPeriod σ x := by
  rw [orbitFinset, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact iterate_injOn_Iio_minimalPeriod (f := σ) (x := x) (by simpa using hi) (by simpa using hj)
    hij

/-- Every iterate of a periodic point lies in its orbit. -/
theorem iterate_mem_orbitFinset (hx : x ∈ periodicPts σ) (n : ℕ) :
    (⇑σ)^[n] x ∈ orbitFinset σ x :=
  mem_orbitFinset.2 ⟨n % minimalPeriod σ x,
    Nat.mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hx), iterate_mod_minimalPeriod_eq⟩

/-- A periodic point lies in its own orbit. -/
theorem self_mem_orbitFinset (hx : x ∈ periodicPts σ) : x ∈ orbitFinset σ x :=
  iterate_mem_orbitFinset hx 0

/-- The orbit of a periodic point is `σ`-stable. -/
theorem isStable_orbitFinset (hx : x ∈ periodicPts σ) : IsStable σ (orbitFinset σ x) := by
  intro y hy
  obtain ⟨i, -, rfl⟩ := mem_orbitFinset.1 hy
  rw [← iterate_succ_apply' (⇑σ) i x]
  exact iterate_mem_orbitFinset hx _

/-- The points of the orbit of a periodic point all have its minimal period. -/
theorem minimalPeriod_of_mem_orbitFinset (hx : x ∈ periodicPts σ) {y : S}
    (hy : y ∈ orbitFinset σ x) : minimalPeriod σ y = minimalPeriod σ x := by
  obtain ⟨i, -, rfl⟩ := mem_orbitFinset.1 hy
  exact minimalPeriod_apply_iterate hx i

omit [DecidableEq S] in
/-- An invariant function is constant along an orbit. -/
theorem apply_iterate_eq {D : S →₀ ℕ} (hD : ∀ y, D (σ y) = D y) (n : ℕ) :
    D ((⇑σ)^[n] x) = D x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', hD, ih]

variable (σ) in
/-- The function with value `n` on the orbit of `x` and `0` elsewhere. -/
def orbitConst (x : S) (n : ℕ) : S →₀ ℕ := ∑ y ∈ orbitFinset σ x, Finsupp.single y n

/-- `orbitConst σ x n` takes the value `n` on the orbit of `x` and `0` elsewhere. -/
theorem orbitConst_apply (n : ℕ) (z : S) :
    orbitConst σ x n z = if z ∈ orbitFinset σ x then n else 0 := by
  simp [orbitConst, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- An invariant function supported in the orbit of `x` is the constant function on that orbit with
value `D x`. -/
theorem eq_orbitConst {D : S →₀ ℕ} (hsupp : D.support ⊆ orbitFinset σ x)
    (hD : ∀ y, D (σ y) = D y) : D = orbitConst σ x (D x) := by
  ext z
  rw [orbitConst_apply]
  split_ifs with hz
  · obtain ⟨i, -, rfl⟩ := mem_orbitFinset.1 hz
    exact apply_iterate_eq hD i
  · exact apply_eq_zero_of_notMem hsupp hz

/-- For a periodic point `x` of minimal period `e`, the function `orbitConst σ x n` is an invariant
function supported in the orbit of `x` of mass `e * n`. -/
theorem orbitConst_mem (hx : x ∈ periodicPts σ) (n : ℕ) :
    orbitConst σ x n ∈ invariantFinsupps σ (orbitFinset σ x) (minimalPeriod σ x * n) := by
  rw [mem_invariantFinsupps]
  have hst := isStable_orbitFinset hx
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [Finset.sum_congr rfl fun z hz => by rw [orbitConst_apply, ite_eq_left hz], Finset.sum_const,
      card_orbitFinset, smul_eq_mul]
  · intro z hz
    by_contra h
    exact (Finsupp.mem_support_iff.1 hz) (by rw [orbitConst_apply, ite_eq_right h])
  · rw [orbitConst_apply, orbitConst_apply]
    by_cases hy : y ∈ orbitFinset σ x
    · rw [ite_eq_left (hst y hy), ite_eq_left hy]
    · rw [ite_eq_right fun h => hy (hst.mem_of_apply_mem h), ite_eq_right hy]

/-- **The invariant functions on one orbit**: there is exactly one of each mass divisible by the
period, and none of any other mass. -/
theorem card_invariantFinsupps_orbitFinset (hx : x ∈ periodicPts σ) (d : ℕ) :
    (invariantFinsupps σ (orbitFinset σ x) d).card =
      if minimalPeriod σ x ∣ d then 1 else 0 := by
  have hpos := minimalPeriod_pos_of_mem_periodicPts hx
  have hmass : ∀ D ∈ invariantFinsupps σ (orbitFinset σ x) d, d = minimalPeriod σ x * D x := by
    intro D hD
    obtain ⟨hs, hsupp, hinv⟩ := mem_invariantFinsupps.1 hD
    have h := orbitConst_mem (σ := σ) hx (D x)
    rw [← eq_orbitConst hsupp hinv] at h
    exact hs.symm.trans (mem_invariantFinsupps.1 h).1
  split_ifs with hdvd
  · obtain ⟨n, rfl⟩ := hdvd
    rw [Finset.card_eq_one]
    refine ⟨orbitConst σ x n, Finset.eq_singleton_iff_unique_mem.2 ⟨orbitConst_mem hx n,
      fun D hD => ?_⟩⟩
    obtain ⟨-, hsupp, hinv⟩ := mem_invariantFinsupps.1 hD
    rw [eq_orbitConst hsupp hinv, Nat.eq_of_mul_eq_mul_left hpos (hmass D hD).symm]
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro D hD
    exact hdvd ⟨_, hmass D hD⟩

/-- Multiplying the geometric series `∑_n T ^ (n e)` by `T ^ e` removes its constant term. -/
private theorem coeff_geometric_mul_X_pow (e : ℕ) (he : 0 < e) (m : ℕ) :
    coeff m (PowerSeries.mk (fun d => if e ∣ d then (1 : ℤ) else 0) * X ^ e) =
      if e ∣ m ∧ m ≠ 0 then 1 else 0 := by
  rw [coeff_mul_X_pow']
  by_cases hm : e ≤ m
  · have h : e ∣ m ↔ e ∣ m - e := by
      conv_lhs => rw [← Nat.sub_add_cancel hm]
      exact Nat.dvd_add_left (dvd_refl e)
    rw [ite_eq_left hm, coeff_mk]
    by_cases h' : e ∣ m
    · rw [ite_eq_left (h.1 h'), ite_eq_left ⟨h', by omega⟩]
    · rw [ite_eq_right fun x => h' (h.2 x), ite_eq_right fun h2 => h' h2.1]
  · rw [ite_eq_right hm]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · rw [ite_eq_right fun h => hm (Nat.le_of_dvd hm0 h.1)]

/-- The geometric series `∑_n T ^ (n e)` is the inverse of `1 - T ^ e`. -/
theorem mk_dvd_mul_one_sub_X_pow (e : ℕ) (he : 0 < e) :
    PowerSeries.mk (fun d => if e ∣ d then (1 : ℤ) else 0) * (1 - X ^ e) = 1 := by
  ext d
  rw [mul_sub, mul_one, map_sub, coeff_geometric_mul_X_pow e he, coeff_mk, coeff_one]
  by_cases hd : d = 0 <;> simp [hd]

/-- The generating series of the invariant functions on the orbit of a periodic point of minimal
period `e` is the geometric series `∑_n T ^ (n e)`. -/
theorem invariantSeries_orbitFinset (hx : x ∈ periodicPts σ) :
    invariantSeries σ (orbitFinset σ x) =
      PowerSeries.mk (fun d => if minimalPeriod σ x ∣ d then (1 : ℤ) else 0) := by
  ext d
  rw [coeff_invariantSeries, card_invariantFinsupps_orbitFinset hx, coeff_mk]
  split_ifs <;> simp

/-- The logarithmic derivative of `∑_n T ^ (n e)` is `e ∑_{n ≥ 1} T ^ (n e)`. -/
theorem coeff_logDerivative_geometric (e : ℕ) (he : 0 < e) (m : ℕ) :
    coeff m (logDerivative (PowerSeries.mk (fun d => if e ∣ d then (1 : ℤ) else 0))) =
      if e ∣ m ∧ m ≠ 0 then (e : ℤ) else 0 := by
  set u := PowerSeries.mk (fun d => if e ∣ d then (1 : ℤ) else 0)
  have hu : constantCoeff u = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, ite_eq_left (dvd_zero e)]
  have hv : constantCoeff (1 - X ^ e : ℤ⟦X⟧) = 1 := by
    simp [he.ne']
  have hmul := mk_dvd_mul_one_sub_X_pow e he
  have hsum := logDerivative_mul hu hv
  rw [hmul, logDerivative_one] at hsum
  have hinv : invOfUnit (1 - X ^ e : ℤ⟦X⟧) 1 = u := by
    calc invOfUnit (1 - X ^ e : ℤ⟦X⟧) 1 = u * (1 - X ^ e) * invOfUnit (1 - X ^ e) 1 := by
          rw [hmul, one_mul]
      _ = u := by rw [mul_assoc, mul_invOfUnit_one hv, mul_one]
  have hv' : logDerivative (1 - X ^ e : ℤ⟦X⟧) = -((e : ℤ⟦X⟧) * X ^ e * u) := by
    rw [logDerivative, hinv, map_sub, derivative_one, derivative_pow, derivative_X]
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    simp only [Nat.add_sub_cancel, zero_sub]
    push_cast
    ring
  have hu' : logDerivative u = (e : ℤ⟦X⟧) * X ^ e * u := by
    linear_combination -hsum - hv'
  rw [hu', ← map_natCast (C (R := ℤ)), mul_assoc, coeff_C_mul, mul_comm (X ^ e),
    show coeff m (u * X ^ e) = _ from coeff_geometric_mul_X_pow e he m]
  split_ifs <;> simp

/-- The number of points of an orbit fixed by `σ^[m]`. -/
theorem card_filter_orbitFinset (hx : x ∈ periodicPts σ) (m : ℕ) :
    ((orbitFinset σ x).filter fun y => (⇑σ)^[m] y = y).card =
      if minimalPeriod σ x ∣ m then minimalPeriod σ x else 0 := by
  have key : ∀ y ∈ orbitFinset σ x, ((⇑σ)^[m] y = y ↔ minimalPeriod σ x ∣ m) := fun y hy => by
    rw [← minimalPeriod_of_mem_orbitFinset hx hy, ← isPeriodicPt_iff_minimalPeriod_dvd]
    rfl
  split_ifs with h
  · rw [Finset.filter_true_of_mem fun y hy => (key y hy).2 h, card_orbitFinset]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun y hy hc => h ((key y hy).1 hc)

/-- **The formula on a single orbit.** -/
theorem coeff_logDerivative_invariantSeries_orbit (hx : x ∈ periodicPts σ) (m : ℕ) :
    coeff m (logDerivative (invariantSeries σ (orbitFinset σ x))) =
      if m = 0 then 0 else
        (((orbitFinset σ x).filter fun y => (⇑σ)^[m] y = y).card : ℤ) := by
  rw [invariantSeries_orbitFinset hx,
    coeff_logDerivative_geometric _ (minimalPeriod_pos_of_mem_periodicPts hx),
    card_filter_orbitFinset hx]
  by_cases hm : m = 0 <;> by_cases h : minimalPeriod σ x ∣ m <;> simp [hm, h]

end Orbit

/-! ### Finite stable sets -/

/-- **The formula on a finite stable set**: the coefficient of `T ^ m`, `m ≥ 1`, of the
logarithmic derivative of the generating series of the invariant functions supported in `F` is
the number of points of `F` fixed by `σ^[m]`. -/
theorem coeff_logDerivative_invariantSeries [DecidableEq S] {F : Finset S} (hF : IsStable σ F)
    (m : ℕ) :
    coeff m (logDerivative (invariantSeries σ F)) =
      if m = 0 then 0 else ((F.filter fun y => (⇑σ)^[m] y = y).card : ℤ) := by
  induction h : F.card using Nat.strong_induction_on generalizing F with
  | _ n ih =>
  rcases F.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · have : invariantSeries σ (∅ : Finset S) = 1 := by
      ext d
      rw [coeff_invariantSeries, coeff_one]
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp [invariantFinsupps_zero]
      · rw [ite_eq_right hd.ne', Nat.cast_eq_zero, Finset.card_eq_zero,
          Finset.eq_empty_iff_forall_notMem]
        intro D hD
        have := (mem_invariantFinsupps.1 hD).1
        simp at this
        omega
    simp [this]
  have hper := hF.mem_periodicPts hx
  set O := orbitFinset σ x
  have hO := isStable_orbitFinset hper
  have hOF : O ⊆ F := fun y hy => by
    obtain ⟨i, -, rfl⟩ := mem_orbitFinset.1 hy
    exact hF.iterate_mem hx i
  set F' := F \ O
  have hF' : IsStable σ F' := fun y hy => by
    rw [Finset.mem_sdiff] at hy ⊢
    exact ⟨hF y hy.1, fun h => hy.2 (hO.mem_of_apply_mem h)⟩
  have hdisj : Disjoint O F' := Finset.disjoint_sdiff
  have hunion : F = O ∪ F' := (Finset.union_sdiff_of_subset hOF).symm
  have hcard : F'.card < n := by
    rw [← h, Finset.card_sdiff_of_subset hOF]
    have : 0 < O.card := Finset.card_pos.2 ⟨x, self_mem_orbitFinset hper⟩
    have := Finset.card_le_card hOF
    omega
  rw [hunion, invariantSeries_union hO hF' hdisj,
    logDerivative_mul (constantCoeff_invariantSeries σ O) (constantCoeff_invariantSeries σ F'),
    map_add, coeff_logDerivative_invariantSeries_orbit hper, ih _ hcard hF' rfl,
    Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
  split_ifs
  · simp
  · push_cast
    ring

/-! ### The whole set -/

section Global

variable (σ)

/-- The invariant functions of degree `d`. -/
def invariantSet (d : ℕ) : Set (S →₀ ℕ) :=
  {D | Finsupp.degree D = d ∧ ∀ y, D (σ y) = D y}

/-- The number `A d` of invariant functions of degree `d`. -/
def invariantCount (d : ℕ) : ℕ := Nat.card (invariantSet σ d)

variable {σ}

/-- The support of an invariant function of degree `d` consists of points of period at most
`d`. -/
theorem exists_iterate_eq_of_mem_support {d : ℕ} {D : S →₀ ℕ} (hD : D ∈ invariantSet σ d)
    {y : S} (hy : y ∈ D.support) :
    ∃ k, 0 < k ∧ k ≤ d ∧ (⇑σ)^[k] y = y := by
  classical
  obtain ⟨hdeg, hinv⟩ := hD
  have hfin : IsStable σ D.support := fun z hz => by
    rw [Finsupp.mem_support_iff] at hz ⊢
    rwa [hinv]
  have hper := hfin.mem_periodicPts hy
  refine ⟨minimalPeriod σ y, minimalPeriod_pos_of_mem_periodicPts hper, ?_,
    iterate_minimalPeriod⟩
  have hsub : orbitFinset σ y ⊆ D.support := fun z hz => by
    obtain ⟨i, -, rfl⟩ := mem_orbitFinset.1 hz
    exact hfin.iterate_mem hy i
  have hpos : 1 ≤ D y := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hy)
  calc minimalPeriod σ y = ∑ z ∈ orbitFinset σ y, 1 := by simp [card_orbitFinset]
    _ ≤ ∑ z ∈ orbitFinset σ y, D z := Finset.sum_le_sum fun z hz => by
        obtain ⟨i, -, rfl⟩ := mem_orbitFinset.1 hz
        rw [apply_iterate_eq hinv]
        exact hpos
    _ ≤ ∑ z ∈ D.support, D z := Finset.sum_le_sum_of_subset hsub
    _ = d := hdeg

variable (hfin : ∀ m, 0 < m → {y | (⇑σ)^[m] y = y}.Finite)
include hfin

/-- The points of period at most `d` form a finite set. -/
theorem finite_periodLE (d : ℕ) : {y | ∃ k, 0 < k ∧ k ≤ d ∧ (⇑σ)^[k] y = y}.Finite := by
  refine ((Set.finite_Icc 1 d).biUnion' fun k hk => hfin k hk.1).subset ?_
  rintro y ⟨k, hk, hkd, hy⟩
  exact Set.mem_biUnion (x := k) ⟨hk, hkd⟩ hy

variable (σ) in
/-- The finite set of points of period at most `d`. -/
def periodLE (d : ℕ) : Finset S := (finite_periodLE hfin d).toFinset

/-- `y` lies in `periodLE σ hfin d` if and only if `σ^[k] y = y` for some `0 < k ≤ d`. -/
theorem mem_periodLE {d : ℕ} {y : S} :
    y ∈ periodLE σ hfin d ↔ ∃ k, 0 < k ∧ k ≤ d ∧ (⇑σ)^[k] y = y := by
  simp [periodLE]

/-- The set of points of period at most `d` is `σ`-stable. -/
theorem isStable_periodLE (d : ℕ) : IsStable σ (periodLE σ hfin d) := by
  intro y hy
  obtain ⟨k, hk, hkd, h⟩ := (mem_periodLE hfin).1 hy
  refine (mem_periodLE hfin).2 ⟨k, hk, hkd, ?_⟩
  rw [← iterate_succ_apply, iterate_succ_apply', h]

/-- The set of points of period at most `d` is monotone in `d`. -/
theorem periodLE_mono {d e : ℕ} (h : d ≤ e) : periodLE σ hfin d ⊆ periodLE σ hfin e :=
  fun y hy => by
    obtain ⟨k, hk, hkd, hky⟩ := (mem_periodLE hfin).1 hy
    exact (mem_periodLE hfin).2 ⟨k, hk, hkd.trans h, hky⟩

/-- An invariant function of degree `d` lies in `invariantFinsupps σ F d` as soon as `F` contains
the points of period at most `d`. -/
private theorem mem_invariantFinsupps_of_mem_invariantSet {d : ℕ} {F : Finset S} {D : S →₀ ℕ}
    (hF : periodLE σ hfin d ⊆ F) (hD : D ∈ invariantSet σ d) : D ∈ invariantFinsupps σ F d := by
  have hsupp : D.support ⊆ F := fun y hy => hF ((mem_periodLE hfin).2
    (exists_iterate_eq_of_mem_support hD hy))
  exact mem_invariantFinsupps.2 ⟨(Finset.sum_subset hsupp fun y _ hy =>
    Finsupp.notMem_support_iff.1 hy).symm.trans hD.1, hsupp, hD.2⟩

/-- **The invariant functions of degree `d` are finite in number**, and are counted by the
invariant functions supported in any finite set containing the points of period at most `d`. -/
theorem natCard_invariant_eq_card {d : ℕ} {F : Finset S} (hF : periodLE σ hfin d ⊆ F) :
    invariantCount σ d = (invariantFinsupps σ F d).card := by
  rw [invariantCount, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun D => ?_)
  refine ⟨mem_invariantFinsupps_of_mem_invariantSet hfin hF, ?_⟩
  rw [mem_invariantFinsupps]
  rintro ⟨hs, hsupp, hinv⟩
  exact ⟨(Finset.sum_subset hsupp fun y _ hy => Finsupp.notMem_support_iff.1 hy).trans hs, hinv⟩

/-- There are only finitely many invariant functions of degree `d`. -/
theorem finite_invariantSet (d : ℕ) : (invariantSet σ d).Finite := by
  classical
  refine (invariantFinsupps σ (periodLE σ hfin d) d).finite_toSet.subset fun D hD => ?_
  exact mem_invariantFinsupps_of_mem_invariantSet hfin subset_rfl hD

omit hfin in
/-- There is exactly one invariant function of degree `0`. -/
theorem invariantCount_zero : invariantCount σ 0 = 1 := by
  rw [invariantCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, by simp [invariantSet]⟩, fun ⟨D, hD⟩ => Subtype.ext ?_⟩
  exact (Finsupp.degree_eq_zero_iff D).1 hD.1

/-- **The logarithmic derivative of the zeta series of a permutation.** If `σ^[m]` has finitely
many fixed points for every `m ≥ 1`, then the coefficient of `T ^ m`, `m ≥ 1`, of
`T d/dT log ∑_d A d T ^ d` is the number of fixed points of `σ^[m]`. -/
theorem coeff_logDerivative_invariantCount {m : ℕ} (hm : m ≠ 0) :
    coeff m (logDerivative (PowerSeries.mk fun d => (invariantCount σ d : ℤ))) =
      Nat.card {y | (⇑σ)^[m] y = y} := by
  classical
  set F := periodLE σ hfin m
  have hcongr : (X : ℤ⟦X⟧) ^ (m + 1) ∣
      PowerSeries.mk (fun d => (invariantCount σ d : ℤ)) - invariantSeries σ F := by
    refine X_pow_dvd_iff.2 fun d hd => ?_
    rw [map_sub, coeff_mk, coeff_invariantSeries,
      natCard_invariant_eq_card hfin (periodLE_mono hfin (Nat.lt_succ_iff.1 hd)), sub_self]
  have h0 : constantCoeff (PowerSeries.mk fun d => (invariantCount σ d : ℤ)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, invariantCount_zero, Nat.cast_one]
  rw [coeff_logDerivative_congr h0 (constantCoeff_invariantSeries σ F) hcongr,
    coeff_logDerivative_invariantSeries (isStable_periodLE hfin m), ite_eq_right hm]
  have hsub : {y | (⇑σ)^[m] y = y} = ((F.filter fun y => (⇑σ)^[m] y = y : Finset S) : Set S) := by
    ext y
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, iff_and_self]
    exact fun hy => (mem_periodLE hfin).2 ⟨m, Nat.pos_of_ne_zero hm, le_rfl, hy⟩
  rw [hsub, Nat.card_coe_set_eq, Set.ncard_coe_finset]

end Global

end Stacks.Zeta

end
