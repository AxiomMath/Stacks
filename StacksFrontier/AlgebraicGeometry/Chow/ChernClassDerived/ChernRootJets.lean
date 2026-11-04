module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.SplittingPrinciplePerfect
public import Mathlib.RingTheory.Binomial

/-!
# Signed Chern roots, their low-degree Chern classes and their power sums

Let `x₁, …, x_n` be commuting elements of a ring and `ε₁, …, ε_n ∈ {±1}`. Formally,
`∏ (1 + x_a)^{ε_a}` is the total Chern class of a virtual bundle with Chern roots `x_a` counted
with the signs `ε_a`, and `∏_{a, b} (1 + x_a + y_b)^{ε_a δ_b}` is the total Chern class of the
tensor product of two such. This file records, for lists of signed roots,

* the components of degree `≤ 2` of `∏ (1 + x_a)^{ε_a}`: `c₁ = ∑ ε_a x_a` and the recursion for
  `c₂`;
* the power sums `P_p = ∑ ε_a x_a^p`;
* the "formal computation in polynomial rings" to which the proof of [Stacks, Tag 0FAG] reduces
  the lemma: for the tensor product of two lists of signed roots, of ranks `r = ∑ ε_a` and
  `s = ∑ δ_b`,

    `c₁ = r c₁' + s c₁`,
    `c₂ = r c₂' + s c₂ + C(r, 2) c₁'² + (r s - 1) c₁' c₁ + C(s, 2) c₁²`,
    `P_p = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁} P'_{p₂}`.

The identities are proved in an arbitrary commutative ring, and transported to the ring of total
Chow cohomology classes, where the roots are first Chern classes of invertible modules and commute
pairwise without the ring being commutative, through the commutative subring they generate.

## Main definitions

* `Stacks.Chow.rootRank`, `Stacks.Chow.rootSum`, `Stacks.Chow.rootSumTwo`,
  `Stacks.Chow.rootPow` — the rank, `c₁`, `c₂` and the power sums of a list of signed roots.
* `Stacks.Chow.rootTensor` — the signed roots `x_a + y_b` of a tensor product.
* `Stacks.Chow.TotalChowClass.oneAddUnit`, `Stacks.Chow.TotalChowClass.rootProd` — the units
  `1 + x` and `∏ (1 + x_a)^{ε_a}` in the ring of total classes.

## References

* [Stacks Project, Tag 0FAG](https://stacks.math.columbia.edu/tag/0FAG)
* [Stacks Project, Tag 0FAD](https://stacks.math.columbia.edu/tag/0FAD)
-/

@[expose] public noncomputable section

open Finset

universe u

namespace Stacks.Chow

/-! ### Lists of signed roots in a ring -/

section RootLists

variable {A : Type*} [Ring A]

/-- The rank `∑ ε_a` of a list of signed roots. -/
def rootRank (l : List (ℤˣ × A)) : ℤ := (l.map fun t ↦ (t.1 : ℤ)).sum

/-- The first Chern class `∑ ε_a x_a` of a list of signed roots. -/
def rootSum (l : List (ℤˣ × A)) : A := (l.map fun t ↦ ((t.1 : ℤ) : A) * t.2).sum

/-- The second Chern class of a list of signed roots, by the recursion
`c₂((ε, x) :: l) = C(ε, 2) x² + ε x c₁(l) + c₂(l)`, where `C(1, 2) = 0` and `C(-1, 2) = 1`. -/
def rootSumTwo : List (ℤˣ × A) → A
  | [] => 0
  | t :: l => (if (t.1 : ℤ) = 1 then 0 else t.2 * t.2) + ((t.1 : ℤ) : A) * t.2 * rootSum l +
      rootSumTwo l

/-- The power sum `∑ ε_a x_a^p` of a list of signed roots. -/
def rootPow (l : List (ℤˣ × A)) (p : ℕ) : A := (l.map fun t ↦ ((t.1 : ℤ) : A) * t.2 ^ p).sum

/-- The signed roots `(ε_a δ_b, x_a + y_b)` of the tensor product of two lists of signed roots. -/
def rootTensor (l l' : List (ℤˣ × A)) : List (ℤˣ × A) :=
  l.flatMap fun t ↦ l'.map fun t' ↦ (t.1 * t'.1, t.2 + t'.2)

omit [Ring A] in
/-- The empty list of signed roots has rank zero. -/
@[simp] theorem rootRank_nil : rootRank ([] : List (ℤˣ × A)) = 0 := rfl
/-- The empty list of signed roots has first Chern class zero. -/
@[simp] theorem rootSum_nil : rootSum ([] : List (ℤˣ × A)) = 0 := rfl
/-- The empty list of signed roots has second Chern class zero. -/
@[simp] theorem rootSumTwo_nil : rootSumTwo ([] : List (ℤˣ × A)) = 0 := rfl
/-- Every power sum of the empty list of signed roots is zero. -/
@[simp] theorem rootPow_nil (p : ℕ) : rootPow ([] : List (ℤˣ × A)) p = 0 := rfl
/-- The tensor product of the empty list of signed roots with any list is empty. -/
@[simp] theorem rootTensor_nil (l' : List (ℤˣ × A)) : rootTensor [] l' = [] := rfl

omit [Ring A] in
/-- The rank of `(ε, x) :: l` is `ε` plus the rank of `l`. -/
theorem rootRank_cons (t : ℤˣ × A) (l : List (ℤˣ × A)) :
    rootRank (t :: l) = t.1 + rootRank l := by
  simp [rootRank]

/-- The first Chern class of `(ε, x) :: l` is `ε x` plus the first Chern class of `l`. -/
theorem rootSum_cons (t : ℤˣ × A) (l : List (ℤˣ × A)) :
    rootSum (t :: l) = ((t.1 : ℤ) : A) * t.2 + rootSum l := by
  simp [rootSum]

/-- The second Chern class of `(ε, x) :: l` is `C(ε, 2) x² + ε x c₁(l) + c₂(l)`. -/
theorem rootSumTwo_cons (t : ℤˣ × A) (l : List (ℤˣ × A)) :
    rootSumTwo (t :: l) = (if (t.1 : ℤ) = 1 then 0 else t.2 * t.2) +
      ((t.1 : ℤ) : A) * t.2 * rootSum l + rootSumTwo l := rfl

/-- The power sum `P_p` of `(ε, x) :: l` is `ε x^p` plus the power sum `P_p` of `l`. -/
theorem rootPow_cons (t : ℤˣ × A) (l : List (ℤˣ × A)) (p : ℕ) :
    rootPow (t :: l) p = ((t.1 : ℤ) : A) * t.2 ^ p + rootPow l p := by
  simp [rootPow]

/-- The tensor product of `(ε, x) :: l` with `l'` is the list of `(ε δ_b, x + y_b)` for
`(δ_b, y_b)` in `l'`, followed by the tensor product of `l` with `l'`. -/
theorem rootTensor_cons (t : ℤˣ × A) (l l' : List (ℤˣ × A)) :
    rootTensor (t :: l) l' = (l'.map fun t' ↦ (t.1 * t'.1, t.2 + t'.2)) ++ rootTensor l l' := by
  simp [rootTensor]

omit [Ring A] in
/-- The rank of a concatenation of lists of signed roots is the sum of the ranks. -/
theorem rootRank_append (l l' : List (ℤˣ × A)) :
    rootRank (l ++ l') = rootRank l + rootRank l' := by
  simp [rootRank]

/-- The first Chern class of a concatenation of lists of signed roots is the sum of the first
Chern classes. -/
theorem rootSum_append (l l' : List (ℤˣ × A)) : rootSum (l ++ l') = rootSum l + rootSum l' := by
  simp [rootSum]

/-- Each power sum of a concatenation of lists of signed roots is the sum of the power sums. -/
theorem rootPow_append (l l' : List (ℤˣ × A)) (p : ℕ) :
    rootPow (l ++ l') p = rootPow l p + rootPow l' p := by
  simp [rootPow]

/-- The second Chern class of a concatenation: `c₂(l ++ l') = c₂(l) + c₁(l) c₁(l') + c₂(l')`. -/
theorem rootSumTwo_append (l l' : List (ℤˣ × A)) :
    rootSumTwo (l ++ l') = rootSumTwo l + rootSum l * rootSum l' + rootSumTwo l' := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.cons_append, rootSumTwo_cons, rootSumTwo_cons, ih, rootSum_append, rootSum_cons]
    noncomm_ring

/-- The rank of a list of signed roots is its power sum of degree zero. -/
theorem rootPow_zero (l : List (ℤˣ × A)) : rootPow l 0 = (rootRank l : A) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [rootPow_cons, rootRank_cons, ih, pow_zero, mul_one]
    push_cast
    rfl

/-- The power sum of degree one of a list of signed roots is its first Chern class. -/
theorem rootPow_one (l : List (ℤˣ × A)) : rootPow l 1 = rootSum l := by
  simp [rootPow, rootSum]

/-- The rank of the tensor product of two lists of signed roots is the product of the ranks. -/
theorem rootRank_rootTensor (l l' : List (ℤˣ × A)) :
    rootRank (rootTensor l l') = rootRank l * rootRank l' := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [rootTensor_cons, rootRank_append, ih, rootRank_cons, add_mul]
    congr 1
    clear ih
    induction l' with
    | nil => simp
    | cons t' l' ih' =>
      rw [List.map_cons, rootRank_cons, ih', rootRank_cons, Units.val_mul, mul_add]

variable {B : Type*} [Ring B] (f : A →+* B)

/-- The image of a list of signed roots under a ring homomorphism. -/
abbrev rootMap (l : List (ℤˣ × A)) : List (ℤˣ × B) := l.map fun t ↦ (t.1, f t.2)

/-- The rank of a list of signed roots is unchanged by a ring homomorphism. -/
theorem rootRank_rootMap (l : List (ℤˣ × A)) : rootRank (rootMap f l) = rootRank l := by
  simp [rootRank, Function.comp_def]

/-- A ring homomorphism maps the first Chern class of a list of signed roots to the first Chern
class of the image list. -/
theorem rootSum_rootMap (l : List (ℤˣ × A)) : rootSum (rootMap f l) = f (rootSum l) := by
  simp [rootSum, map_list_sum, Function.comp_def]

/-- A ring homomorphism maps the second Chern class of a list of signed roots to the second Chern
class of the image list. -/
theorem rootSumTwo_rootMap (l : List (ℤˣ × A)) :
    rootSumTwo (rootMap f l) = f (rootSumTwo l) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    show rootSumTwo ((t.1, f t.2) :: rootMap f l) = _
    rw [rootSumTwo_cons, rootSumTwo_cons, ih, rootSum_rootMap]
    split_ifs <;> simp

/-- A ring homomorphism maps each power sum of a list of signed roots to the corresponding power
sum of the image list. -/
theorem rootPow_rootMap (l : List (ℤˣ × A)) (p : ℕ) :
    rootPow (rootMap f l) p = f (rootPow l p) := by
  simp [rootPow, map_list_sum, Function.comp_def]

/-- The tensor product of lists of signed roots commutes with the image under a ring
homomorphism. -/
theorem rootTensor_rootMap (l l' : List (ℤˣ × A)) :
    rootTensor (rootMap f l) (rootMap f l') = rootMap f (rootTensor l l') := by
  simp [rootTensor, List.map_flatMap, List.flatMap_map, Function.comp_def]

end RootLists

/-! ### The formal computation for a tensor product, in a commutative ring -/

section Commutative

variable {K : Type*} [CommRing K]

/-- `C(ε + r, 2) = C(r, 2) + C(ε, 2) + ε r` for a sign `ε`, where `C(1, 2) = 0` and
`C(-1, 2) = 1`. -/
theorem ringChoose_unit_add_two (ε : ℤˣ) (r : ℤ) :
    Ring.choose ((ε : ℤ) + r) 2 = Ring.choose r 2 + (if (ε : ℤ) = 1 then 0 else 1) + ε * r := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · have h := Ring.choose_succ_succ r 1
    rw [Ring.choose_one_right] at h
    simp only [Units.val_one, if_true, add_zero, one_mul]
    rw [add_comm (1 : ℤ) r, h]
    ring
  · have h := Ring.choose_succ_succ (-1 + r) 1
    rw [Ring.choose_one_right] at h
    simp only [Units.val_neg, Units.val_one, show ((-1 : ℤ) = 1) = False by decide, if_false,
      neg_one_mul]
    rw [show -1 + r + 1 = r by ring] at h
    rw [h]
    ring

/-- `2 C(n, 2) = n (n - 1)` for an integer `n`. -/
theorem two_mul_ringChoose_two (n : ℤ) : 2 * Ring.choose n 2 = n * (n - 1) := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose n 2
  rw [Nat.factorial_two, nsmul_eq_mul] at h
  push_cast at h
  rw [← h, descPochhammer_succ_right, descPochhammer_one]
  simp [Polynomial.smeval_mul, Polynomial.smeval_X, Polynomial.smeval_sub]

/-- `c₁` of the signed roots `x + y_b` of `(ε, x) ⊗ l'`. -/
theorem rootSum_map_tensor (ε : ℤˣ) (x : K) (l' : List (ℤˣ × K)) :
    rootSum (l'.map fun t' ↦ (ε * t'.1, x + t'.2)) =
      ((ε : ℤ) : K) * ((rootRank l' : K) * x + rootSum l') := by
  induction l' with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, rootSum_cons, ih, rootRank_cons, rootSum_cons]
    push_cast
    ring

/-- `c₂` of the signed roots `x + y_b` of `(ε, x) ⊗ l'`: the formula of Stacks 0FAG for a single
signed root on the left. -/
theorem rootSumTwo_map_tensor (ε : ℤˣ) (x : K) (l' : List (ℤˣ × K)) :
    rootSumTwo (l'.map fun t' ↦ (ε * t'.1, x + t'.2)) =
      ((ε : ℤ) : K) * rootSumTwo l' + (rootRank l' : K) * ((if (ε : ℤ) = 1 then 0 else 1) * x ^ 2)
        + (if (ε : ℤ) = 1 then 0 else 1) * rootSum l' ^ 2
        + (((ε : ℤ) : K) * rootRank l' - 1) * (rootSum l' * (((ε : ℤ) : K) * x))
        + ((Ring.choose (rootRank l') 2 : ℤ) : K) * (((ε : ℤ) : K) * x) ^ 2 := by
  induction l' with
  | nil => simp [Ring.choose_zero_succ]
  | cons t l ih =>
    rw [List.map_cons, rootSumTwo_cons, ih, rootSum_map_tensor, rootSumTwo_cons, rootSum_cons,
      rootRank_cons, ringChoose_unit_add_two]
    rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or t.1 with h | h <;>
      simp only [h, Units.val_one, Units.val_neg, mul_one, mul_neg, neg_neg, one_mul, neg_mul,
        if_true, if_false, show ((-1 : ℤ) = 1) = False by decide] <;> push_cast <;> ring

/-- **The formal computation of Stacks 0FAG in degree one**: for the tensor product of two lists
of signed roots of ranks `r` and `s`, `c₁ = s c₁ + r c₁'`. -/
theorem rootSum_rootTensor (l l' : List (ℤˣ × K)) :
    rootSum (rootTensor l l') = (rootRank l' : K) * rootSum l + (rootRank l : K) * rootSum l' := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [rootTensor_cons, rootSum_append, rootSum_map_tensor, ih, rootSum_cons, rootRank_cons]
    push_cast
    ring

/-- **The formal computation of Stacks 0FAG in degree two**: for the tensor product of two lists
of signed roots of ranks `r` and `s`,
`c₂ = r c₂' + s c₂ + C(r, 2) c₁'² + (r s - 1) c₁' c₁ + C(s, 2) c₁²`. -/
theorem rootSumTwo_rootTensor (l l' : List (ℤˣ × K)) :
    rootSumTwo (rootTensor l l') =
      (rootRank l : K) * rootSumTwo l' + (rootRank l' : K) * rootSumTwo l
        + ((Ring.choose (rootRank l) 2 : ℤ) : K) * rootSum l' ^ 2
        + ((rootRank l : K) * rootRank l' - 1) * (rootSum l' * rootSum l)
        + ((Ring.choose (rootRank l') 2 : ℤ) : K) * rootSum l ^ 2 := by
  induction l with
  | nil => simp [Ring.choose_zero_succ]
  | cons t l ih =>
    have h2 : ((2 * Ring.choose (rootRank l') 2 : ℤ) : K) =
        ((rootRank l' * (rootRank l' - 1) : ℤ) : K) :=
      congrArg (Int.cast) (two_mul_ringChoose_two (rootRank l'))
    push_cast at h2
    rw [rootTensor_cons, rootSumTwo_append, rootSumTwo_map_tensor, rootSum_map_tensor,
      rootSum_rootTensor, ih, rootSumTwo_cons, rootSum_cons, rootRank_cons,
      ringChoose_unit_add_two]
    rcases Int.units_eq_one_or t.1 with h | h <;>
      simp only [h, Units.val_one, Units.val_neg, if_true, if_false,
        show ((-1 : ℤ) = 1) = False by decide] <;> push_cast
    · linear_combination (-(t.2 * rootSum l)) * h2
    · linear_combination (t.2 * rootSum l) * h2

/-- **The formal computation of Stacks 0FAG for the power sums**: for the tensor product of two
lists of signed roots, `P_p = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁} P'_{p₂}`. -/
theorem rootPow_rootTensor (l l' : List (ℤˣ × K)) (p : ℕ) :
    rootPow (rootTensor l l') p = ∑ q ∈ antidiagonal p,
      (p.choose q.1 : K) * (rootPow l q.1 * rootPow l' q.2) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [rootTensor_cons, rootPow_append, ih]
    simp only [rootPow_cons]
    have hmap : rootPow (l'.map fun t' ↦ (t.1 * t'.1, t.2 + t'.2)) p =
        ∑ q ∈ antidiagonal p, (p.choose q.1 : K) *
          ((((t.1 : ℤ) : K) * t.2 ^ q.1) * rootPow l' q.2) := by
      clear ih
      induction l' with
      | nil => simp
      | cons t' l' ih' =>
        rw [List.map_cons, rootPow_cons, ih', (Commute.all t.2 t'.2).add_pow',
          Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [rootPow_cons, nsmul_eq_mul]
        push_cast
        ring
    rw [hmap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    ring

end Commutative

/-! ### Transport to a ring through the commutative subring generated by the roots -/

section Transport

variable {A : Type*} [Ring A]

/-- A list of signed roots with entries in a subring lifts to that subring. -/
theorem exists_rootMap_eq_of_mem (R : Subring A) :
    ∀ l : List (ℤˣ × A), (∀ t ∈ l, t.2 ∈ R) → ∃ lR : List (ℤˣ × R), rootMap R.subtype lR = l
  | [], _ => ⟨[], rfl⟩
  | t :: l, h => by
    obtain ⟨lR, hlR⟩ := exists_rootMap_eq_of_mem R l fun t' ht' ↦ h t' (List.mem_cons_of_mem _ ht')
    refine ⟨(t.1, ⟨t.2, h t List.mem_cons_self⟩) :: lR, ?_⟩
    show List.map _ (_ :: lR) = _
    rw [List.map_cons]
    exact congrArg₂ List.cons rfl hlR

variable {l l' : List (ℤˣ × A)} (hcomm : ∀ t ∈ l ++ l', ∀ t' ∈ l ++ l', Commute t.2 t'.2)

include hcomm in
/-- Pairwise commuting signed roots lift to a commutative ring mapping to `A`: the subring
generated by the roots. -/
private theorem exists_commRing_rootMap_eq_of_commute :
    ∃ (R : Type u_1) (_ : CommRing R) (f : R →+* A) (lR lR' : List (ℤˣ × R)),
      rootMap f lR = l ∧ rootMap f lR' = l' := by
  obtain ⟨lR, hl⟩ := exists_rootMap_eq_of_mem (Subring.closure {a | ∃ t ∈ l ++ l', t.2 = a}) l
    fun t ht ↦ Subring.subset_closure ⟨t, List.mem_append_left _ ht, rfl⟩
  obtain ⟨lR', hl'⟩ := exists_rootMap_eq_of_mem (Subring.closure {a | ∃ t ∈ l ++ l', t.2 = a}) l'
    fun t ht ↦ Subring.subset_closure ⟨t, List.mem_append_right _ ht, rfl⟩
  refine ⟨_, Subring.closureCommRingOfComm ?_, (Subring.closure _).subtype, lR, lR', hl, hl'⟩
  rintro a ⟨t, ht, rfl⟩ b ⟨t', ht', rfl⟩
  exact hcomm t ht t' ht'

include hcomm in
/-- **The degree-two computation of Stacks 0FAG for pairwise commuting signed roots in an
arbitrary ring**: it holds in the commutative subring the roots generate. -/
theorem rootSumTwo_rootTensor_of_commute :
    rootSumTwo (rootTensor l l') =
      (rootRank l : A) * rootSumTwo l' + (rootRank l' : A) * rootSumTwo l
        + ((Ring.choose (rootRank l) 2 : ℤ) : A) * rootSum l' ^ 2
        + ((rootRank l : A) * rootRank l' - 1) * (rootSum l' * rootSum l)
        + ((Ring.choose (rootRank l') 2 : ℤ) : A) * rootSum l ^ 2 := by
  obtain ⟨R, _, f, lR, lR', rfl, rfl⟩ := exists_commRing_rootMap_eq_of_commute hcomm
  have h := congrArg f (rootSumTwo_rootTensor lR lR')
  rw [rootTensor_rootMap, rootSumTwo_rootMap, rootSumTwo_rootMap, rootSumTwo_rootMap,
    rootSum_rootMap, rootSum_rootMap, rootRank_rootMap, rootRank_rootMap, h]
  simp

include hcomm in
/-- **The degree-one computation of Stacks 0FAG for pairwise commuting signed roots.** -/
theorem rootSum_rootTensor_of_commute :
    rootSum (rootTensor l l') = (rootRank l' : A) * rootSum l + (rootRank l : A) * rootSum l' := by
  obtain ⟨R, _, f, lR, lR', rfl, rfl⟩ := exists_commRing_rootMap_eq_of_commute hcomm
  have h := congrArg f (rootSum_rootTensor lR lR')
  rw [rootTensor_rootMap, rootSum_rootMap, rootSum_rootMap, rootSum_rootMap, rootRank_rootMap,
    rootRank_rootMap, h]
  simp

include hcomm in
/-- **The power-sum computation of Stacks 0FAG for pairwise commuting signed roots.** -/
theorem rootPow_rootTensor_of_commute (p : ℕ) :
    rootPow (rootTensor l l') p = ∑ q ∈ antidiagonal p,
      (p.choose q.1 : A) * (rootPow l q.1 * rootPow l' q.2) := by
  obtain ⟨R, _, f, lR, lR', rfl, rfl⟩ := exists_commRing_rootMap_eq_of_commute hcomm
  have h := congrArg f (rootPow_rootTensor lR lR' p)
  rw [rootTensor_rootMap, rootPow_rootMap, h, map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp [rootPow_rootMap]

end Transport

/-! ### Signed roots in the ring of total classes -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y : AlgebraicGeometry.Scheme.{u}} {sY : Y ⟶ C.S}
  [AlgebraicGeometry.LocallyOfFiniteType sY]

/-- A class homogeneous of degree one has degree-zero component zero, so `1 + x` is a unit. -/
theorem isUnit_one_add_of_isHomogeneous_one {x : TotalChowClass C sY} (hx : x.IsHomogeneous 1) :
    IsUnit (1 + x) :=
  isUnit_of_apply_zero (by rw [add_apply, hx 0 (by norm_num), add_zero])

/-- **The unit `1 + x`** for `x` homogeneous of degree one (and `1` for other `x`). -/
def oneAddUnit (x : TotalChowClass C sY) : (TotalChowClass C sY)ˣ := by
  classical exact if h : IsUnit (1 + x) then h.unit else 1

/-- For `x` homogeneous of degree one, the unit `oneAddUnit x` is `1 + x`. -/
theorem val_oneAddUnit {x : TotalChowClass C sY} (hx : x.IsHomogeneous 1) :
    (oneAddUnit x : TotalChowClass C sY) = 1 + x := by
  rw [oneAddUnit, dif_pos (isUnit_one_add_of_isHomogeneous_one hx)]
  rfl

/-- **The total Chern class `∏ (1 + x_a)^{ε_a}` of a list of signed roots**, as a unit, the
product taken in the order of the list. -/
def rootProd (l : List (ℤˣ × TotalChowClass C sY)) : (TotalChowClass C sY)ˣ :=
  (l.map fun t ↦ oneAddUnit t.2 ^ (t.1 : ℤ)).prod

/-- The total Chern class of the empty list of signed roots is `1`. -/
@[simp] theorem rootProd_nil : rootProd ([] : List (ℤˣ × TotalChowClass C sY)) = 1 := rfl

/-- The total Chern class of `(ε, x) :: l` is `(1 + x)^ε` times the total Chern class of `l`. -/
theorem rootProd_cons (t : ℤˣ × TotalChowClass C sY) (l : List (ℤˣ × TotalChowClass C sY)) :
    rootProd (t :: l) = oneAddUnit t.2 ^ (t.1 : ℤ) * rootProd l := by
  simp [rootProd]

/-- The total Chern class of a concatenation of lists of signed roots is the product of the total
Chern classes. -/
theorem rootProd_append (l l' : List (ℤˣ × TotalChowClass C sY)) :
    rootProd (l ++ l') = rootProd l * rootProd l' := by
  simp [rootProd]

/-- The components of degree `≤ 2` of a product of two classes of degree-zero component `1`:
`(ab)₁ = a₁ + b₁` and `(ab)₂ = a₂ + a₁ b₁ + b₂`. -/
theorem homComponent_mul_jets {a b : TotalChowClass C sY} (ha : homComponent 0 a = 1)
    (hb : homComponent 0 b = 1) :
    homComponent 0 (a * b) = 1 ∧
      homComponent 1 (a * b) = homComponent 1 a + homComponent 1 b ∧
      homComponent 2 (a * b) =
        homComponent 2 a + homComponent 1 a * homComponent 1 b + homComponent 2 b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [homComponent_mul]
    simp [ha, hb]
  · rw [homComponent_mul]
    simp [Finset.sum_range_succ, ha, hb]
  · rw [homComponent_mul]
    simp [Finset.sum_range_succ, ha, hb]

/-- The components of degree `≤ 2` of `(1 + x)^{±1}` for `x` homogeneous of degree one:
`1`, `± x` and `C(±1, 2) x²`. -/
theorem homComponent_oneAddUnit_zpow {x : TotalChowClass C sY} (hx : x.IsHomogeneous 1)
    (ε : ℤˣ) :
    homComponent 0 ((oneAddUnit x ^ (ε : ℤ) : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) = 1 ∧
      homComponent 1 ((oneAddUnit x ^ (ε : ℤ) : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) =
        ((ε : ℤ) : TotalChowClass C sY) * x ∧
      homComponent 2 ((oneAddUnit x ^ (ε : ℤ) : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) =
        if (ε : ℤ) = 1 then 0 else x * x := by
  have hu : ((oneAddUnit x : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) 0 =
      (1 : TotalChowClass C sY) 0 := by
    rw [val_oneAddUnit hx, add_apply, hx 0 (by norm_num), add_zero]
  have h1 := homComponent_one_add_of_isHomogeneous_one hx
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp [val_oneAddUnit hx, h1]
  · simp only [Units.val_neg, Units.val_one, zpow_neg, zpow_one,
      show ((-1 : ℤ) = 1) = False by decide, if_false]
    have h0 := homComponent_zero_of_apply_zero (inv_apply_zero_eq_one hu)
    have hinv1 := homComponent_inv_eq hu 1
    have hinv2 := homComponent_inv_eq hu 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, val_oneAddUnit hx, h1,
      homComponent_one, h0] at hinv1 hinv2
    refine ⟨h0, ?_, ?_⟩
    · rw [hinv1]
      simp
    · rw [hinv2, hinv1]
      simp

/-- **The components of degree `≤ 2` of `∏ (1 + x_a)^{ε_a}`** are `1`, `c₁ = ∑ ε_a x_a` and the
second Chern class `Stacks.Chow.rootSumTwo` of the signed roots. -/
theorem homComponent_rootProd (l : List (ℤˣ × TotalChowClass C sY))
    (hl : ∀ t ∈ l, t.2.IsHomogeneous 1) :
    homComponent 0 ((rootProd l : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) = 1 ∧
      homComponent 1 ((rootProd l : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) =
        rootSum l ∧
      homComponent 2 ((rootProd l : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) =
        rootSumTwo l := by
  induction l with
  | nil => simp [homComponent_one]
  | cons t l ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih fun t' ht' ↦ hl t' (List.mem_cons_of_mem _ ht')
    obtain ⟨h0, h1, h2⟩ := homComponent_oneAddUnit_zpow (hl t List.mem_cons_self) t.1
    obtain ⟨m0, m1, m2⟩ := homComponent_mul_jets h0 ih0
    rw [rootProd_cons, Units.val_mul]
    refine ⟨m0, ?_, ?_⟩
    · rw [m1, h1, ih1, rootSum_cons]
    · rw [m2, h2, h1, ih1, ih2, rootSumTwo_cons]

/-- The components of `1 + x` commute with every class commuting with `x`. -/
theorem commute_homComponent_one_add {x y : TotalChowClass C sY} (hx : x.IsHomogeneous 1)
    (hxy : Commute x y) (i : ℕ) : Commute (homComponent i (1 + x)) y := by
  rw [homComponent_one_add_of_isHomogeneous_one hx]
  split_ifs
  · exact Commute.one_left y
  · exact hxy
  · exact Commute.zero_left y

/-- For `x` homogeneous of degree one, the degree-zero component of `1 + x` is `1`. -/
theorem homComponent_zero_one_add {x : TotalChowClass C sY} (hx : x.IsHomogeneous 1) :
    homComponent 0 (1 + x) = 1 := by
  rw [homComponent_one_add_of_isHomogeneous_one hx, if_pos rfl]

/-- The components of `(1 + x)^{±1}` commute with every class commuting with `x`. -/
theorem commute_homComponent_oneAddUnit_zpow {x y : TotalChowClass C sY}
    (hx : x.IsHomogeneous 1) (hxy : Commute x y) (ε : ℤˣ) (i : ℕ) :
    Commute (homComponent i
      ((oneAddUnit x ^ (ε : ℤ) : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)) y := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rw [Units.val_one, zpow_one, val_oneAddUnit hx]
    exact commute_homComponent_one_add hx hxy i
  · rw [Units.val_neg, Units.val_one, zpow_neg, zpow_one]
    refine commute_homComponent_of_mul_eq_one (c := (oneAddUnit x : TotalChowClass C sY))
      (by rw [val_oneAddUnit hx]; exact homComponent_zero_one_add hx) (Units.mul_inv _)
      (fun k ↦ ?_) i
    rw [val_oneAddUnit hx]
    exact commute_homComponent_one_add hx hxy k

/-- The components of a product commute with a class commuting with the components of the
factors. -/
theorem commute_homComponent_mul_left {a b y : TotalChowClass C sY}
    (ha : ∀ i, Commute (homComponent i a) y) (hb : ∀ i, Commute (homComponent i b) y)
    (i : ℕ) : Commute (homComponent i (a * b)) y := by
  rw [homComponent_mul]
  exact Commute.sum_left _ _ _ fun j _ ↦ (ha _).mul_left (hb _)

/-- The components of `∏ (1 + x_a)^{ε_a}` commute with every class commuting with the roots. -/
theorem commute_homComponent_rootProd {y : TotalChowClass C sY}
    (l : List (ℤˣ × TotalChowClass C sY)) (hl : ∀ t ∈ l, t.2.IsHomogeneous 1)
    (hy : ∀ t ∈ l, Commute t.2 y) (i : ℕ) :
    Commute (homComponent i ((rootProd l : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)) y := by
  induction l generalizing i with
  | nil =>
    rw [rootProd_nil, Units.val_one, homComponent_one]
    split_ifs
    · exact Commute.one_left y
    · exact Commute.zero_left y
  | cons t l ih =>
    rw [rootProd_cons, Units.val_mul]
    exact commute_homComponent_mul_left
      (commute_homComponent_oneAddUnit_zpow (hl t List.mem_cons_self) (hy t List.mem_cons_self) _)
      (ih (fun t' ht' ↦ hl t' (List.mem_cons_of_mem _ ht'))
        (fun t' ht' ↦ hy t' (List.mem_cons_of_mem _ ht'))) i

/-- **The power sums of `(1 + x)^{±1}`** are `± x^p`, for `p ≥ 1`. -/
theorem newtonComponents_oneAddUnit_zpow {x : TotalChowClass C sY} (hx : x.IsHomogeneous 1)
    (ε : ℤˣ) (p : ℕ) (hp : 0 < p) :
    newtonComponents ((oneAddUnit x ^ (ε : ℤ) : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) p =
      ((ε : ℤ) : TotalChowClass C sY) * x ^ p := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rw [Units.val_one, zpow_one, val_oneAddUnit hx,
      newtonComponents_one_add_of_isHomogeneous_one hx p hp, Int.cast_one, one_mul]
  · rw [Units.val_neg, Units.val_one, zpow_neg, zpow_one,
      newtonComponents_of_mul_eq_one (c := (oneAddUnit x : TotalChowClass C sY))
        (by rw [val_oneAddUnit hx]; exact homComponent_zero_one_add hx) (Units.mul_inv _)
        (fun i j ↦ by
          rw [val_oneAddUnit hx]
          exact commute_homComponent_one_add hx
            (commute_homComponent_one_add hx (Commute.refl x) j).symm i) p,
      val_oneAddUnit hx, newtonComponents_one_add_of_isHomogeneous_one hx p hp]
    simp

/-- **The power sums of `∏ (1 + x_a)^{ε_a}`** are `∑ ε_a x_a^p`, for `p ≥ 1` and pairwise commuting
roots. -/
theorem newtonComponents_rootProd (l : List (ℤˣ × TotalChowClass C sY))
    (hl : ∀ t ∈ l, t.2.IsHomogeneous 1) (hcomm : ∀ t ∈ l, ∀ t' ∈ l, Commute t.2 t'.2)
    (p : ℕ) (hp : 0 < p) :
    newtonComponents ((rootProd l : (TotalChowClass C sY)ˣ) : TotalChowClass C sY) p =
      rootPow l p := by
  induction l with
  | nil => rw [rootProd_nil, Units.val_one, newtonComponents_one, rootPow_nil]
  | cons t l ih =>
    have hl' : ∀ t' ∈ l, t'.2.IsHomogeneous 1 := fun t' ht' ↦ hl t' (List.mem_cons_of_mem _ ht')
    have ht := hl t List.mem_cons_self
    rw [rootProd_cons, Units.val_mul, newtonComponents_mul
      (homComponent_oneAddUnit_zpow ht t.1).1 (homComponent_rootProd l hl').1
      (fun i j ↦ (commute_homComponent_rootProd l hl' (fun t' ht' ↦
        (commute_homComponent_oneAddUnit_zpow ht
          (hcomm t List.mem_cons_self t' (List.mem_cons_of_mem _ ht')) t.1 i).symm) j).symm),
      newtonComponents_oneAddUnit_zpow ht t.1 p hp,
      ih hl' (fun a ha b hb ↦ hcomm a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)),
      rootPow_cons]

end TotalChowClass

end Stacks.Chow

end
