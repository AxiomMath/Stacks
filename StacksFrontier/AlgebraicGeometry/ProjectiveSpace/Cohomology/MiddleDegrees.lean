module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TopDegree
public import StacksFrontier.RingTheory.Cech.Substrate

/-!
# Acyclicity of the Čech complex of `𝒪(d)` on projective space

Projective `n`-space over a ring `R` is covered by the `n + 1` standard opens `D₊(T₀), …,
D₊(Tₙ)`, and the degree-`q` term of the ordered Čech complex of that cover for `𝒪(d)` is indexed
by the `(q + 1)`-element sets `S ⊆ {0, …, n}`, its `S`-component being the degree-`d` part of
`R[T₀, …, Tₙ][1/∏_{i ∈ S} Tᵢ]` — the module
`Stacks.ProjectiveSpace.Cohomology.twistChart R n d S` of the monomial model. This file writes
that complex down for every `n` and every `d`, as the single module `LaurentCochain R n` of
Laurent coefficient families indexed by *all* index sets together with the submodules
`laurentCechCochains R n d q` cutting out one degree, and proves it acyclic in the whole range
where `Hᵠ(ℙⁿ_R, 𝒪(d))` vanishes.

The engine is a contracting homotopy, exactly the one in the Stacks proof of Tag 01XT. That
proof splits the complex into its `ℤ^{n+1}`-weight summands, and for a weight `e` with
`NEG(e) = {i | eᵢ < 0}` neither empty nor everything picks an index `i_fix ∉ NEG(e)` and
contracts the weight-`e` summand by adjoining `i_fix` to the index set. Here the weight splitting
is not performed: the homotopy `laurentCechHomotopy` adjoins to the index set, monomial by
monomial, the *least* index at which the exponent vector is nonnegative — the predicate
`IsFirstNonneg`, selected with `Finsupp.filter`. That is a canonical choice of `i_fix`, uniform
in the weight, so a single linear map on `LaurentCochain R n` carries all the weight-wise
homotopies at once and `laurentCechDiff_laurentCechHomotopy_add` is the identity `dh + hd = 1`
with one hypothesis: that no monomial occurring in the cochain has *all* exponents negative.

Every vanishing range of `Hᵠ(ℙⁿ_R, 𝒪(d))` is that hypothesis in a different guise.

* `0 < q < n`: a degree-`q` cochain lives on index sets of size `q + 1 ≤ n`, so some variable is
  not inverted and its exponent is nonnegative (`exists_nonneg_of_mem_laurentCechCochains`).
* `-n ≤ d`, any `q > 0`, the top degree included: there is no degree-`d` Laurent monomial in
  `n + 1` variables with every exponent negative at all
  (`exists_nonneg_of_mem_laurentCechCochains_of_le`, from
  `negativeLaurentMonomials_eq_empty_iff`).
* `q > n`: there is no cochain, the index sets being too large
  (`laurentCechCochains_eq_bot`).
* `q = 0` and `d < 0`: here the homotopy is unavailable — the identity `dh + hd = 1` needs a
  cochain of positive degree — and the vanishing is instead the cocycle condition
  (`apply_singleton_eq_of_laurentCechDiff_eq_zero`) together with
  `twistChart_eq_bot_of_neg`.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.IsFirstNonneg` — `i` is the least index at which an
  exponent vector is nonnegative.
* `Stacks.ProjectiveSpace.Cohomology.LaurentCochain` — Čech cochains of the standard cover with
  Laurent coefficients, all degrees at once.
* `Stacks.ProjectiveSpace.Cohomology.laurentCechDiff` — the Čech differential
  `(d c)_S = ∑_{i ∈ S} (-1)^{pos of i in S} c_{S ∖ {i}}`.
* `Stacks.ProjectiveSpace.Cohomology.laurentCechHomotopy` — the contracting homotopy.
* `Stacks.ProjectiveSpace.Cohomology.laurentCechCochains` — the degree-`q` Čech cochains for
  `𝒪(d)`, as a submodule.
* `Stacks.ProjectiveSpace.Cohomology.laurentCechDiffRestrict` — the differential as a map of
  those submodules.
* `Stacks.ProjectiveSpace.Cohomology.laurentDiagonalCochain` — a polynomial section read as a
  degree-zero Čech cochain, the same section on every standard open.
* `Stacks.ProjectiveSpace.Cohomology.laurentTopCechDiff` — the differential out of degree
  `n - 1`, read as a map into the sections on the total intersection.

## Main results

* `sum_filter_isFirstNonneg` — a Laurent coefficient family with no all-negative monomial is the
  sum of its parts of given least nonnegative exponent. This is the weight splitting, in the one
  form the homotopy needs.
* `cechSign_mul_cechSign_erase` — the sign cancellation between deleting `i` then adjoining `j`
  and adjoining `j` then deleting `i`, which is why the homotopy works.
* `laurentCechDiff_comp_self` — the differential squares to zero.
* `laurentCechDiff_laurentCechHomotopy_add` — **`dh + hd = 1`** away from the all-negative
  monomials.
* `exists_laurentCechDiff_eq` — **`Hᵠ(ℙⁿ_R, 𝒪(d)) = 0` for `0 < q < n`**, every `d`; and
  `range_laurentCechDiffRestrict` as an equality of cocycles and coboundaries.
* `exists_laurentCechDiff_eq_of_le` and `range_laurentCechDiffRestrict_of_le` — **`Hᵠ = 0` for
  every `q > 0` when `-n ≤ d`**, the top degree included, hence for every `d ≥ 0`.
* `laurentCechCochains_eq_bot` — **`Hᵠ = 0` for `q > n`.**
* `ker_laurentCechDiffRestrict_zero_eq_bot` — **`H⁰ = 0` for `d < 0` and `0 < n`.**

The two degrees that do carry cohomology are identified in the same complex, so that the whole
of Tag 01XT is a statement about it:

* `laurentCechCohomologyZeroEquiv` — **`H⁰` is the module of polynomial sections**, for `0 < n`;
  with `twistChartEmptyLinearEquiv` that is the degree-`d` homogeneous polynomials for `0 ≤ d`.
* `range_laurentTopCechDiff` — **the top-degree differential has the same image as
  `topCechDiff`**, so `topCechCohomologyEquiv` computes `Hⁿ` of this complex: the
  free module on the degree-`d` Laurent monomials with every exponent negative.

## Implementation notes

The cochains are a *plain function type* on `Finset (Fin (n + 1))`, not a dependent product over
the `(q + 1)`-element sets of the submodules `twistChart R n d S`, and the degree and the
section conditions are hypotheses (membership in `laurentCechCochains`) rather than part of the
type. That is what keeps the file free of transport: the Čech and homotopy formulas rewrite the
index set — `insert j (S.erase i) = (insert j S).erase i` — under the cochain, and with a
non-dependent index that is `congrArg`, whereas in the dependent product each such step is an
`Eq.rec` between two spellings of one module. Both maps are therefore defined on all of
`LaurentCochain R n` and shown to respect the submodules separately
(`laurentCechDiff_mem_laurentCechCochains`, `laurentCechHomotopy_mem_laurentCechCochains`).

Three small lemmas are restatements rather than new facts, and the reason is spelling in each
case: `filter_sum` is `map_sum` for `Finsupp.filterAddHom`, put at the `Finsupp.filter` spelling
`rw` can match; `sum_sum_erase_eq_zero` is `Cech.double_sum_antisymm_zero` in the `erase` form
the Čech differential produces instead of the complement form, and without its `Fintype`
hypothesis; and `cechSign_smul_cechSign_smul` is `Tag0G6J.cechSign_mul_self` in the
scalar-action form, restated because that lemma's file imports normed-ring theory.

`Tag0G6J.cechComplex_nullHomotopic` is the same contraction for the extended alternating Čech
complex of a family `f` with some `f i` a unit, and it is *not* used here. Routing the weight-`e`
summand through it needs, besides that homotopy, a direct-sum decomposition of this complex over
`ℤ^{n+1}`, an order-reindexing of the sets `S ⊇ NEG(e)` by `S ∖ NEG(e)` carrying a sign
rescaling (the Čech sign of inserting `j` counts the elements of `NEG(e)` below `j` as well), a
degree shift by `#NEG(e)`, and the identification of `LocalizedModule (Submonoid.powers 1) R`
with `R`. The homotopy is the cheapest of those five, and writing it directly in the monomial
model replaces the other four by `Finsupp.filter`.

No `@[stacks]` attribute is attached. Tag 01XT needs, besides the monomial computation here and
in `Stacks.ProjectiveSpace.Cohomology.TopDegree`, the identification of the Čech complex of the
standard cover with these charts for general `n` — available at the pin only for `n = 1`, in
`StacksFrontier.AlgebraicGeometry.ProjectiveSpace.CechComparison.OverlapRestriction` — and the
comparison of Čech with derived cohomology, Tag 01XD.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0G6J](https://stacks.math.columbia.edu/tag/0G6J)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

open Finsupp

universe u

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {n : ℕ} {d : ℤ} {q : ℕ}

section FirstNonneg

/-- `IsFirstNonneg e i` says that `i` is the least index at which the exponent vector `e` is
nonnegative. For a Laurent monomial of `ℙⁿ` this is the first variable along which it is
regular. -/
def IsFirstNonneg (e : Fin (n + 1) → ℤ) (i : Fin (n + 1)) : Prop :=
  0 ≤ e i ∧ ∀ j < i, e j < 0

/-- Being the least index with a nonnegative exponent is decidable, so the parts of a Laurent
coefficient family of given least nonnegative exponent can be cut out with `Finsupp.filter`. -/
instance (e : Fin (n + 1) → ℤ) : DecidablePred (IsFirstNonneg e) := fun i =>
  decidable_of_iff (0 ≤ e i ∧ ∀ j < i, e j < 0) Iff.rfl

/-- The defining property of `IsFirstNonneg`. -/
theorem isFirstNonneg_iff {e : Fin (n + 1) → ℤ} {i : Fin (n + 1)} :
    IsFirstNonneg e i ↔ 0 ≤ e i ∧ ∀ j < i, e j < 0 := Iff.rfl

/-- An exponent vector with a nonnegative entry has a least one. -/
theorem exists_isFirstNonneg {e : Fin (n + 1) → ℤ} (he : ∃ i, 0 ≤ e i) :
    ∃ i, IsFirstNonneg e i := by
  obtain ⟨i, hi⟩ := he
  obtain ⟨m, hm, hmin⟩ := wellFounded_lt.has_min {k : Fin (n + 1) | 0 ≤ e k} ⟨i, hi⟩
  exact ⟨m, hm, fun j hj => not_le.1 fun h => hmin j h hj⟩

/-- There is at most one least nonnegative entry. -/
theorem isFirstNonneg_unique {e : Fin (n + 1) → ℤ} {i j : Fin (n + 1)}
    (hi : IsFirstNonneg e i) (hj : IsFirstNonneg e j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hi.1 (not_le.2 (hj.2 i h))
  · exact h
  · exact absurd hj.1 (not_le.2 (hi.2 j h))

/-- **Splitting a Laurent coefficient family by the least nonnegative exponent.** If every
monomial occurring in `x` has some nonnegative exponent, then `x` is the sum over `i` of the part
of `x` whose least nonnegative exponent is `i`. -/
theorem sum_filter_isFirstNonneg (x : (Fin (n + 1) → ℤ) →₀ R)
    (hx : ∀ e ∈ x.support, ∃ i, 0 ≤ e i) :
    ∑ i : Fin (n + 1), Finsupp.filter (fun e => IsFirstNonneg e i) x = x := by
  refine Finsupp.ext fun e => ?_
  rw [Finsupp.finsetSum_apply]
  by_cases hx0 : x e = 0
  · refine (Finset.sum_eq_zero fun i _ => ?_).trans hx0.symm
    by_cases hi : IsFirstNonneg e i
    · rw [Finsupp.filter_apply_pos (fun e' => IsFirstNonneg e' i) x hi, hx0]
    · rw [Finsupp.filter_apply_neg (fun e' => IsFirstNonneg e' i) x hi]
  · obtain ⟨i, hi⟩ := exists_isFirstNonneg (hx e (Finsupp.mem_support_iff.2 hx0))
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun j _ hj =>
        Finsupp.filter_apply_neg (fun e' => IsFirstNonneg e' j) x
          fun hcon => hj (isFirstNonneg_unique hcon hi)),
      Finsupp.filter_apply_pos (fun e' => IsFirstNonneg e' i) x hi]

/-- Filtering commutes with finite sums. This is `map_sum` for `Finsupp.filterAddHom`, restated
at the `Finsupp.filter` spelling so that `rw` can see it. -/
theorem filter_sum {ι : Type*} (p : (Fin (n + 1) → ℤ) → Prop) [DecidablePred p]
    (s : Finset ι) (f : ι → ((Fin (n + 1) → ℤ) →₀ R)) :
    Finsupp.filter p (∑ i ∈ s, f i) = ∑ i ∈ s, Finsupp.filter p (f i) :=
  map_sum (Finsupp.filterAddHom p) f s

end FirstNonneg

section Signs

/-- Two sign exponents of opposite parity give opposite signs. -/
theorem neg_one_pow_mul_eq_neg {a b c e : ℕ} (h : a + b + 1 = c + e ∨ c + e + 1 = a + b) :
    ((-1 : ℤ) ^ a * (-1) ^ b) = -((-1) ^ c * (-1) ^ e) := by
  rw [← pow_add, ← pow_add]
  rcases h with h | h
  · rw [← h, pow_succ]; ring
  · rw [← h, pow_succ]; ring

/-- **Applying the Čech sign twice is the identity.** `Tag0G6J.cechSign_mul_self` is the same
fact for the product of the two signs; it is restated here in the scalar-action form the Čech
homotopy uses, and because its file imports the normed-ring theory this one has no use for. -/
theorem cechSign_smul_cechSign_smul {M : Type*} [AddCommGroup M] (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (x : M) : Cech.cechSign S i • Cech.cechSign S i • x = x := by
  rw [smul_smul, Cech.cechSign, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul]

/-- **Sign cancellation between the two ways of reaching `insert j (S.erase i)`**, for `i ∈ S`
and `j ∉ S`: deleting `i` from `S` and then adjoining `j`, against adjoining `j` to `S` and then
deleting `i`. This is what makes the contracting homotopy of the Čech complex work. -/
theorem cechSign_mul_cechSign_erase {S : Finset (Fin (n + 1))} {i j : Fin (n + 1)}
    (hi : i ∈ S) (hj : j ∉ S) :
    Cech.cechSign S i * Cech.cechSign (S.erase i) j
      = -(Cech.cechSign S j * Cech.cechSign (insert j S) i) := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  rw [Cech.cechSign, Cech.cechSign, Cech.cechSign, Cech.cechSign, Finset.filter_erase,
    Finset.filter_insert]
  refine neg_one_pow_mul_eq_neg ?_
  rcases lt_or_gt_of_ne hij with h | h
  · have hmem : i ∈ Finset.filter (fun x => x < j) S := Finset.mem_filter.2 ⟨hi, h⟩
    have hpos : 0 < (Finset.filter (fun x => x < j) S).card := Finset.card_pos.2 ⟨i, hmem⟩
    rw [Finset.card_erase_of_mem hmem, ite_eq_right (show ¬ j < i from not_lt.2 h.le)]
    omega
  · have hnot : i ∉ Finset.filter (fun x => x < j) S := fun hcon =>
      absurd (Finset.mem_filter.1 hcon).2 (not_lt.2 h.le)
    have hnot2 : j ∉ Finset.filter (fun x => x < i) S := fun hcon =>
      hj (Finset.mem_filter.1 hcon).1
    rw [Finset.erase_eq_of_notMem hnot, ite_eq_left h, Finset.card_insert_of_notMem hnot2]
    omega

/-- **Sign antisymmetry of the double Čech differential**: the two orders of deleting `i` and `j`
from `S` carry opposite signs. -/
theorem cechSign_mul_cechSign_erase_swap {S : Finset (Fin (n + 1))} {i j : Fin (n + 1)}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    Cech.cechSign S i * Cech.cechSign (S.erase i) j
      = -(Cech.cechSign S j * Cech.cechSign (S.erase j) i) := by
  rw [Cech.cechSign, Cech.cechSign, Cech.cechSign, Cech.cechSign, Finset.filter_erase,
    Finset.filter_erase]
  refine neg_one_pow_mul_eq_neg ?_
  rcases lt_or_gt_of_ne hij with h | h
  · have hmem : i ∈ Finset.filter (fun x => x < j) S := Finset.mem_filter.2 ⟨hi, h⟩
    have hpos : 0 < (Finset.filter (fun x => x < j) S).card := Finset.card_pos.2 ⟨i, hmem⟩
    have hnot : j ∉ Finset.filter (fun x => x < i) S := fun hcon =>
      absurd (Finset.mem_filter.1 hcon).2 (not_lt.2 h.le)
    rw [Finset.card_erase_of_mem hmem, Finset.erase_eq_of_notMem hnot]
    omega
  · have hmem : j ∈ Finset.filter (fun x => x < i) S := Finset.mem_filter.2 ⟨hj, h⟩
    have hpos : 0 < (Finset.filter (fun x => x < i) S).card := Finset.card_pos.2 ⟨j, hmem⟩
    have hnot : i ∉ Finset.filter (fun x => x < j) S := fun hcon =>
      absurd (Finset.mem_filter.1 hcon).2 (not_lt.2 h.le)
    rw [Finset.card_erase_of_mem hmem, Finset.erase_eq_of_notMem hnot]
    omega

/-- A double sum of an antisymmetric family over the ordered pairs of distinct elements of a
finite set vanishes. `Cech.double_sum_antisymm_zero` is the same statement for the pairs *outside*
a given set, over a `Fintype`; this is the `erase` form the Čech differential produces, and it
needs no `Fintype`. -/
theorem sum_sum_erase_eq_zero {α : Type*} [DecidableEq α] {M : Type*} [AddCommGroup M]
    (S : Finset α) (g : α → α → M)
    (hg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → g i j = -g j i) :
    ∑ i ∈ S, ∑ j ∈ S.erase i, g i j = 0 := by
  have hconv : ∑ i ∈ S, ∑ j ∈ S.erase i, g i j = ∑ p ∈ S.offDiag, g p.1 p.2 := by
    rw [Finset.sum_sigma']
    apply Finset.sum_nbij' (fun p => (p.1, p.2)) (fun p => ⟨p.1, p.2⟩)
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_sigma, Finset.mem_erase] at hab
      simp [Finset.mem_offDiag, hab.1, hab.2.2, Ne.symm hab.2.1]
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_offDiag] at hab
      simp [Finset.mem_sigma, Finset.mem_erase, hab.1, hab.2.1, Ne.symm hab.2.2]
    · rintro ⟨a, b⟩ _; rfl
    · rintro ⟨a, b⟩ _; rfl
    · rintro ⟨a, b⟩ _; rfl
  rw [hconv]
  apply Finset.sum_involution (fun p _ => (p.2, p.1))
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_offDiag] at hab
    rw [hg a hab.1 b hab.2.1 hab.2.2]; simp
  · rintro ⟨a, b⟩ hab hfne
    simp only [Finset.mem_offDiag] at hab
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro hba; exact absurd hba.symm hab.2.2
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_offDiag] at hab ⊢
    exact ⟨hab.2.1, hab.1, Ne.symm hab.2.2⟩
  · rintro ⟨a, b⟩ _; rfl

end Signs

section Complex

/-- Čech cochains of the standard cover of `ℙⁿ_R` with Laurent coefficients, all degrees at once:
one Laurent coefficient family for each set of indices, the degree-`q` part being the families
concentrated on the `(q + 1)`-element sets. -/
abbrev LaurentCochain (R : Type u) [CommRing R] (n : ℕ) : Type u :=
  Finset (Fin (n + 1)) → ((Fin (n + 1) → ℤ) →₀ R)

/-- **The Čech differential of the standard cover of `ℙⁿ_R` in the monomial model**:
`(d c)_S = ∑_{i ∈ S} (-1)^{pos of i in S} c_{S ∖ {i}}`. It raises the cardinality of the index
set, hence the Čech degree, by one. -/
def laurentCechDiff (R : Type u) [CommRing R] (n : ℕ) :
    LaurentCochain R n →ₗ[R] LaurentCochain R n where
  toFun c S := ∑ i ∈ S, Cech.cechSign S i • c (S.erase i)
  map_add' c₁ c₂ := funext fun S => by
    simp only [Pi.add_apply, smul_add]
    exact Finset.sum_add_distrib
  map_smul' r c := funext fun S => by
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ r _

/-- The Čech differential on the index set `S`, as a signed sum over the faces of `S`. -/
@[simp]
theorem laurentCechDiff_apply (c : LaurentCochain R n) (S : Finset (Fin (n + 1))) :
    laurentCechDiff R n c S = ∑ i ∈ S, Cech.cechSign S i • c (S.erase i) := rfl

/-- **The Čech differential squares to zero.** -/
theorem laurentCechDiff_comp_self :
    (laurentCechDiff R n).comp (laurentCechDiff R n) = 0 := by
  refine LinearMap.ext fun c => funext fun S => ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply, laurentCechDiff_apply,
    Finset.sum_congr rfl fun i (hi : i ∈ S) => by
      rw [laurentCechDiff_apply, Finset.smul_sum,
        Finset.sum_congr rfl fun j (hj : j ∈ S.erase i) => smul_smul _ _ _]]
  refine sum_sum_erase_eq_zero S _ fun i hi j hj hij => ?_
  rw [cechSign_mul_cechSign_erase_swap hi hj hij, neg_smul, Finset.erase_right_comm]

/-- **The contracting homotopy of the Čech complex of the standard cover of `ℙⁿ_R`.** On the
monomial of weight `e` it adjoins to the index set the least index `i` at which `e` is
nonnegative, with the Čech sign; the Stacks proof of Tag 01XT chooses such an index once per
weight, and `IsFirstNonneg` is the canonical choice. -/
def laurentCechHomotopy (R : Type u) [CommRing R] (n : ℕ) :
    LaurentCochain R n →ₗ[R] LaurentCochain R n where
  toFun c T := ∑ i ∈ Tᶜ, Cech.cechSign T i •
    Finsupp.filter (fun e => IsFirstNonneg e i) (c (insert i T))
  map_add' c₁ c₂ := funext fun T => by
    simp only [Pi.add_apply, Finsupp.filter_add, smul_add]
    exact Finset.sum_add_distrib
  map_smul' r c := funext fun T => by
    simp only [Pi.smul_apply, Finsupp.filter_smul, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ r _

/-- The contracting homotopy on the index set `T`: for each index `i` outside `T`, the part of
`c` at `insert i T` whose least nonnegative exponent is `i`, with the Čech sign. -/
@[simp]
theorem laurentCechHomotopy_apply (c : LaurentCochain R n) (T : Finset (Fin (n + 1))) :
    laurentCechHomotopy R n c T = ∑ i ∈ Tᶜ, Cech.cechSign T i •
      Finsupp.filter (fun e => IsFirstNonneg e i) (c (insert i T)) := rfl

/-- The part of `d ∘ h` at the index set `S` that does not come from re-adjoining a deleted
index. -/
theorem laurentCechDiff_laurentCechHomotopy_apply (c : LaurentCochain R n)
    (S : Finset (Fin (n + 1))) :
    laurentCechDiff R n (laurentCechHomotopy R n c) S
      = (∑ i ∈ S, Finsupp.filter (fun e => IsFirstNonneg e i) (c S))
        + ∑ i ∈ S, ∑ j ∈ Sᶜ, (Cech.cechSign S i * Cech.cechSign (S.erase i) j) •
            Finsupp.filter (fun e => IsFirstNonneg e j) (c (insert j (S.erase i))) := by
  have key : ∀ i ∈ S, Cech.cechSign S i • laurentCechHomotopy R n c (S.erase i)
      = Finsupp.filter (fun e => IsFirstNonneg e i) (c S)
        + ∑ j ∈ Sᶜ, (Cech.cechSign S i * Cech.cechSign (S.erase i) j) •
            Finsupp.filter (fun e => IsFirstNonneg e j) (c (insert j (S.erase i))) := by
    intro i hi
    have hiC : i ∉ Sᶜ := fun hcon => (Finset.mem_compl.1 hcon) hi
    rw [laurentCechHomotopy_apply, Finset.compl_erase, Finset.smul_sum,
      Finset.sum_insert hiC, Cech.cechSign_erase, cechSign_smul_cechSign_smul,
      Finset.insert_erase hi]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => smul_smul _ _ _)
  rw [laurentCechDiff_apply, Finset.sum_congr rfl key, Finset.sum_add_distrib]

/-- The part of `h ∘ d` at the index set `S` that does not come from deleting the adjoined
index. -/
theorem laurentCechHomotopy_laurentCechDiff_apply (c : LaurentCochain R n)
    (S : Finset (Fin (n + 1))) :
    laurentCechHomotopy R n (laurentCechDiff R n c) S
      = (∑ j ∈ Sᶜ, Finsupp.filter (fun e => IsFirstNonneg e j) (c S))
        + ∑ j ∈ Sᶜ, ∑ i ∈ S, (Cech.cechSign S j * Cech.cechSign (insert j S) i) •
            Finsupp.filter (fun e => IsFirstNonneg e j) (c (insert j (S.erase i))) := by
  have key : ∀ j ∈ Sᶜ, Cech.cechSign S j •
        Finsupp.filter (fun e => IsFirstNonneg e j) (laurentCechDiff R n c (insert j S))
      = Finsupp.filter (fun e => IsFirstNonneg e j) (c S)
        + ∑ i ∈ S, (Cech.cechSign S j * Cech.cechSign (insert j S) i) •
            Finsupp.filter (fun e => IsFirstNonneg e j) (c (insert j (S.erase i))) := by
    intro j hj
    have hjS : j ∉ S := Finset.mem_compl.1 hj
    rw [laurentCechDiff_apply, filter_sum, Finset.smul_sum, Finset.sum_insert hjS]
    refine congrArg₂ _ ?_ (Finset.sum_congr rfl fun i hi => ?_)
    · rw [Finsupp.filter_smul, Cech.cechSign_insert, cechSign_smul_cechSign_smul,
        Finset.erase_insert hjS]
    · have hne : j ≠ i := by rintro rfl; exact hjS hi
      rw [Finsupp.filter_smul, smul_smul, Finset.erase_insert_of_ne hne]
  rw [laurentCechHomotopy_apply, Finset.sum_congr rfl key, Finset.sum_add_distrib]

/-- **`d h + h d = 1`: the Čech complex of the standard cover of `ℙⁿ_R` is contractible in the
monomial model, away from the all-negative monomials.** The hypothesis is that every monomial
occurring in `c` has a nonnegative exponent, which for a Čech cochain of degree `q` holds as soon
as `q + 1 ≤ n`. -/
theorem laurentCechDiff_laurentCechHomotopy_add (c : LaurentCochain R n)
    (hc : ∀ (S : Finset (Fin (n + 1))) (e : Fin (n + 1) → ℤ), e ∈ (c S).support → ∃ i, 0 ≤ e i) :
    laurentCechDiff R n (laurentCechHomotopy R n c)
      + laurentCechHomotopy R n (laurentCechDiff R n c) = c := by
  refine funext fun S => ?_
  have hcross : (∑ i ∈ S, ∑ j ∈ Sᶜ, (Cech.cechSign S i * Cech.cechSign (S.erase i) j) •
        Finsupp.filter (fun e => IsFirstNonneg e j) (c (insert j (S.erase i))))
      + ∑ j ∈ Sᶜ, ∑ i ∈ S, (Cech.cechSign S j * Cech.cechSign (insert j S) i) •
          Finsupp.filter (fun e => IsFirstNonneg e j) (c (insert j (S.erase i))) = 0 := by
    rw [Finset.sum_comm (s := Sᶜ) (t := S), ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [← add_smul, cechSign_mul_cechSign_erase hi (Finset.mem_compl.1 hj), neg_add_cancel,
      zero_smul]
  rw [Pi.add_apply, laurentCechDiff_laurentCechHomotopy_apply,
    laurentCechHomotopy_laurentCechDiff_apply, add_add_add_comm, hcross, add_zero,
    Finset.sum_add_sum_compl]
  exact sum_filter_isFirstNonneg (c S) (hc S)

end Complex

section Cochains

/-- **The degree-`q` ordered Čech cochains of the standard cover of `ℙⁿ_R` for `𝒪(d)`, in the
monomial model**: the Laurent coefficient families concentrated on the `(q + 1)`-element index
sets `S` whose value at `S` is a degree-`d` section over `D₊(∏_{i ∈ S} Tᵢ)`, i.e. lies in
`twistChart R n d S`. -/
def laurentCechCochains (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ) :
    Submodule R (LaurentCochain R n) where
  carrier := {c | (∀ S : Finset (Fin (n + 1)), c S ∈ twistChart R n d (S : Set (Fin (n + 1)))) ∧
    ∀ S : Finset (Fin (n + 1)), S.card ≠ q + 1 → c S = 0}
  add_mem' h₁ h₂ := ⟨fun S => add_mem (h₁.1 S) (h₂.1 S), fun S hS => by
    rw [Pi.add_apply, h₁.2 S hS, h₂.2 S hS, add_zero]⟩
  zero_mem' := ⟨fun S => zero_mem _, fun _ _ => rfl⟩
  smul_mem' r c h := ⟨fun S => Submodule.smul_mem _ r (h.1 S), fun S hS => by
    rw [Pi.smul_apply, h.2 S hS, smul_zero]⟩

/-- Membership in the degree-`q` Čech cochains, unfolded. -/
@[simp]
theorem mem_laurentCechCochains {c : LaurentCochain R n} :
    c ∈ laurentCechCochains R n d q ↔
      (∀ S : Finset (Fin (n + 1)), c S ∈ twistChart R n d (S : Set (Fin (n + 1)))) ∧
        ∀ S : Finset (Fin (n + 1)), S.card ≠ q + 1 → c S = 0 :=
  Iff.rfl

/-- The Čech differential takes degree-`q` cochains to degree-`(q + 1)` cochains. -/
theorem laurentCechDiff_mem_laurentCechCochains {c : LaurentCochain R n}
    (hc : c ∈ laurentCechCochains R n d q) :
    laurentCechDiff R n c ∈ laurentCechCochains R n d (q + 1) := by
  refine ⟨fun S => Submodule.sum_mem _ fun i hi => zsmul_mem ?_ _, fun S hS => ?_⟩
  · exact twistChart_mono (fun x hx => Finset.mem_coe.2 (Finset.erase_subset i S
      (Finset.mem_coe.1 hx))) ((mem_laurentCechCochains.1 hc).1 (S.erase i))
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [(mem_laurentCechCochains.1 hc).2 (S.erase i) (fun hcon => hS ?_), smul_zero]
    rw [← Finset.card_erase_add_one hi, hcon]

/-- The contracting homotopy takes degree-`(q + 1)` cochains to degree-`q` cochains: filtering by
`IsFirstNonneg · i` before adjoining `i` is exactly what keeps the result a section over the
smaller open. -/
theorem laurentCechHomotopy_mem_laurentCechCochains {c : LaurentCochain R n}
    (hc : c ∈ laurentCechCochains R n d (q + 1)) :
    laurentCechHomotopy R n c ∈ laurentCechCochains R n d q := by
  refine ⟨fun T => Submodule.sum_mem _ fun i hi => zsmul_mem ?_ _, fun T hT => ?_⟩
  · intro e he
    have hsupp : e ∈ (c (insert i T)).support.filter (fun e => IsFirstNonneg e i) := by
      have h := Finset.mem_coe.1 he
      rwa [Finsupp.support_filter] at h
    obtain ⟨he', hfirst⟩ := Finset.mem_filter.1 hsupp
    have hmem := (mem_laurentCechCochains.1 hc).1 (insert i T) (Finset.mem_coe.2 he')
    refine ⟨hmem.1, fun k hk => ?_⟩
    by_cases hki : k = i
    · exact hki ▸ hfirst.1
    · exact hmem.2 k fun hcon => (Finset.mem_insert.1 (Finset.mem_coe.1 hcon)).elim hki
        (fun h => hk (Finset.mem_coe.2 h))
  · refine Finset.sum_eq_zero fun i hi => ?_
    have hcard := Finset.card_insert_of_notMem (Finset.mem_compl.1 hi)
    have hz : c (insert i T) = 0 :=
      (mem_laurentCechCochains.1 hc).2 (insert i T) (by omega)
    rw [hz, Finsupp.filter_zero, smul_zero]

/-- **A Čech cochain of degree `q ≤ n - 1` has no all-negative monomial.** Its value at `S` is a
section over `D₊(∏_{i ∈ S} Tᵢ)` with `#S = q + 1 ≤ n`, so some variable is not inverted and the
corresponding exponent is nonnegative. This is the hypothesis of
`laurentCechDiff_laurentCechHomotopy_add`. -/
theorem exists_nonneg_of_mem_laurentCechCochains (hq : q + 1 ≤ n) {c : LaurentCochain R n}
    (hc : c ∈ laurentCechCochains R n d q) (S : Finset (Fin (n + 1)))
    (e : Fin (n + 1) → ℤ) (he : e ∈ (c S).support) : ∃ i, 0 ≤ e i := by
  by_cases hS : S.card = q + 1
  · have hne : Sᶜ.Nonempty := Finset.card_pos.1 (by
      rw [Finset.card_compl, Fintype.card_fin, hS]; omega)
    obtain ⟨k, hk⟩ := hne
    exact ⟨k, ((mem_laurentCechCochains.1 hc).1 S (Finset.mem_coe.2 he)).2 k
      fun hcon => Finset.mem_compl.1 hk (Finset.mem_coe.1 hcon)⟩
  · rw [(mem_laurentCechCochains.1 hc).2 S hS] at he
    exact absurd he (by simp)

/-- **For `-n ≤ d` no Čech cochain of `𝒪(d)` has an all-negative monomial, in any degree**:
there is no degree-`d` Laurent monomial in `n + 1` variables with every exponent negative. -/
theorem exists_nonneg_of_mem_laurentCechCochains_of_le (hd : -(n : ℤ) ≤ d)
    {c : LaurentCochain R n} (hc : c ∈ laurentCechCochains R n d q)
    (S : Finset (Fin (n + 1))) (e : Fin (n + 1) → ℤ) (he : e ∈ (c S).support) :
    ∃ i, 0 ≤ e i := by
  by_contra hcon
  rw [not_exists] at hcon
  have hmem : e ∈ laurentMonomials n d (S : Set (Fin (n + 1))) :=
    (mem_laurentCechCochains.1 hc).1 S (Finset.mem_coe.2 he)
  exact Set.eq_empty_iff_forall_notMem.1 ((negativeLaurentMonomials_eq_empty_iff n d).2 hd) e
    ⟨hmem.1, fun i => not_le.1 (hcon i)⟩

/-- **Above degree `n` the standard cover of `ℙⁿ_R` has no Čech cochains at all**: a cochain of
degree `q > n` would be concentrated on the `(q + 1)`-element subsets of an `(n + 1)`-element
set. Hence `Hᵠ(ℙⁿ_R, 𝒪(d)) = 0` for `q > n` already at the level of cochains. -/
theorem laurentCechCochains_eq_bot (hq : n < q) : laurentCechCochains R n d q = ⊥ := by
  refine le_antisymm (fun c hc => (Submodule.mem_bot R).2 (funext fun S => ?_)) bot_le
  refine (mem_laurentCechCochains.1 hc).2 S fun hcon => ?_
  have h := S.card_le_univ
  rw [hcon, Fintype.card_fin] at h
  omega

end Cochains

section Vanishing

/-- **Čech cocycles with no all-negative monomial are coboundaries.** The coboundary is the
explicit value of the contracting homotopy; this is the engine behind every vanishing range of
`Hᵠ(ℙⁿ_R, 𝒪(d))` except `q = n, d < -n`. -/
theorem exists_laurentCechDiff_eq_of_exists_nonneg {c : LaurentCochain R n}
    (hc : c ∈ laurentCechCochains R n d (q + 1))
    (hnn : ∀ (S : Finset (Fin (n + 1))) (e : Fin (n + 1) → ℤ), e ∈ (c S).support → ∃ i, 0 ≤ e i)
    (hdc : laurentCechDiff R n c = 0) :
    ∃ b ∈ laurentCechCochains R n d q, laurentCechDiff R n b = c := by
  refine ⟨laurentCechHomotopy R n c, laurentCechHomotopy_mem_laurentCechCochains hc, ?_⟩
  have h := laurentCechDiff_laurentCechHomotopy_add c hnn
  rwa [hdc, map_zero, add_zero] at h

/-- **The middle-degree Čech cohomology of `𝒪(d)` on `ℙⁿ_R` vanishes, in the monomial model.**
For `0 < q + 1 < n` every degree-`(q + 1)` Čech cocycle of the standard cover is the Čech
coboundary of the explicit degree-`q` cochain `laurentCechHomotopy R n c`, for every `d`. -/
theorem exists_laurentCechDiff_eq (hq : q + 2 ≤ n) {c : LaurentCochain R n}
    (hc : c ∈ laurentCechCochains R n d (q + 1)) (hdc : laurentCechDiff R n c = 0) :
    ∃ b ∈ laurentCechCochains R n d q, laurentCechDiff R n b = c :=
  exists_laurentCechDiff_eq_of_exists_nonneg hc
    (exists_nonneg_of_mem_laurentCechCochains (by omega) hc) hdc

/-- **For `-n ≤ d` the Čech cohomology of `𝒪(d)` on `ℙⁿ_R` vanishes in every positive degree, in
the monomial model** — in particular for every `d ≥ 0`, and including the top degree `q = n`,
which the middle-degree statement does not reach. -/
theorem exists_laurentCechDiff_eq_of_le (hd : -(n : ℤ) ≤ d) {c : LaurentCochain R n}
    (hc : c ∈ laurentCechCochains R n d (q + 1)) (hdc : laurentCechDiff R n c = 0) :
    ∃ b ∈ laurentCechCochains R n d q, laurentCechDiff R n b = c :=
  exists_laurentCechDiff_eq_of_exists_nonneg hc
    (exists_nonneg_of_mem_laurentCechCochains_of_le hd hc) hdc

/-- The Čech differential as a map of Čech cochain modules of the standard cover of `ℙⁿ_R`. -/
def laurentCechDiffRestrict (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ) :
    laurentCechCochains R n d q →ₗ[R] laurentCechCochains R n d (q + 1) :=
  (laurentCechDiff R n).restrict fun _ hc => laurentCechDiff_mem_laurentCechCochains hc

/-- The restricted differential is the ambient one. -/
@[simp]
theorem laurentCechDiffRestrict_coe (c : laurentCechCochains R n d q) :
    (laurentCechDiffRestrict R n d q c : LaurentCochain R n) = laurentCechDiff R n c :=
  rfl

/-- Čech coboundaries are Čech cocycles. -/
theorem range_laurentCechDiffRestrict_le_ker :
    LinearMap.range (laurentCechDiffRestrict R n d q)
      ≤ LinearMap.ker (laurentCechDiffRestrict R n d (q + 1)) := by
  rintro _ ⟨b, rfl⟩
  refine LinearMap.mem_ker.2 (Subtype.ext ?_)
  show laurentCechDiff R n (laurentCechDiff R n (b : LaurentCochain R n)) = 0
  exact LinearMap.congr_fun laurentCechDiff_comp_self (b : LaurentCochain R n)

/-- Coboundaries are all the cocycles as soon as every cocycle is the differential of a cochain. -/
private theorem range_laurentCechDiffRestrict_eq_ker
    (h : ∀ c ∈ laurentCechCochains R n d (q + 1), laurentCechDiff R n c = 0 →
      ∃ b ∈ laurentCechCochains R n d q, laurentCechDiff R n b = c) :
    LinearMap.range (laurentCechDiffRestrict R n d q)
      = LinearMap.ker (laurentCechDiffRestrict R n d (q + 1)) :=
  le_antisymm range_laurentCechDiffRestrict_le_ker fun c hc => by
    obtain ⟨b, hb, hbc⟩ := h c c.2 (congrArg Subtype.val (LinearMap.mem_ker.1 hc))
    exact ⟨⟨b, hb⟩, Subtype.ext hbc⟩

/-- **`Hᵠ(ℙⁿ_R, 𝒪(d)) = 0` for `0 < q < n`, at the Čech level in the monomial model**: the
cocycles in degree `q + 1` are exactly the coboundaries from degree `q`, for every `d`. -/
theorem range_laurentCechDiffRestrict (hq : q + 2 ≤ n) :
    LinearMap.range (laurentCechDiffRestrict R n d q)
      = LinearMap.ker (laurentCechDiffRestrict R n d (q + 1)) :=
  range_laurentCechDiffRestrict_eq_ker fun _ hc => exists_laurentCechDiff_eq hq hc

/-- **`Hᵠ(ℙⁿ_R, 𝒪(d)) = 0` for every `q > 0` when `-n ≤ d`, at the Čech level in the monomial
model**, the top degree `q = n` included. -/
theorem range_laurentCechDiffRestrict_of_le (hd : -(n : ℤ) ≤ d) :
    LinearMap.range (laurentCechDiffRestrict R n d q)
      = LinearMap.ker (laurentCechDiffRestrict R n d (q + 1)) :=
  range_laurentCechDiffRestrict_eq_ker fun _ hc => exists_laurentCechDiff_eq_of_le hd hc

/-- The Čech sign of the smaller element of a two-element index set is `+1`. -/
theorem cechSign_pair_left {a b : Fin (n + 1)} (hab : a < b) :
    Cech.cechSign ({a, b} : Finset (Fin (n + 1))) a = 1 := by
  simp [Cech.cechSign, Finset.filter_insert, Finset.filter_singleton, not_lt.2 hab.le]

/-- The Čech sign of the larger element of a two-element index set is `-1`. -/
theorem cechSign_pair_right {a b : Fin (n + 1)} (hab : a < b) :
    Cech.cechSign ({a, b} : Finset (Fin (n + 1))) b = -1 := by
  simp [Cech.cechSign, Finset.filter_insert, Finset.filter_singleton, hab]

/-- **The Čech differential on an overlap of two standard opens is the difference of the two
restrictions.** -/
theorem laurentCechDiff_apply_pair (c : LaurentCochain R n) {a b : Fin (n + 1)} (hab : a < b) :
    laurentCechDiff R n c {a, b} = c {b} - c {a} := by
  have hne : a ≠ b := ne_of_lt hab
  have h1 : ({a, b} : Finset (Fin (n + 1))).erase a = {b} :=
    Finset.erase_insert (by simp [hne])
  have h2 : ({a, b} : Finset (Fin (n + 1))).erase b = {a} := by
    rw [Finset.erase_insert_of_ne hne]; simp
  rw [laurentCechDiff_apply, Finset.sum_pair hne, cechSign_pair_left hab,
    cechSign_pair_right hab, h1, h2, one_smul, neg_one_smul, sub_eq_add_neg]

/-- **The degree-zero Čech cocycle condition**: a Čech cocycle of degree zero of the standard
cover takes one common value on all the standard opens, because any two indices form an
overlap. -/
theorem apply_singleton_eq_of_laurentCechDiff_eq_zero {c : LaurentCochain R n}
    (hc : laurentCechDiff R n c = 0) (i j : Fin (n + 1)) : c {i} = c {j} := by
  have key : ∀ a b : Fin (n + 1), a < b → c {a} = c {b} := by
    intro a b hab
    have h := congrFun hc ({a, b} : Finset (Fin (n + 1)))
    rw [laurentCechDiff_apply_pair c hab, Pi.zero_apply, sub_eq_zero] at h
    exact h.symm
  rcases lt_trichotomy i j with h | h | h
  · exact key i j h
  · rw [h]
  · exact (key j i h).symm

/-- **The degree-zero Čech cohomology of `𝒪(d)` on `ℙⁿ_R` vanishes for `d < 0`**, as soon as
`0 < n`: a family of Laurent sections agreeing on the overlaps has one common value, which is
then regular along every variable, and there is no polynomial section in negative degree. -/
theorem ker_laurentCechDiffRestrict_zero_eq_bot (hn : 0 < n) (hd : d < 0) :
    LinearMap.ker (laurentCechDiffRestrict R n d 0) = ⊥ := by
  refine le_antisymm (fun c hc => (Submodule.mem_bot R).2 (Subtype.ext (funext fun S => ?_)))
    bot_le
  have hz : laurentCechDiff R n (c : LaurentCochain R n) = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.1 hc)
  have hmem : (c : LaurentCochain R n) {(0 : Fin (n + 1))}
      ∈ twistChart R n d (∅ : Set (Fin (n + 1))) := by
    rw [← twistChart_iInf_singleton n hn d]
    refine (Submodule.mem_iInf _).2 fun i => ?_
    rw [apply_singleton_eq_of_laurentCechDiff_eq_zero hz 0 i, ← Finset.coe_singleton]
    exact (mem_laurentCechCochains.1 c.2).1 {i}
  have hzero : (c : LaurentCochain R n) {(0 : Fin (n + 1))} = 0 :=
    (Submodule.eq_bot_iff _).1 (twistChart_eq_bot_of_neg n hd) _ hmem
  show (c : LaurentCochain R n) S = 0
  by_cases hS : S.card = 0 + 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hS
    rw [apply_singleton_eq_of_laurentCechDiff_eq_zero hz i 0, hzero]
  · exact (mem_laurentCechCochains.1 c.2).2 S hS


/-- A degree-`d` polynomial section of `𝒪(d)` read as a degree-zero Čech cochain of the standard
cover of `ℙⁿ_R`: the same section on each standard open `D₊(Tᵢ)`, and zero in all other
degrees. -/
def laurentDiagonalCochain (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    twistChart R n d (∅ : Set (Fin (n + 1))) →ₗ[R] LaurentCochain R n where
  toFun z S := if S.card = 1 then (z : (Fin (n + 1) → ℤ) →₀ R) else 0
  map_add' z w := funext fun S => by by_cases hS : S.card = 1 <;> simp [hS]
  map_smul' r z := funext fun S => by by_cases hS : S.card = 1 <;> simp [hS]

/-- The diagonal cochain is the given section on every one-element index set and zero
elsewhere. -/
@[simp]
theorem laurentDiagonalCochain_apply (z : twistChart R n d (∅ : Set (Fin (n + 1))))
    (S : Finset (Fin (n + 1))) :
    laurentDiagonalCochain R n d z S =
      if S.card = 1 then (z : (Fin (n + 1) → ℤ) →₀ R) else 0 :=
  rfl

/-- A polynomial section, read diagonally, is a Čech cochain of degree zero. -/
theorem laurentDiagonalCochain_mem (z : twistChart R n d (∅ : Set (Fin (n + 1)))) :
    laurentDiagonalCochain R n d z ∈ laurentCechCochains R n d 0 := by
  refine ⟨fun S => ?_, fun S hS => ?_⟩
  · rw [laurentDiagonalCochain_apply]
    by_cases hc : S.card = 1
    · rw [ite_eq_left hc]
      exact twistChart_mono (Set.empty_subset _) z.2
    · rw [ite_eq_right hc]
      exact zero_mem _
  · rw [laurentDiagonalCochain_apply, ite_eq_right (by simpa using hS)]

/-- A polynomial section, read diagonally, is a Čech cocycle. -/
theorem laurentCechDiff_laurentDiagonalCochain (z : twistChart R n d (∅ : Set (Fin (n + 1)))) :
    laurentCechDiff R n (laurentDiagonalCochain R n d z) = 0 := by
  have key : ∀ u v : Fin (n + 1), u < v →
      laurentCechDiff R n (laurentDiagonalCochain R n d z) {u, v} = 0 := fun u v huv => by
    rw [laurentCechDiff_apply_pair _ huv]
    simp
  refine funext fun S => ?_
  by_cases hS : S.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hS
    rcases lt_or_gt_of_ne hab with h | h
    · exact key a b h
    · rw [Finset.pair_comm]
      exact key b a h
  · rw [laurentCechDiff_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard := Finset.card_erase_of_mem hi
    have hpos := Finset.card_pos.2 ⟨i, hi⟩
    rw [laurentDiagonalCochain_apply, ite_eq_right (by omega), smul_zero]

/-- Distinct polynomial sections give distinct diagonal cochains. -/
theorem laurentDiagonalCochain_injective :
    Function.Injective (laurentDiagonalCochain R n d) := fun z w h =>
  Subtype.ext (by simpa using congrFun h ({0} : Finset (Fin (n + 1))))

/-- A degree-`d` polynomial section read as a degree-zero Čech cocycle of the standard cover of
`ℙⁿ_R`. -/
def laurentDiagonalCocycle (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    twistChart R n d (∅ : Set (Fin (n + 1))) →ₗ[R]
      LinearMap.ker (laurentCechDiffRestrict R n d 0) :=
  LinearMap.codRestrict _
    (LinearMap.codRestrict (laurentCechCochains R n d 0) (laurentDiagonalCochain R n d)
      laurentDiagonalCochain_mem)
    fun z => LinearMap.mem_ker.2 (Subtype.ext (laurentCechDiff_laurentDiagonalCochain z))

/-- The underlying cochain of `laurentDiagonalCocycle` is `laurentDiagonalCochain`. -/
@[simp]
theorem laurentDiagonalCocycle_coe (z : twistChart R n d (∅ : Set (Fin (n + 1)))) :
    ((laurentDiagonalCocycle R n d z : laurentCechCochains R n d 0) : LaurentCochain R n)
      = laurentDiagonalCochain R n d z :=
  rfl

/-- **`H⁰(ℙⁿ_R, 𝒪(d))` is the module of polynomial sections, at the Čech level in the monomial
model**, for `0 < n`: a degree-zero Čech cocycle of the standard cover has one common value,
which is then regular along every variable. Composing with
`Stacks.ProjectiveSpace.Cohomology.twistChartEmptyLinearEquiv` identifies it with the degree-`d`
homogeneous polynomials in `T₀, …, Tₙ` when `0 ≤ d`, and
`ker_laurentCechDiffRestrict_zero_eq_bot` is the same statement for `d < 0`. -/
def laurentCechCohomologyZeroEquiv (hn : 0 < n) :
    twistChart R n d (∅ : Set (Fin (n + 1))) ≃ₗ[R]
      LinearMap.ker (laurentCechDiffRestrict R n d 0) :=
  LinearEquiv.ofBijective (laurentDiagonalCocycle R n d)
    ⟨fun z w h => laurentDiagonalCochain_injective
        (congrArg (fun x : LinearMap.ker (laurentCechDiffRestrict R n d 0) =>
          ((x : laurentCechCochains R n d 0) : LaurentCochain R n)) h),
      fun c => by
        have hz : laurentCechDiff R n (c : LaurentCochain R n) = 0 :=
          congrArg Subtype.val (LinearMap.mem_ker.1 c.2)
        have hmem : (c : LaurentCochain R n) {(0 : Fin (n + 1))}
            ∈ twistChart R n d (∅ : Set (Fin (n + 1))) := by
          rw [← twistChart_iInf_singleton n hn d]
          refine (Submodule.mem_iInf _).2 fun i => ?_
          rw [apply_singleton_eq_of_laurentCechDiff_eq_zero hz 0 i, ← Finset.coe_singleton]
          exact (mem_laurentCechCochains.1 (c : laurentCechCochains R n d 0).2).1 {i}
        refine ⟨⟨_, hmem⟩, Subtype.ext (Subtype.ext (funext fun S => ?_))⟩
        rw [laurentDiagonalCocycle_coe, laurentDiagonalCochain_apply]
        by_cases hS : S.card = 1
        · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hS
          rw [ite_eq_left (by simp)]
          exact apply_singleton_eq_of_laurentCechDiff_eq_zero hz 0 i
        · rw [ite_eq_right hS,
            (mem_laurentCechCochains.1 (c : laurentCechCochains R n d 0).2).2 S
              (by simpa using hS)]⟩


/-- **The top-degree Čech differential of the standard cover of `ℙ^{m+1}_R`**, read as a map into
the degree-`d` Laurent sections on the total intersection `D₊(T₀ ⋯ T_{m+1})`: a Čech cochain of
degree `m` is sent to the value of its coboundary on the only index set of size `m + 2`. -/
def laurentTopCechDiff (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    laurentCechCochains R (m + 1) d m →ₗ[R] ((Fin (m + 1 + 1) → ℤ) →₀ R) :=
  (LinearMap.proj (R := R) (φ := fun _ : Finset (Fin (m + 1 + 1)) =>
      ((Fin (m + 1 + 1) → ℤ) →₀ R)) Finset.univ).comp
    ((laurentCechDiff R (m + 1)).comp (laurentCechCochains R (m + 1) d m).subtype)

/-- The top-degree differential, as the signed sum of the `n + 1` codimension-one faces of the
total index set. -/
@[simp]
theorem laurentTopCechDiff_apply {m : ℕ} (b : laurentCechCochains R (m + 1) d m) :
    laurentTopCechDiff R m d b = ∑ i : Fin (m + 1 + 1), Cech.cechSign Finset.univ i •
      (b : LaurentCochain R (m + 1)) (Finset.univ.erase i) :=
  rfl

/-- The index set complementary to `i` is the index set `{0, …, m+1}` with `i` deleted. -/
theorem coe_univ_erase (m : ℕ) (i : Fin (m + 1 + 1)) :
    ((Finset.univ.erase i : Finset (Fin (m + 1 + 1))) : Set (Fin (m + 1 + 1)))
      = ({i}ᶜ : Set (Fin (m + 1 + 1))) := by
  rw [Finset.coe_erase, Finset.coe_univ]
  exact (Set.compl_eq_univ_sdiff _).symm

/-- **The top-degree Čech differential of this complex has the same image as
`Stacks.ProjectiveSpace.Cohomology.topCechDiff`.** Hence the top-degree computation —
`topCechDiff_sup_negativeTwistPart`, `isCompl_negativeTwistPart` and `topCechCohomologyEquiv` —
computes the degree-`(m+1)` cohomology of the complex of this file, and all of
`Hᵠ(ℙⁿ_R, 𝒪(d))` becomes a statement about one Čech complex. -/
theorem range_laurentTopCechDiff (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    LinearMap.range (laurentTopCechDiff R m d)
      = LinearMap.range (topCechDiff R (m + 1) d) := by
  rw [range_topCechDiff]
  refine le_antisymm ?_ (iSup_le fun i x hx => ?_)
  · rintro _ ⟨b, rfl⟩
    rw [laurentTopCechDiff_apply]
    refine Submodule.sum_mem _ fun i _ => zsmul_mem ?_ _
    refine le_iSup (fun j => twistChart R (m + 1) d ({j}ᶜ : Set (Fin (m + 1 + 1)))) i ?_
    rw [← coe_univ_erase m i]
    exact (mem_laurentCechCochains.1 b.2).1 _
  · have hcard : (Finset.univ.erase i).card = m + 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    have hmemb : (fun S : Finset (Fin (m + 1 + 1)) =>
        if S = Finset.univ.erase i then Cech.cechSign Finset.univ i • x else 0)
          ∈ laurentCechCochains R (m + 1) d m := by
      refine ⟨fun S => ?_, fun S hS => ?_⟩
      · show (if S = Finset.univ.erase i then Cech.cechSign Finset.univ i • x else 0)
          ∈ twistChart R (m + 1) d (S : Set (Fin (m + 1 + 1)))
        by_cases hSi : S = Finset.univ.erase i
        · rw [ite_eq_left hSi, hSi, coe_univ_erase m i]
          exact zsmul_mem hx _
        · rw [ite_eq_right hSi]
          exact zero_mem _
      · show (if S = Finset.univ.erase i then Cech.cechSign Finset.univ i • x else 0) = 0
        refine ite_eq_right fun hSi => hS ?_
        rw [hSi]
        exact hcard
    refine ⟨⟨_, hmemb⟩, ?_⟩
    rw [laurentTopCechDiff_apply]
    refine (Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hj => ?_).trans ?_
    · have hne : Finset.univ.erase j ≠ Finset.univ.erase i := fun hcon => by
        have hmem : i ∈ Finset.univ.erase j :=
          Finset.mem_erase.2 ⟨fun h => hj h.symm, Finset.mem_univ i⟩
        rw [hcon] at hmem
        exact (Finset.mem_erase.1 hmem).1 rfl
      show Cech.cechSign Finset.univ j •
        (if Finset.univ.erase j = Finset.univ.erase i then
          Cech.cechSign Finset.univ i • x else 0) = 0
      rw [ite_eq_right hne, smul_zero]
    · show Cech.cechSign Finset.univ i •
        (if Finset.univ.erase i = Finset.univ.erase i then
          Cech.cechSign Finset.univ i • x else 0) = x
      rw [ite_eq_left rfl, cechSign_smul_cechSign_smul]

end Vanishing

end Stacks.ProjectiveSpace.Cohomology

end
