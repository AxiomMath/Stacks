module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MonomialPairing
public import StacksFrontier.CategoryTheory.Abelian.KernelLadder

/-!
# The dual Koszul strand of the monomial sums is exact

Let `S` be a scheme, let `n = m + 1 ≥ 1` and let `e ≥ 1` be an integer. The direct sums

`Dʲ = ⨁_{|s| = j} monomialSum (e - j)`,

indexed by the `j`-element sets of coordinates, carry the differentials obtained from the Koszul
matrix of the coordinates by replacing multiplication by `Tᵢ` with its transpose on the monomial
sums. The purpose of this file is the matrix calculus of those differentials: their entries,
the retraction of the first one and the homotopy which together exhibit

`D⁰ ⟶ D¹`

as a **kernel** of `D¹ ⟶ D²`. The splitting is produced by choosing, for each multidegree of
positive total degree, a coordinate dividing it; the two identities

`d⁰ ≫ r = 1`  and  `r ≫ d⁰ + d¹ ≫ t = 1`

are the degree-`e` strand of the Koszul complex of the coordinates in the polynomial ring, read
through the monomial bases, and a split pair is a kernel.

Dualised, this says that the degree-`e` part of the polynomial algebra is the syzygies of the
Koszul relations among the coordinates; it is the right-hand side of the degree-`n` row of the
display of [Stacks, Tag 01XW] in the form in which the row's induction on the complementary
degree uses it.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `divCoord`, `splitIdx`, `splitRest`: division of a multidegree by a coordinate dividing it,
  and the choice of such a coordinate.
* `singletonIdx`, `pairIdx`: the one- and two-element sets of coordinates.
* `dualCoeff`, `dualDiff`: **the dual Koszul differential.**

## Main results

* `exists_pos_coeff`: a multidegree of positive total degree is divisible by a coordinate.
* `dualCoeff_eq` and `dualCoeff_eq_zero`: **the matrix entries of the dual differential**, the
  sum over the coordinates collapsing to at most one term; `dualCoeff_zero`, `dualCoeff_one` and
  `dualCoeff_one_eq_zero` are their readings in the two degrees the splitting uses.
* `monomialSumMul_ι_π`: the matrix entry of the transpose of multiplication by a coordinate.
* `monomialSumMul_comp_comm`: the transposes of multiplication by two coordinates commute.
* `dualDiff_comp_dualDiff`: **the first two dual differentials compose to zero.**
* `isLimit_dualDiff`: **`D⁰ ⟶ D¹` is a kernel of `D¹ ⟶ D²`.**

## Implementation notes

The index sets of the two levels are of different universes — the sets of coordinates lie in
`Type 0` and the multidegrees in the universe of the base scheme — so the outer level uses
`CategoryTheory.Limits.biproduct.matrix`, which is available only for `Type 0`, and the inner
level uses `CategoryTheory.Limits.biproduct.lift` and
`CategoryTheory.Limits.biproduct.desc`, which are universe-polymorphic.

The matrix entry of the dual differential is a sum over all coordinates of a term supported on
the one coordinate adjoined to the index set, as in
`Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulCoeff`, so that no dependent case split appears
in the definition; the three evaluation lemmas collapse the sum.

Division of a multidegree by a coordinate dividing it is obtained from an existence statement by
`Exists.choose`, and is used only through its defining property; nothing below depends on which
coordinate the choice function picks.

No `stacks` attribute is attached: what is proved here is a statement about monomials, used as
one half of the degree-`n` row of [Stacks, Tag 01XW].

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

open Stacks.AlgebraicGeometry.ProjKoszulComplex (koszulIndex koszulSign
  biproduct_ι_comp_comp_π zsmul_comp_add_zsmul_comp_eq_zero)

/-! ### Dividing a multidegree by a coordinate -/

/-- **A multidegree of positive total degree has a positive exponent.** -/
theorem exists_pos_coeff {n : ℕ} {t : ℤ} (ht : 1 ≤ t) (b : MonomialIndex.{u} n t) :
    ∃ i : Fin (n + 1), 1 ≤ b.1 (ULift.up i) := by
  by_contra hcon
  push Not at hcon
  have hzero : b.1 = 0 := by
    ext x
    have hx := hcon x.down
    rw [ULift.up_down] at hx
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega
  have hb := b.2
  rw [hzero, map_zero] at hb
  omega

/-- **A multidegree with a positive `i`-th exponent is `δᵢ` times a multidegree.** -/
theorem exists_eq_addOf {n : ℕ} {t t' : ℤ} (ht : 1 + t' = t) (b : MonomialIndex.{u} n t)
    (i : Fin (n + 1)) (hi : 1 ≤ b.1 (ULift.up i)) :
    ∃ c : MonomialIndex.{u} n t', MonomialIndex.addOf (coordIndex i) c ht = b := by
  have hval : Finsupp.single (ULift.up i) 1 + (b.1 - Finsupp.single (ULift.up i) 1) = b.1 := by
    ext y
    rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hy : ULift.up i = y
    · subst hy; rw [if_pos rfl]; omega
    · rw [if_neg hy]; omega
  have hdeg : (((b.1 - Finsupp.single (ULift.up i) 1).degree : ℤ)) = t' := by
    have h2 := congrArg Finsupp.degree hval
    rw [map_add, Finsupp.degree_single] at h2
    have hb := b.2
    omega
  exact ⟨⟨_, hdeg⟩, Subtype.ext hval⟩

/-- **The quotient of a multidegree by a coordinate dividing it.** -/
def divCoord {n : ℕ} (i : Fin (n + 1)) {t t' : ℤ} (ht : 1 + t' = t) (b : MonomialIndex.{u} n t)
    (hi : 1 ≤ b.1 (ULift.up i)) : MonomialIndex.{u} n t' :=
  (exists_eq_addOf ht b i hi).choose

/-- The quotient of a multidegree by a coordinate dividing it, times that coordinate, is the
multidegree. -/
theorem divCoord_spec {n : ℕ} (i : Fin (n + 1)) {t t' : ℤ} (ht : 1 + t' = t)
    (b : MonomialIndex.{u} n t) (hi : 1 ≤ b.1 (ULift.up i)) :
    MonomialIndex.addOf (coordIndex i) (divCoord i ht b hi) ht = b :=
  (exists_eq_addOf ht b i hi).choose_spec

/-- **A chosen coordinate dividing a multidegree of positive total degree.** -/
def splitIdx {n : ℕ} {t : ℤ} (ht : 1 ≤ t) (b : MonomialIndex.{u} n t) : Fin (n + 1) :=
  (exists_pos_coeff ht b).choose

/-- The chosen coordinate divides the multidegree. -/
theorem splitIdx_spec {n : ℕ} {t : ℤ} (ht : 1 ≤ t) (b : MonomialIndex.{u} n t) :
    1 ≤ b.1 (ULift.up (splitIdx ht b)) :=
  (exists_pos_coeff ht b).choose_spec

/-- **The quotient of a multidegree of positive total degree by the chosen coordinate.** -/
def splitRest {n : ℕ} {t t' : ℤ} (ht1 : 1 ≤ t) (ht : 1 + t' = t) (b : MonomialIndex.{u} n t) :
    MonomialIndex.{u} n t' :=
  divCoord (splitIdx ht1 b) ht b (splitIdx_spec ht1 b)

/-- The chosen coordinate times the quotient is the multidegree. -/
theorem splitRest_spec {n : ℕ} {t t' : ℤ} (ht1 : 1 ≤ t) (ht : 1 + t' = t)
    (b : MonomialIndex.{u} n t) :
    MonomialIndex.addOf (coordIndex (splitIdx ht1 b)) (splitRest ht1 ht b) ht = b :=
  divCoord_spec _ ht b _

/-- **Multidegrees cancel from a product.** -/
theorem addOf_left_cancel {n : ℕ} {e₁ e₂ e₃ : ℤ} (a : MonomialIndex.{u} n e₁)
    {c c' : MonomialIndex.{u} n e₂} {h : e₁ + e₂ = e₃}
    (hcc : MonomialIndex.addOf a c h = MonomialIndex.addOf a c' h) : c = c' :=
  Subtype.ext (add_left_cancel (a := a.1) (congrArg Subtype.val hcc))

/-- The `i`-th exponent of `δₖ` times a multidegree, for `k ≠ i`, is that of the multidegree. -/
theorem addOf_coordIndex_apply_of_ne {n : ℕ} {e₁ e₂ : ℤ} {k i : Fin (n + 1)} (hki : k ≠ i)
    (c : MonomialIndex.{u} n e₁) (h : 1 + e₁ = e₂) :
    (MonomialIndex.addOf (coordIndex k) c h).1 (ULift.up i) = c.1 (ULift.up i) := by
  rw [MonomialIndex.addOf_val, Finsupp.add_apply, coordIndex, Finsupp.single_apply,
    if_neg (fun hh => hki (ULift.up.inj hh)), zero_add]

/-- The `i`-th exponent of `δᵢ` times a multidegree is one more than that of the
multidegree. -/
theorem addOf_coordIndex_apply_self {n : ℕ} {e₁ e₂ : ℤ} (i : Fin (n + 1))
    (c : MonomialIndex.{u} n e₁) (h : 1 + e₁ = e₂) :
    (MonomialIndex.addOf (coordIndex i) c h).1 (ULift.up i) = c.1 (ULift.up i) + 1 := by
  rw [MonomialIndex.addOf_val, Finsupp.add_apply, coordIndex, Finsupp.single_eq_same]
  omega

/-! ### One- and two-element sets of coordinates -/

/-- **The one-element set of coordinates `{i}`.** -/
def singletonIdx {N : ℕ} (i : Fin N) : koszulIndex N 1 := ⟨{i}, by simp⟩

/-- The underlying set of `singletonIdx i` is `{i}`. -/
@[simp] theorem singletonIdx_val {N : ℕ} (i : Fin N) : (singletonIdx i).1 = {i} := rfl

/-- **The two-element set of coordinates `{k, i}`**, for `k ≠ i`. -/
def pairIdx {N : ℕ} (k i : Fin N) (h : k ≠ i) : koszulIndex N 2 :=
  ⟨{k, i}, by
    rw [Finset.card_insert_of_notMem (by simpa using h), Finset.card_singleton]
    rfl⟩

/-- The underlying set of `pairIdx k i h` is `{k, i}`. -/
@[simp] theorem pairIdx_val {N : ℕ} (k i : Fin N) (h : k ≠ i) : (pairIdx k i h).1 = {k, i} := rfl

/-- **A one-element set of coordinates is a singleton.** -/
theorem koszulIndex_one_eq {N : ℕ} (s : koszulIndex N 1) : ∃ i, s = singletonIdx i := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.1 (show s.1.card = 1 by have := s.2; omega)
  exact ⟨i, Subtype.ext hi⟩

/-! ### The dual Koszul differential -/

variable (m : ℕ) (S : Scheme.{u})

/-- The inclusion of a summand followed by a projection of a biproduct of copies of one object is
the identity or zero. -/
private theorem biproduct_ι_π_ite {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type*}
    [DecidableEq J] (X : C) [HasBiproduct fun _ : J => X] (x y : J) :
    biproduct.ι (fun _ : J => X) x ≫ biproduct.π _ y = if x = y then 𝟙 X else 0 := by
  rw [biproduct.ι_π]
  by_cases h : x = y
  · rw [dif_pos h, if_pos h]; subst h; simp
  · rw [dif_neg h, if_neg h]

/-- The component of a monomial sum at a multidegree, paired with the inclusion of another. -/
@[reassoc] theorem monomialSum_ι_π (t : ℤ) (x y : MonomialIndex.{u} (m + 1) t) :
    biproduct.ι (fun _ : MonomialIndex.{u} (m + 1) t => Scheme.unitModule S) x ≫
        biproduct.π _ y = if x = y then 𝟙 (Scheme.unitModule S) else 0 := by
  exact biproduct_ι_π_ite _ x y

/-- **The matrix entry of the transpose of multiplication by a coordinate.** -/
theorem monomialSumMul_ι_π (i : Fin (m + 1 + 1)) (t t' : ℤ) (ht : 1 + t' = t)
    (b : MonomialIndex.{u} (m + 1) t) (b' : MonomialIndex.{u} (m + 1) t') :
    biproduct.ι (fun _ : MonomialIndex.{u} (m + 1) t => Scheme.unitModule S) b ≫
        monomialSumMul (m + 1) S i t t' ht ≫ biproduct.π _ b' =
      if b = MonomialIndex.addOf (coordIndex i) b' ht then 𝟙 (Scheme.unitModule S) else 0 := by
  rw [monomialSumMul, biproduct.lift_π, monomialSum_ι_π]

/-- **The matrix entry of the dual Koszul differential**: the Koszul sign of the coordinate
adjoined to the index set times the transpose of multiplication by that coordinate, and zero if
no coordinate is adjoined. -/
def dualCoeff (j j' : ℤ) {t t' : ℤ} (ht : 1 + t' = t) (s : koszulIndex (m + 1 + 1) j)
    (u : koszulIndex (m + 1 + 1) j') :
    monomialSum (m + 1) S t ⟶ monomialSum (m + 1) S t' :=
  ∑ i : Fin (m + 1 + 1), if u.1 = insert i s.1 ∧ i ∉ s.1 then
    koszulSign i s.1 • monomialSumMul (m + 1) S i t t' ht else 0

/-- **The dual Koszul differential** of the monomial sums. The target index `j'` is a named
integer so that successive differentials compose with no transport. -/
def dualDiff (j j' : ℤ) (_hj : j + 1 = j') {t t' : ℤ} (ht : 1 + t' = t) :
    (⨁ fun _ : koszulIndex (m + 1 + 1) j => monomialSum (m + 1) S t) ⟶
      (⨁ fun _ : koszulIndex (m + 1 + 1) j' => monomialSum (m + 1) S t') :=
  biproduct.matrix (dualCoeff m S j j' ht)

/-- **The matrix entry of the dual Koszul differential at a pair of index sets differing by one
coordinate** is the Koszul sign of that coordinate in the source set times the transpose of
multiplication by it. The coordinate is determined by the pair, so the sum defining the entry
has only this one nonzero term. -/
theorem dualCoeff_eq (j j' : ℤ) {t t' : ℤ} (ht : 1 + t' = t) (s : koszulIndex (m + 1 + 1) j)
    (u : koszulIndex (m + 1 + 1) j') {i : Fin (m + 1 + 1)} (hi : i ∉ s.1)
    (hu : u.1 = insert i s.1) :
    dualCoeff m S j j' ht s u = koszulSign i s.1 • monomialSumMul (m + 1) S i t t' ht := by
  refine Eq.trans (Finset.sum_eq_single_of_mem i (Finset.mem_univ i) ?_) (ite_eq_left ⟨hu, hi⟩)
  intro b _ hb
  refine ite_eq_right fun h => hb ?_
  have hbt : b ∈ insert i s.1 := hu ▸ h.1 ▸ Finset.mem_insert_self b s.1
  exact (Finset.mem_insert.1 hbt).resolve_right h.2

/-- **The matrix entry of the dual Koszul differential vanishes** at a pair of index sets not
differing by a single new coordinate. -/
theorem dualCoeff_eq_zero (j j' : ℤ) {t t' : ℤ} (ht : 1 + t' = t) (s : koszulIndex (m + 1 + 1) j)
    (u : koszulIndex (m + 1 + 1) j')
    (h : ∀ i : Fin (m + 1 + 1), i ∉ s.1 → u.1 ≠ insert i s.1) :
    dualCoeff m S j j' ht s u = 0 :=
  Finset.sum_eq_zero fun i _ => ite_eq_right fun hc => h i hc.2 hc.1

/-- The column of the dual Koszul differential at a pair of index sets is its matrix entry. -/
@[reassoc] theorem ι_dualDiff_π (j j' : ℤ) (hj : j + 1 = j') {t t' : ℤ} (ht : 1 + t' = t)
    (s : koszulIndex (m + 1 + 1) j) (u : koszulIndex (m + 1 + 1) j') :
    biproduct.ι _ s ≫ dualDiff m S j j' hj ht ≫ biproduct.π _ u =
      dualCoeff m S j j' ht s u := by
  rw [dualDiff, ← Category.assoc, biproduct.ι_matrix, biproduct.lift_π]

/-- **The matrix entry of the dual Koszul differential out of degree zero** is the transpose of
multiplication by the coordinate indexing the target. -/
theorem dualCoeff_zero (j' : ℤ) {t t' : ℤ} (ht : 1 + t' = t) (s : koszulIndex (m + 1 + 1) 0)
    (k : Fin (m + 1 + 1)) (u : koszulIndex (m + 1 + 1) j') (hu : u.1 = {k}) :
    dualCoeff m S 0 j' ht s u = monomialSumMul (m + 1) S k t t' ht := by
  have hs : s.1 = ∅ := Finset.card_eq_zero.1 (by have := s.2; omega)
  rw [dualCoeff_eq m S 0 j' ht s u (i := k) (by rw [hs]; exact Finset.notMem_empty k)
    (by rw [hu, hs, Finset.insert_empty]), hs]
  simp [koszulSign]

/-- **The matrix entry of the dual Koszul differential out of a one-element set** is the Koszul
sign times the transpose of multiplication by the other coordinate of the target. -/
theorem dualCoeff_one (j' : ℤ) {t t' : ℤ} (ht : 1 + t' = t) (i k : Fin (m + 1 + 1))
    (hki : k ≠ i) (u : koszulIndex (m + 1 + 1) j') (hu : u.1 = {k, i}) :
    dualCoeff m S 1 j' ht (singletonIdx i) u =
      koszulSign k {i} • monomialSumMul (m + 1) S k t t' ht :=
  dualCoeff_eq m S 1 j' ht (singletonIdx i) u (by simpa using hki) (by rw [hu]; rfl)

/-- **The matrix entry of the dual Koszul differential out of a one-element set vanishes** when
the target does not contain that coordinate. -/
theorem dualCoeff_one_eq_zero (j' : ℤ) {t t' : ℤ} (ht : 1 + t' = t) (i : Fin (m + 1 + 1))
    (u : koszulIndex (m + 1 + 1) j') (hu : i ∉ u.1) :
    dualCoeff m S 1 j' ht (singletonIdx i) u = 0 :=
  dualCoeff_eq_zero m S 1 j' ht (singletonIdx i) u fun l _ hcon =>
    hu (by rw [hcon]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self i))

/-! ### The Koszul signs of a one-element set -/

/-- The Koszul sign of a coordinate in a one-element set is `-1` exactly when that set lies
below it. -/
theorem koszulSign_singleton {N : ℕ} (k i : Fin N) :
    koszulSign k {i} = if i < k then -1 else 1 := by
  rw [koszulSign, Finset.filter_singleton]
  by_cases h : i < k
  · rw [if_pos h, if_pos h, Finset.card_singleton, pow_one]
  · rw [if_neg h, if_neg h, Finset.card_empty, pow_zero]

/-- A Koszul sign squares to one. -/
theorem koszulSign_mul_self {N : ℕ} (k : Fin N) (s : Finset (Fin N)) :
    koszulSign k s * koszulSign k s = 1 := by
  rw [koszulSign, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

/-- **The two Koszul signs of a pair of distinct coordinates multiply to `-1`**, exactly one of
the two orderings holding. -/
theorem koszulSign_mul_swap {N : ℕ} {i i' : Fin N} (h : i ≠ i') :
    koszulSign i {i'} * koszulSign i' {i} = -1 := by
  rw [koszulSign_singleton, koszulSign_singleton]
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · rw [if_neg (not_lt_of_gt hlt), if_pos hlt, one_mul]
  · exact absurd heq h
  · rw [if_pos hgt, if_neg (not_lt_of_gt hgt), mul_one]

/-- **The two Koszul signs of a pair of distinct coordinates sum to zero**, exactly one of the
two orderings holding. -/
theorem koszulSign_add_swap {N : ℕ} {i i' : Fin N} (h : i ≠ i') :
    koszulSign i {i'} + koszulSign i' {i} = 0 := by
  rw [koszulSign_singleton, koszulSign_singleton]
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · rw [if_neg (not_lt_of_gt hlt), if_pos hlt]; ring
  · exact absurd heq h
  · rw [if_pos hgt, if_neg (not_lt_of_gt hgt)]; ring

/-- Two one-element sets of coordinates agree exactly when the coordinates do. -/
@[simp] theorem singletonIdx_inj {N : ℕ} {i i' : Fin N} :
    singletonIdx i = singletonIdx i' ↔ i = i' :=
  ⟨fun h => Finset.singleton_inj.1 (congrArg Subtype.val h), fun h => by rw [h]⟩

/-- The component of a direct sum of monomial sums at an index set, paired with the inclusion of
another. -/
@[reassoc] theorem koszulSum_ι_π {j : ℤ} (t : ℤ) (x y : koszulIndex (m + 1 + 1) j) :
    biproduct.ι (fun _ : koszulIndex (m + 1 + 1) j => monomialSum (m + 1) S t) x ≫
        biproduct.π _ y = if x = y then 𝟙 (monomialSum (m + 1) S t) else 0 := by
  exact biproduct_ι_π_ite _ x y

/-! ### The dual Koszul differential squares to zero -/

/-- **The transposes of multiplication by two coordinates commute**: both composites project
onto the component of the multidegree shifted by both coordinates. -/
theorem monomialSumMul_comp_comm (i k : Fin (m + 1 + 1)) (t t' t'' : ℤ) (h1 : 1 + t' = t)
    (h2 : 1 + t'' = t') :
    monomialSumMul (m + 1) S k t t' h1 ≫ monomialSumMul (m + 1) S i t' t'' h2 =
      monomialSumMul (m + 1) S i t t' h1 ≫ monomialSumMul (m + 1) S k t' t'' h2 := by
  refine biproduct.hom_ext _ _ fun c => ?_
  have hc : MonomialIndex.addOf (coordIndex k) (MonomialIndex.addOf (coordIndex i) c h2) h1 =
      MonomialIndex.addOf (coordIndex i) (MonomialIndex.addOf (coordIndex k) c h2) h1 :=
    Subtype.ext (by simp only [MonomialIndex.addOf_val]; abel)
  simp only [monomialSumMul, Category.assoc, biproduct.lift_π]
  rw [hc]

/-- **The first two dual Koszul differentials compose to zero.** The entry of the composite
from the empty set of coordinates to a two-element set `{k, i}` is the sum over the one-element
sets in between of the products of the entries; only `{k}` and `{i}` contribute, both products
are the transpose of multiplication by `Tₖ Tᵢ`, and the two Koszul signs they carry sum to
zero. -/
theorem dualDiff_comp_dualDiff {t t' t'' : ℤ} (h1 : 1 + t' = t) (h2 : 1 + t'' = t')
    (hj0 : (0 : ℤ) + 1 = 1) (hj1 : (1 : ℤ) + 1 = 2) :
    dualDiff m S 0 1 hj0 h1 ≫ dualDiff m S 1 2 hj1 h2 = 0 := by
  refine biproduct.hom_ext' _ _ fun s => biproduct.hom_ext _ _ fun u => ?_
  rw [comp_zero, zero_comp, biproduct_ι_comp_comp_π,
    Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) =>
      congrArg₂ CategoryStruct.comp (ι_dualDiff_π m S 0 1 hj0 h1 s v)
        (ι_dualDiff_π m S 1 2 hj1 h2 v u)]
  obtain ⟨k, i, hki, hu⟩ := Finset.card_eq_two.1 (show u.1.card = 2 by have := u.2; omega)
  refine Eq.trans (Finset.sum_eq_add_of_mem (singletonIdx k) (singletonIdx i)
    (Finset.mem_univ _) (Finset.mem_univ _) (by simpa using hki) ?_) ?_
  · intro v _ hv
    obtain ⟨l, rfl⟩ := koszulIndex_one_eq v
    have hl : l ∉ u.1 := by
      rw [hu]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact fun hcon => hcon.elim (fun h => hv.1 (by rw [h])) fun h => hv.2 (by rw [h])
    rw [dualCoeff_one_eq_zero m S 2 h2 l u hl, comp_zero]
  · rw [dualCoeff_zero m S 1 h1 s k (singletonIdx k) rfl,
      dualCoeff_zero m S 1 h1 s i (singletonIdx i) rfl,
      dualCoeff_one m S 2 h2 k i (Ne.symm hki) u (by rw [hu, Finset.pair_comm]),
      dualCoeff_one m S 2 h2 i k hki u hu]
    refine Eq.trans ?_ (zsmul_comp_add_zsmul_comp_eq_zero
      (monomialSumMul (m + 1) S k t t' h1) (monomialSumMul (m + 1) S i t t' h1)
      (monomialSumMul (m + 1) S i t' t'' h2) (monomialSumMul (m + 1) S k t' t'' h2)
      (monomialSumMul_comp_comm m S k i t t' t'' h1 h2) 1 (koszulSign i {k}) 1
      (koszulSign k {i}) (by rw [one_mul, one_mul]; exact koszulSign_add_swap (Ne.symm hki)))
    rw [one_zsmul, one_zsmul]

/-! ### The retraction of the first dual differential -/

variable {e t₁ t₂ : ℤ}

/-- **The retraction of the first dual Koszul differential**: the component at a multidegree `c`
of total degree `e` is the projection onto the summand indexed by the chosen coordinate dividing
`c` and the quotient of `c` by it. -/
def dualRetraction (he : 1 ≤ e) (h1 : 1 + t₁ = e) :
    (⨁ fun _ : koszulIndex (m + 1 + 1) 1 => monomialSum (m + 1) S t₁) ⟶
      (⨁ fun _ : koszulIndex (m + 1 + 1) 0 => monomialSum (m + 1) S e) :=
  (biproduct.lift fun c => biproduct.π _ (singletonIdx (splitIdx he c)) ≫
      biproduct.π _ (splitRest he h1 c)) ≫
    biproduct.ι (fun _ : koszulIndex (m + 1 + 1) 0 => monomialSum (m + 1) S e) default

/-- The column of the retraction at a multidegree. -/
theorem dualRetraction_π (he : 1 ≤ e) (h1 : 1 + t₁ = e) (s : koszulIndex (m + 1 + 1) 0)
    (c : MonomialIndex.{u} (m + 1) e) :
    dualRetraction m S he h1 ≫ biproduct.π _ s ≫ biproduct.π _ c =
      biproduct.π _ (singletonIdx (splitIdx he c)) ≫ biproduct.π _ (splitRest he h1 c) := by
  obtain rfl : s = default := Subsingleton.elim _ _
  rw [dualRetraction, Category.assoc, ← Category.assoc (biproduct.ι _ default),
    biproduct.ι_π_self, Category.id_comp, biproduct.lift_π]

/-- The column of the first dual differential at a one-element set of coordinates. -/
@[reassoc] theorem ι_dualDiff_zero_π (h1 : 1 + t₁ = e) (hj : (0 : ℤ) + 1 = 1)
    (s : koszulIndex (m + 1 + 1) 0) (i : Fin (m + 1 + 1)) :
    biproduct.ι _ s ≫ dualDiff m S 0 1 hj h1 ≫ biproduct.π _ (singletonIdx i) =
      monomialSumMul (m + 1) S i e t₁ h1 := by
  rw [ι_dualDiff_π, dualCoeff_zero m S 1 h1 s i (singletonIdx i) rfl]

/-- The column of the second dual differential at a two-element set of coordinates. -/
@[reassoc] theorem ι_dualDiff_one_π (h2 : 1 + t₂ = t₁) (hj : (1 : ℤ) + 1 = 2) (i : Fin (m + 1 + 1))
    (u : koszulIndex (m + 1 + 1) 2) :
    biproduct.ι _ (singletonIdx i) ≫ dualDiff m S 1 2 hj h2 ≫ biproduct.π _ u =
      dualCoeff m S 1 2 h2 (singletonIdx i) u :=
  ι_dualDiff_π m S 1 2 hj h2 (singletonIdx i) u

/-- **The retraction retracts the first dual Koszul differential.** The composite sends the
summand of a multidegree `c` to that of `δₖ` times the quotient of `c` by the chosen coordinate
`k`, which is `c` again. -/
theorem dualDiff_comp_dualRetraction (he : 1 ≤ e) (h1 : 1 + t₁ = e) (hj : (0 : ℤ) + 1 = 1) :
    dualDiff m S 0 1 hj h1 ≫ dualRetraction m S he h1 = 𝟙 _ := by
  refine biproduct.hom_ext _ _ fun s => biproduct.hom_ext _ _ fun c => ?_
  refine biproduct.hom_ext' _ _ fun s' => biproduct.hom_ext' _ _ fun b => ?_
  obtain rfl : s' = s := Subsingleton.elim _ _
  simp only [Category.assoc, Category.id_comp, biproduct.ι_π_self_assoc]
  rw [dualRetraction_π m S he h1 s' c, ι_dualDiff_zero_π_assoc m S h1 hj s' (splitIdx he c),
    monomialSumMul_ι_π m S _ e t₁ h1 b (splitRest he h1 c), splitRest_spec he h1 c,
    monomialSum_ι_π m S e b c]

/-! ### The homotopy -/

/-- **The quotient of `δ_{i'} · c'` by its chosen coordinate has a positive `i'`-th exponent**
when that coordinate is not `i'`: the two factorisations of `δ_{i'} · c'` give that exponent as
one more than the `i'`-th exponent of `c'`. -/
theorem one_le_splitRest_apply (he : 1 ≤ e) (h1 : 1 + t₁ = e) (i' : Fin (m + 1 + 1))
    (c' : MonomialIndex.{u} (m + 1) t₁)
    (h : splitIdx he (MonomialIndex.addOf (coordIndex i') c' h1) ≠ i') :
    1 ≤ (splitRest he h1 (MonomialIndex.addOf (coordIndex i') c' h1)).1 (ULift.up i') := by
  have hval : (MonomialIndex.addOf (coordIndex
        (splitIdx he (MonomialIndex.addOf (coordIndex i') c' h1)))
        (splitRest he h1 (MonomialIndex.addOf (coordIndex i') c' h1)) h1).1 (ULift.up i') =
      (MonomialIndex.addOf (coordIndex i') c' h1).1 (ULift.up i') := by
    rw [splitRest_spec he h1 (MonomialIndex.addOf (coordIndex i') c' h1)]
  rw [addOf_coordIndex_apply_of_ne h _ h1, addOf_coordIndex_apply_self i' c' h1] at hval
  omega

/-- **The column of the homotopy** at a coordinate `i'` and a multidegree `c'`: zero when the
chosen coordinate of `δ_{i'} · c'` is `i'` itself, and otherwise the Koszul sign of that
coordinate in `{i'}` times the projection onto the summand indexed by the pair of the two
coordinates and by the quotient of `c'` by the chosen one. -/
def dualHomotopyEntry (he : 1 ≤ e) (h1 : 1 + t₁ = e) (h2 : 1 + t₂ = t₁)
    (i' : Fin (m + 1 + 1)) (c' : MonomialIndex.{u} (m + 1) t₁) :
    (⨁ fun _ : koszulIndex (m + 1 + 1) 2 => monomialSum (m + 1) S t₂) ⟶ Scheme.unitModule S :=
  if h : splitIdx he (MonomialIndex.addOf (coordIndex i') c' h1) = i' then 0
  else koszulSign (splitIdx he (MonomialIndex.addOf (coordIndex i') c' h1)) {i'} •
    (biproduct.π _ (pairIdx (splitIdx he (MonomialIndex.addOf (coordIndex i') c' h1)) i' h) ≫
      biproduct.π _ (divCoord i' h2
        (splitRest he h1 (MonomialIndex.addOf (coordIndex i') c' h1))
        (one_le_splitRest_apply m he h1 i' c' h)))

/-- **The homotopy** between the identity of the middle term and the composite of the retraction
with the first dual Koszul differential. -/
def dualHomotopy (he : 1 ≤ e) (h1 : 1 + t₁ = e) (h2 : 1 + t₂ = t₁) :
    (⨁ fun _ : koszulIndex (m + 1 + 1) 2 => monomialSum (m + 1) S t₂) ⟶
      (⨁ fun _ : koszulIndex (m + 1 + 1) 1 => monomialSum (m + 1) S t₁) :=
  biproduct.lift fun s' => biproduct.lift fun c' =>
    ∑ i' : Fin (m + 1 + 1), if s'.1 = {i'} then dualHomotopyEntry m S he h1 h2 i' c' else 0

/-- The column of the homotopy at a one-element set of coordinates. -/
@[reassoc] theorem dualHomotopy_π (he : 1 ≤ e) (h1 : 1 + t₁ = e) (h2 : 1 + t₂ = t₁)
    (i' : Fin (m + 1 + 1)) (c' : MonomialIndex.{u} (m + 1) t₁) :
    dualHomotopy m S he h1 h2 ≫ biproduct.π _ (singletonIdx i') ≫ biproduct.π _ c' =
      dualHomotopyEntry m S he h1 h2 i' c' := by
  rw [← Category.assoc, dualHomotopy, biproduct.lift_π, biproduct.lift_π]
  refine Eq.trans (Finset.sum_eq_single i' (fun l _ hl => ?_) (fun hi => ?_)) ?_
  · exact if_neg (fun hcon => hl (Finset.singleton_inj.1 hcon).symm)
  · exact absurd (Finset.mem_univ i') hi
  · exact if_pos rfl

/-- The column of the composite of the retraction with the first dual Koszul differential: it is
the projection onto the summand of the chosen coordinate of `δ_{i'} · c'` and of the quotient
by it. -/
@[reassoc] theorem dualRetraction_comp_dualDiff_zero_π (he : 1 ≤ e) (h1 : 1 + t₁ = e)
    (hj0 : (0 : ℤ) + 1 = 1) (i' : Fin (m + 1 + 1)) (c' : MonomialIndex.{u} (m + 1) t₁) :
    dualRetraction m S he h1 ≫ dualDiff m S 0 1 hj0 h1 ≫
        biproduct.π _ (singletonIdx i') ≫ biproduct.π _ c' =
      biproduct.π _ (singletonIdx (splitIdx he (MonomialIndex.addOf (coordIndex i') c' h1))) ≫
        biproduct.π _ (splitRest he h1 (MonomialIndex.addOf (coordIndex i') c' h1)) := by
  rw [dualRetraction, Category.assoc, ι_dualDiff_zero_π_assoc m S h1 hj0 default i',
    monomialSumMul, biproduct.lift_π, biproduct.lift_π]

/-- **The retraction and the homotopy split the dual Koszul strand.** Write `K` for the chosen
coordinate of `δ_{i'} · c'` and `W` for the quotient of `δ_{i'} · c'` by `K`. The entry of the
first composite from the summand `({i}, b')` to the summand `({i'}, c')` is `1` when `i = K` and
`b' = W` and zero otherwise; the entry of the second is `1` when `i = i'` and `b' = c'`, is `-1`
when `i = K ≠ i'` and `b' = W`, and is zero otherwise; and the two together are the entry of the
identity. -/
theorem dualRetraction_comp_add (he : 1 ≤ e) (h1 : 1 + t₁ = e) (h2 : 1 + t₂ = t₁)
    (hj0 : (0 : ℤ) + 1 = 1) (hj1 : (1 : ℤ) + 1 = 2) :
    dualRetraction m S he h1 ≫ dualDiff m S 0 1 hj0 h1 +
      dualDiff m S 1 2 hj1 h2 ≫ dualHomotopy m S he h1 h2 = 𝟙 _ := by
  refine biproduct.hom_ext _ _ fun sq => biproduct.hom_ext _ _ fun c' => ?_
  obtain ⟨i', rfl⟩ := koszulIndex_one_eq sq
  refine biproduct.hom_ext' _ _ fun sp => biproduct.hom_ext' _ _ fun b' => ?_
  obtain ⟨i, rfl⟩ := koszulIndex_one_eq sp
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, Category.id_comp]
  rw [dualRetraction_comp_dualDiff_zero_π m S he h1 hj0 i' c',
    dualHomotopy_π m S he h1 h2 i' c', dualHomotopyEntry]
  by_cases hK : splitIdx he (MonomialIndex.addOf (coordIndex i') c' h1) = i'
  · have hW : splitRest he h1 (MonomialIndex.addOf (coordIndex i') c' h1) = c' := by
      refine addOf_left_cancel (coordIndex i') (h := h1) ?_
      have hsp := splitRest_spec he h1 (MonomialIndex.addOf (coordIndex i') c' h1)
      rw [hK] at hsp
      exact hsp
    rw [dif_pos hK, hK, hW]
    simp
  · rw [dif_neg hK]
    simp only [Preadditive.comp_zsmul]
    rw [ι_dualDiff_one_π_assoc m S h2 hj1 i
      (pairIdx (splitIdx he (MonomialIndex.addOf (coordIndex i') c' h1)) i' hK)]
    by_cases hii : i = i'
    · subst hii
      have hBc : MonomialIndex.addOf
          (coordIndex (splitIdx he (MonomialIndex.addOf (coordIndex i) c' h1)))
          (divCoord i h2 (splitRest he h1 (MonomialIndex.addOf (coordIndex i) c' h1))
            (one_le_splitRest_apply m he h1 i c' hK)) h2 = c' := by
        refine addOf_left_cancel (coordIndex i) (h := h1) (Subtype.ext ?_)
        have h3 := congrArg Subtype.val
          (splitRest_spec he h1 (MonomialIndex.addOf (coordIndex i) c' h1))
        have h4 := congrArg Subtype.val (divCoord_spec i h2
          (splitRest he h1 (MonomialIndex.addOf (coordIndex i) c' h1))
          (one_le_splitRest_apply m he h1 i c' hK))
        simp only [MonomialIndex.addOf_val] at h3 h4 ⊢
        rw [← h4] at h3
        rw [← h3]
        abel
      rw [dualCoeff_one m S 2 h2 i _ hK _ (pairIdx_val _ _ hK), Preadditive.zsmul_comp,
        Preadditive.comp_zsmul, smul_smul, koszulSign_mul_self, one_zsmul,
        monomialSumMul_ι_π m S _ t₁ t₂ h2 b' _, hBc,
        biproduct.ι_π_ne_assoc _ (fun hcon => hK (singletonIdx_inj.1 hcon).symm),
        biproduct.ι_π_self_assoc, monomialSum_ι_π m S t₁ b' c']
      simp
    · by_cases hiK : i = splitIdx he (MonomialIndex.addOf (coordIndex i') c' h1)
      · have hpair : (pairIdx (splitIdx he (MonomialIndex.addOf (coordIndex i') c' h1)) i'
            hK).1 = {i', i} := by rw [pairIdx_val, ← hiK, Finset.pair_comm]
        have hBW : MonomialIndex.addOf (coordIndex i')
            (divCoord i' h2 (splitRest he h1 (MonomialIndex.addOf (coordIndex i') c' h1))
              (one_le_splitRest_apply m he h1 i' c' hK)) h2 =
            splitRest he h1 (MonomialIndex.addOf (coordIndex i') c' h1) :=
          divCoord_spec i' h2 _ _
        rw [dualCoeff_one m S 2 h2 i i' (fun hcon => hii hcon.symm) _ hpair,
          Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← hiK,
          koszulSign_mul_swap (fun hcon => hii hcon),
          monomialSumMul_ι_π m S _ t₁ t₂ h2 b' _, hBW, biproduct.ι_π_self_assoc,
          biproduct.ι_π_ne_assoc _ (fun hcon => hii (singletonIdx_inj.1 hcon)),
          monomialSum_ι_π m S t₁ b' _]
        split_ifs <;> simp
      · have hnot : i ∉ (pairIdx (splitIdx he (MonomialIndex.addOf (coordIndex i') c' h1)) i'
            hK).1 := by
          rw [pairIdx_val]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact fun hcon => hcon.elim hiK hii
        rw [dualCoeff_one_eq_zero m S 2 h2 i _ hnot,
          biproduct.ι_π_ne_assoc _ (fun hcon => hiK (singletonIdx_inj.1 hcon)),
          biproduct.ι_π_ne_assoc _ (fun hcon => hii (singletonIdx_inj.1 hcon))]
        simp

/-- **The first dual Koszul differential is a kernel of the second**: the retraction and the
homotopy split the pair, and a split pair is a kernel. -/
def isLimit_dualDiff (he : 1 ≤ e) (h1 : 1 + t₁ = e) (h2 : 1 + t₂ = t₁)
    (hj0 : (0 : ℤ) + 1 = 1) (hj1 : (1 : ℤ) + 1 = 2)
    (w : dualDiff m S 0 1 hj0 h1 ≫ dualDiff m S 1 2 hj1 h2 = 0) :
    IsLimit (KernelFork.ofι (dualDiff m S 0 1 hj0 h1) w) :=
  isLimit_kernelFork_of_split _ _ w (dualRetraction m S he h1) (dualHomotopy m S he h1 h2)
    (dualDiff_comp_dualRetraction m S he h1 hj0) (dualRetraction_comp_add m S he h1 h2 hj0 hj1)

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
