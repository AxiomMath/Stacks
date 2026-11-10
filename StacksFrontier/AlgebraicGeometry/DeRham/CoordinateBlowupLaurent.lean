module

public import StacksFrontier.Algebra.Homology.CechFinsuppHomotopy
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupChartIntersections
public import StacksFrontier.RingTheory.MvPolynomial.LaurentCoefficients

/-!
# The chart fractions of the coordinate blowup, as Laurent polynomials

In the situation of `StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupChartIntersections`,
the functions on `D(y₁ ⋯ y_n) ⊆ X = Spec R[x₁, …, x_m, y₁, …, y_n]` are the Laurent polynomials
in which the `y_j` may occur with negative exponents. This file makes that identification and
computes, in Laurent terms, the fractions describing the sections of `𝒪_L(iE)` over an
intersection of charts: they are exactly the Laurent polynomials whose monomials have
nonnegative exponents in the `x`'s and in the `y`'s not selected by the tuple, and total degree at
least `-i` in the `y`'s. This is the shape `Stacks.CechFinsupp.supported` describes, with the set
of indices a monomial needs being the set of `y`'s it has a negative exponent in.

## Main definitions

* `Stacks.DeRham.CoordinateCech.laurent`: the embedding of the functions on `D(y₁ ⋯ y_n)` into
  Laurent polynomials.
* `Stacks.DeRham.CoordinateCech.twistOk`, `Stacks.DeRham.CoordinateCech.negSet`: the allowed
  Laurent exponents and the coordinates in which an exponent is negative.

## Main results

* `Stacks.DeRham.CoordinateCech.laurent_injective`.
* `Stacks.DeRham.CoordinateCech.coeff_laurent_mem_supported` and
  `Stacks.DeRham.CoordinateCech.exists_laurent_eq`: **the twisted chart fractions of a tuple are
  exactly the Laurent polynomials supported on the range of the tuple.**
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial

universe u

namespace Stacks.DeRham.CoordinateCech

open Stacks.LaurentCoeff Stacks.PartialLaurent

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The Laurent exponent of the variable `y_k`. -/
abbrev yExp (k : Fin n) : (Fin m ⊕ Fin n) →₀ ℤ := Finsupp.single (Sum.inr k) 1

/-- Reading a global function on `X` as a Laurent polynomial. -/
def polyLaurent : Γ(coordinateAmbient R m n, ⊤) →+* AddMonoidAlgebra R ((Fin m ⊕ Fin n) →₀ ℤ) :=
  (toLaurent R).comp (Stacks.MoreMorphisms.gammaEquiv R m n).symm.toRingHom

/-- The coordinate `y_k` is the Laurent monomial with exponent `yExp m n k`. -/
theorem polyLaurent_coord (k : Fin n) :
    polyLaurent R m n (coord R m n k) = AddMonoidAlgebra.single (yExp m n k) 1 := by
  simp [polyLaurent, coord, Stacks.MoreMorphisms.coordinateSection, toLaurent_X]

/-- Reading a global function on `X` as a Laurent polynomial is injective. -/
theorem polyLaurent_injective : Function.Injective (polyLaurent R m n) :=
  toLaurent_injective.comp (Stacks.MoreMorphisms.gammaEquiv R m n).symm.injective

/-- The product `y₁ ⋯ y_n` is a unit in the Laurent polynomials. -/
theorem isUnit_polyLaurent_coordProd : IsUnit (polyLaurent R m n (coordProd R m n)) := by
  rw [coordProd, map_prod]
  exact IsUnit.prod_univ_iff.2 fun k => by rw [polyLaurent_coord]; exact isUnit_single _

/-- The functions on `D(y₁ ⋯ y_n)` are the localization of the global functions on `X` away from
`y₁ ⋯ y_n`. -/
instance : IsLocalization.Away (coordProd R m n) (Frac R m n) :=
  (isAffineOpen_top (coordinateAmbient R m n)).isLocalization_basicOpen (coordProd R m n)

/-- **The functions on `D(y₁ ⋯ y_n)`, as Laurent polynomials.** -/
def laurent : Frac R m n →+* AddMonoidAlgebra R ((Fin m ⊕ Fin n) →₀ ℤ) :=
  IsLocalization.Away.lift (coordProd R m n) (isUnit_polyLaurent_coordProd R m n)

/-- On the restriction of a global function, `laurent` agrees with `polyLaurent`. -/
theorem laurent_toFrac (a : Γ(coordinateAmbient R m n, ⊤)) :
    laurent R m n (toFrac R m n a) = polyLaurent R m n a :=
  IsLocalization.Away.lift_eq (coordProd R m n) (isUnit_polyLaurent_coordProd R m n) a

/-- The embedding of the functions on `D(y₁ ⋯ y_n)` into Laurent polynomials is injective. -/
theorem laurent_injective : Function.Injective (laurent R m n) := by
  refine (IsLocalization.lift_injective_iff _).2 fun a b => ?_
  change toFrac R m n a = toFrac R m n b ↔ _
  exact ⟨fun h => by rw [toFrac_injective R m n h], fun h =>
    by rw [polyLaurent_injective R m n h]⟩

/-- The restriction of the coordinate `y_k` is the Laurent monomial with exponent `yExp m n k`. -/
theorem laurent_toFrac_coord (k : Fin n) :
    laurent R m n (toFrac R m n (coord R m n k)) = AddMonoidAlgebra.single (yExp m n k) 1 := by
  rw [laurent_toFrac, polyLaurent_coord]

/-! ### The supported Laurent polynomials -/

/-- The total degree in the `y`'s of a Laurent exponent. -/
def yDegree (w : (Fin m ⊕ Fin n) →₀ ℤ) : ℤ := ∑ k, w (Sum.inr k)

/-- **The allowed Laurent exponents for `𝒪_L(iE)`**: nonnegative in the `x`'s, and of total degree
at least `-i` in the `y`'s. -/
def twistOk (i : ℕ) : Set ((Fin m ⊕ Fin n) →₀ ℤ) :=
  {w | (∀ s, 0 ≤ w (Sum.inl s)) ∧ -(i : ℤ) ≤ yDegree m n w}

/-- The coordinates `y_k` in which a Laurent exponent is negative. -/
def negSet (w : (Fin m ⊕ Fin n) →₀ ℤ) : Set (ULift.{u} (Fin n)) :=
  {k | w (Sum.inr k.down) < 0}

/-- An allowed exponent for `i < n` is nonnegative in at least one coordinate `y_k`. -/
theorem exists_not_mem_negSet {i : ℕ} (hi : i < n) {w} (hw : w ∈ twistOk m n i) :
    ∃ k, k ∉ negSet.{u} m n w := by
  by_contra h
  push Not at h
  have hneg : ∀ k : Fin n, w (Sum.inr k) ≤ -1 := fun k => by
    have := h ⟨k⟩
    simp only [negSet, Set.mem_ofPred_eq] at this
    omega
  have hsum : yDegree m n w ≤ ∑ _k : Fin n, (-1 : ℤ) := Finset.sum_le_sum fun k _ => hneg k
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg,
    mul_one] at hsum
  have := hw.2
  omega

/-! ### Exponent bookkeeping -/

/-- The total degree in the `y`'s, as an additive map. -/
def yDegreeHom : ((Fin m ⊕ Fin n) →₀ ℤ) →+ ℤ where
  toFun := yDegree m n
  map_zero' := by simp [yDegree]
  map_add' a b := by simp [yDegree, Finset.sum_add_distrib]

/-- The exponent of `y_k` has total degree `1` in the `y`'s. -/
theorem yDegree_yExp (k : Fin n) : yDegree m n (yExp m n k) = 1 := by
  classical
  rw [yDegree, Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    simp [hk'.symm]
  · simp

/-- The exponent of the product of the coordinates selected by a tuple. -/
def tupleExp {p : ℕ} (x : Fin (p + 1) → Fin n) : (Fin m ⊕ Fin n) →₀ ℤ := ∑ k, yExp m n (x k)

/-- The exponent of the product of the coordinates selected by a tuple vanishes in each `x`. -/
theorem tupleExp_inl {p : ℕ} (x : Fin (p + 1) → Fin n) (s : Fin m) :
    tupleExp m n x (Sum.inl s) = 0 := by
  simp [tupleExp, Finsupp.finsetSum_apply]

/-- The exponent of the product of the coordinates selected by a tuple vanishes in each `y_k` with
`k` outside the range of the tuple. -/
theorem tupleExp_inr_of_not_mem {p : ℕ} (x : Fin (p + 1) → Fin n) {k' : Fin n}
    (hk' : k' ∉ Set.range x) : tupleExp m n x (Sum.inr k') = 0 := by
  rw [tupleExp, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finsupp.single_apply, ite_eq_right]
  intro h
  exact hk' ⟨k, Sum.inr_injective h⟩

/-- The exponent of the product of the coordinates selected by a tuple is at least `1` in each
selected `y_k`. -/
theorem one_le_tupleExp_of_mem {p : ℕ} (x : Fin (p + 1) → Fin n) (k : Fin (p + 1)) :
    1 ≤ tupleExp m n x (Sum.inr (x k)) := by
  rw [tupleExp, Finsupp.finsetSum_apply]
  calc (1 : ℤ) = yExp m n (x k) (Sum.inr (x k)) := by simp
    _ ≤ ∑ k', yExp m n (x k') (Sum.inr (x k)) :=
      Finset.single_le_sum (f := fun k' => yExp m n (x k') (Sum.inr (x k)))
        (fun k' _ => by rw [Finsupp.single_apply]; split_ifs <;> simp) (Finset.mem_univ k)

/-- The exponent of the product of the coordinates selected by a tuple is nonnegative. -/
theorem tupleExp_nonneg {p : ℕ} (x : Fin (p + 1) → Fin n) (v : Fin m ⊕ Fin n) :
    0 ≤ tupleExp m n x v := by
  rw [tupleExp, Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun k _ => by rw [Finsupp.single_apply]; split_ifs <;> simp

/-- The product of the coordinates selected by a tuple of length `p + 1` has total degree `p + 1`
in the `y`'s. -/
theorem yDegree_tupleExp {p : ℕ} (x : Fin (p + 1) → Fin n) :
    yDegree m n (tupleExp m n x) = p + 1 := by
  change yDegreeHom m n (tupleExp m n x) = _
  rw [tupleExp, map_sum]
  change ∑ k, yDegree m n (yExp m n (x k)) = _
  simp [yDegree_yExp]

/-- The restriction of the product of the coordinates selected by a tuple is the Laurent monomial
with exponent `tupleExp m n x`. -/
theorem laurent_toFrac_tupleCoord {p : ℕ} (x : Fin (p + 1) → Fin n) :
    laurent R m n (toFrac R m n (tupleCoord R m n x)) =
      AddMonoidAlgebra.single (tupleExp m n x) 1 := by
  rw [laurent_toFrac, tupleCoord, map_prod]
  simp_rw [polyLaurent_coord]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  rfl

/-- The `y`-degree of a polynomial exponent is its partial degree in the `y`'s. -/
theorem yDegree_natToInt (β : (Fin m ⊕ Fin n) →₀ ℕ) :
    yDegree m n (natToInt β) = (partialDegree (Sum.inr : Fin n → Fin m ⊕ Fin n) β : ℤ) := by
  simp [yDegree, partialDegree, natToInt]

/-- The ideal of the centre, read in the polynomial ring. -/
theorem mem_pow_iff {N : ℕ} (a : Γ(coordinateAmbient R m n, ⊤)) :
    a ∈ (Stacks.MoreMorphisms.coordinateIdeal R m n).ideal
        (Stacks.MoreMorphisms.topAffineOpen R m n) ^ N ↔
      (Stacks.MoreMorphisms.gammaEquiv R m n).symm a ∈
        Ideal.span (Set.range fun j : Fin n => (X (Sum.inr j) : MvPolynomial (Fin m ⊕ Fin n) R))
          ^ N := by
  rw [Stacks.MoreMorphisms.coordinateIdeal_ideal_top, ← Ideal.map_pow,
    Ideal.map_comap_of_equiv, Ideal.mem_comap]
  rfl

/-! ### Twisted chart fractions are supported Laurent polynomials -/

/-- The restriction of `y_j ^ a * y_j ^ b * y_x ^ r` is the corresponding Laurent monomial. -/
private theorem laurent_toFrac_coord_pow_mul {p : ℕ} (a b r : ℕ) (j : Fin n)
    (x : Fin (p + 1) → Fin n) :
    laurent R m n (toFrac R m n (coord R m n j) ^ a * toFrac R m n (coord R m n j) ^ b *
        toFrac R m n (tupleCoord R m n x) ^ r) =
      AddMonoidAlgebra.single (a • yExp m n j + b • yExp m n j + r • tupleExp m n x) 1 := by
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, laurent_toFrac_coord,
    laurent_toFrac_tupleCoord, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.single_pow, one_pow, one_pow, one_pow,
    AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, one_mul, one_mul]

/-- The `y`-degree of the twist exponents `u - v` (see `coeff_laurent_mem_supported`) shifts the
`y`-degree of `w` by `i + N`. -/
private theorem yDegree_add_twist_sub {p : ℕ} (w : (Fin m ⊕ Fin n) →₀ ℤ) (i N r : ℕ) (j : Fin n)
    (x : Fin (p + 1) → Fin n) :
    yDegree m n (w + ((i • yExp m n j + N • yExp m n j + r • tupleExp m n x) -
      (r * (p + 1)) • yExp m n j)) = yDegree m n w + i + N := by
  change yDegreeHom m n _ = _
  simp only [map_add, map_sub, map_nsmul]
  change yDegree m n w + (i • yDegree m n (yExp m n j) + N • yDegree m n (yExp m n j) +
    r • yDegree m n (tupleExp m n x) - (r * (p + 1)) • yDegree m n (yExp m n j)) = _
  rw [yDegree_yExp, yDegree_tupleExp]
  simp only [nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- **A twisted chart fraction of a tuple is supported on the range of the tuple.** -/
theorem coeff_laurent_mem_supported (i : ℕ) {p : ℕ} (x : Fin (p + 1) → Fin n)
    {h : Frac R m n} (hh : IsChartFraction R m n x (h * toFrac R m n (coord R m n (x 0)) ^ i)) :
    (laurent R m n h).coeff ∈
      Stacks.CechFinsupp.supported (twistOk m n i) (negSet.{u} m n)
        (Set.range (ULift.up ∘ x)) := by
  classical
  obtain ⟨N, r, a, ha, hf⟩ := hh
  set j := x 0
  set u : (Fin m ⊕ Fin n) →₀ ℤ := i • yExp m n j + N • yExp m n j + r • tupleExp m n x
  set v : (Fin m ⊕ Fin n) →₀ ℤ := (r * (p + 1)) • yExp m n j
  have hΛ : laurent R m n h * AddMonoidAlgebra.single u 1 =
      polyLaurent R m n a * AddMonoidAlgebra.single v 1 := by
    have hf' : h * (toFrac R m n (coord R m n j) ^ i * toFrac R m n (coord R m n j) ^ N *
        toFrac R m n (tupleCoord R m n x) ^ r) =
        toFrac R m n a * toFrac R m n (coord R m n j) ^ (r * (p + 1)) := by rw [← hf]; ring
    rw [← laurent_toFrac_coord_pow_mul R m n i N r j x, ← map_mul, hf', map_mul, laurent_toFrac,
      map_pow, laurent_toFrac_coord, AddMonoidAlgebra.single_pow, one_pow]
  have hh' : laurent R m n h = polyLaurent R m n a * AddMonoidAlgebra.single (v - u) 1 := by
    have h2 := congrArg (· * AddMonoidAlgebra.single (-u) (1 : R)) hΛ
    simp only [mul_assoc, AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul] at h2
    rw [← sub_eq_add_neg] at h2
    rw [← h2]
    exact (mul_one _).symm
  rw [Stacks.CechFinsupp.mem_supported]
  intro w hw
  rw [hh', Finsupp.mem_support_iff, AddMonoidAlgebra.coeff_mul_single_apply, mul_one] at hw
  obtain ⟨β, hβ, hβw⟩ := exists_eq_natToInt_of_mem_support _ (Finsupp.mem_support_iff.2 hw)
  have hβN := le_partialDegree_of_mem_pow (Sum.inr : Fin n → Fin m ⊕ Fin n)
    ((mem_pow_iff R m n a).1 ha) β hβ
  have hw' : w = natToInt β + (v - u) := by rw [← hβw]; abel
  refine ⟨⟨fun s => ?_, ?_⟩, fun k hk => ?_⟩
  · rw [hw']
    simp [u, v, natToInt, tupleExp_inl]
  · have hd := yDegree_add_twist_sub m n w i N r j x
    rw [show w + (u - v) = natToInt β by rw [hw']; abel, yDegree_natToInt] at hd
    omega
  · simp only [negSet, Set.mem_ofPred_eq] at hk
    by_contra hkx
    have hkx' : k.down ∉ Set.range x := fun ⟨l, hl⟩ => hkx ⟨l, by simp [hl]⟩
    have hj : k.down ≠ j := fun h => hkx' ⟨0, h.symm⟩
    rw [hw'] at hk
    simp [u, v, natToInt, tupleExp_inr_of_not_mem m n x hkx', hj.symm]
      at hk
    omega

/-- A Laurent monomial with nonnegative exponents comes from a monomial. -/
theorem natToInt_toNat {w : (Fin m ⊕ Fin n) →₀ ℤ} (hw : ∀ s, 0 ≤ w s) :
    natToInt (Finsupp.mapRange Int.toNat (by simp) w) = w := by
  ext s
  simp [Int.toNat_of_nonneg (hw s)]

/-- **Every Laurent polynomial supported on the range of a tuple is a twisted chart fraction of
it.** -/
theorem exists_laurent_eq (i : ℕ) {p : ℕ} (x : Fin (p + 1) → Fin n)
    (g : ((Fin m ⊕ Fin n) →₀ ℤ) →₀ R)
    (hg : g ∈ Stacks.CechFinsupp.supported (twistOk m n i) (negSet.{u} m n)
      (Set.range (ULift.up ∘ x))) :
    ∃ h : Frac R m n, (laurent R m n h).coeff = g ∧
      IsChartFraction R m n x (h * toFrac R m n (coord R m n (x 0)) ^ i) := by
  classical
  rw [Stacks.CechFinsupp.mem_supported] at hg
  set j := x 0
  set r : ℕ := ∑ w ∈ g.support, ∑ k : Fin n, (w (Sum.inr k)).natAbs
  have hr : ∀ w ∈ g.support, ∀ k : Fin n, -(r : ℤ) ≤ w (Sum.inr k) := fun w hw k => by
    have h1 : (w (Sum.inr k)).natAbs ≤ ∑ k : Fin n, (w (Sum.inr k)).natAbs :=
      Finset.single_le_sum (f := fun k => (w (Sum.inr k)).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    have h2 : ∑ k : Fin n, (w (Sum.inr k)).natAbs ≤ r :=
      Finset.single_le_sum (f := fun w => ∑ k : Fin n, (w (Sum.inr k)).natAbs)
        (fun _ _ => Nat.zero_le _) hw
    omega
  set N : ℕ := r * (p + 1) + r
  set u : (Fin m ⊕ Fin n) →₀ ℤ := i • yExp m n j + N • yExp m n j + r • tupleExp m n x
  set v : (Fin m ⊕ Fin n) →₀ ℤ := (r * (p + 1)) • yExp m n j
  have hu : ∀ s, u s = (i : ℤ) * yExp m n j s + (N : ℤ) * yExp m n j s +
      (r : ℤ) * tupleExp m n x s := fun s => by
    simp only [u, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
  have hv : ∀ s, v s = ((r * (p + 1) : ℕ) : ℤ) * yExp m n j s := fun s => by
    simp only [v, Finsupp.smul_apply, nsmul_eq_mul]
  have hnonneg : ∀ w ∈ g.support, ∀ s, 0 ≤ (w + (u - v)) s := fun w hw s => by
    obtain ⟨⟨hinl, -⟩, hneg⟩ := hg w hw
    rcases s with s | k
    · rw [Finsupp.add_apply, Finsupp.sub_apply, hu, hv, tupleExp_inl]
      simpa [yExp] using hinl s
    · by_cases hkx : k ∈ Set.range x
      · by_cases hkj : k = j
        · subst hkj
          have h1 : 1 ≤ tupleExp m n x (Sum.inr j) := one_le_tupleExp_of_mem m n x 0
          have h2 : -(r : ℤ) ≤ w (Sum.inr j) := hr w hw (x 0)
          have h3 : (r : ℤ) ≤ r * tupleExp m n x (Sum.inr j) := by nlinarith
          have hN : (N : ℤ) = r * (p + 1) + r := by simp only [N]; push_cast; ring
          rw [Finsupp.add_apply, Finsupp.sub_apply, hu, hv]
          simp only [yExp, Finsupp.single_eq_same, mul_one]
          push_cast
          nlinarith
        · obtain ⟨l, rfl⟩ := hkx
          have h1 := one_le_tupleExp_of_mem m n x l
          have h2 := hr w hw (x l)
          have h3 : (r : ℤ) ≤ r * tupleExp m n x (Sum.inr (x l)) := by nlinarith
          have hz : yExp m n j (Sum.inr (x l)) = 0 := by
            simp [Ne.symm hkj]
          rw [Finsupp.add_apply, Finsupp.sub_apply, hu, hv, hz]
          push_cast
          nlinarith
      · have hw0 : 0 ≤ w (Sum.inr k) := by
          by_contra hlt
          have := hneg (show (⟨k⟩ : ULift.{u} (Fin n)) ∈ negSet.{u} m n w by
            simp only [negSet, Set.mem_ofPred_eq]; omega)
          obtain ⟨l, hl⟩ := this
          exact hkx ⟨l, by simpa using congrArg ULift.down hl⟩
        have hkj : k ≠ j := fun h => hkx ⟨0, h.symm⟩
        have hz : yExp m n j (Sum.inr k) = 0 := by simp [Ne.symm hkj]
        rw [Finsupp.add_apply, Finsupp.sub_apply, hu, hv, hz, tupleExp_inr_of_not_mem m n x hkx]
        simpa using hw0
  set β : ((Fin m ⊕ Fin n) →₀ ℤ) → ((Fin m ⊕ Fin n) →₀ ℕ) :=
    fun w => Finsupp.mapRange Int.toNat (by simp) (w + (u - v))
  set a0 : MvPolynomial (Fin m ⊕ Fin n) R := ∑ w ∈ g.support, monomial (β w) (g w)
  set a : Γ(coordinateAmbient R m n, ⊤) := Stacks.MoreMorphisms.gammaEquiv R m n a0
  have hpa :
      polyLaurent R m n a = AddMonoidAlgebra.ofCoeff g * AddMonoidAlgebra.single (u - v) 1 := by
    have hsum : polyLaurent R m n a =
        ∑ w ∈ g.support, AddMonoidAlgebra.single (w + (u - v)) (g w) := by
      simp only [polyLaurent, RingHom.comp_apply, a, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, a0, map_sum, toLaurent_monomial]
      exact Finset.sum_congr rfl fun w hw => by
        simp only [β]
        rw [natToInt_toNat m n (hnonneg w hw)]
    rw [hsum]
    conv_rhs => rw [← AddMonoidAlgebra.ofCoeff_coeff (AddMonoidAlgebra.ofCoeff g),
      AddMonoidAlgebra.coeff_ofCoeff, ← Finsupp.sum_single g, Finsupp.sum,
      AddMonoidAlgebra.ofCoeff_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    change _ = AddMonoidAlgebra.single w (g w) * _
    rw [AddMonoidAlgebra.single_mul_single, mul_one]
  have ha : a ∈ (Stacks.MoreMorphisms.coordinateIdeal R m n).ideal
      (Stacks.MoreMorphisms.topAffineOpen R m n) ^ N := by
    rw [mem_pow_iff, RingEquiv.symm_apply_apply]
    refine Ideal.sum_mem _ fun w hw => monomial_mem_pow _ Sum.inr_injective _ ?_ _
    have hdeg := (hg w hw).1.2
    have h1 : yDegree m n (w + (u - v)) = (partialDegree Sum.inr (β w) : ℤ) := by
      rw [← yDegree_natToInt]
      exact congrArg (yDegree m n) (natToInt_toNat m n (hnonneg w hw)).symm
    have h2 := yDegree_add_twist_sub m n w i N r j x
    rw [h2] at h1
    omega
  have hU : IsUnit (toFrac R m n (coord R m n j) ^ i * toFrac R m n (coord R m n j) ^ N *
      toFrac R m n (tupleCoord R m n x) ^ r) :=
    (((isUnit_toFrac_coord R m n j).pow i).mul ((isUnit_toFrac_coord R m n j).pow N)).mul
      ((isUnit_toFrac_tupleCoord R m n x).pow r)
  have hlU := laurent_toFrac_coord_pow_mul R m n i N r j x
  have hlUinv : laurent R m n (↑hU.unit⁻¹ : Frac R m n) = AddMonoidAlgebra.single (-u) 1 := by
    have h1 : laurent R m n (↑hU.unit⁻¹ : Frac R m n) * AddMonoidAlgebra.single u 1 = 1 := by
      rw [← hlU, ← map_mul, hU.val_inv_mul, map_one]
    exact left_inv_eq_right_inv h1 (by
      rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul, ← AddMonoidAlgebra.one_def])
  refine ⟨toFrac R m n a * toFrac R m n (coord R m n j) ^ (r * (p + 1)) * ↑hU.unit⁻¹, ?_,
    N, r, a, ha, ?_⟩
  · rw [map_mul, map_mul, hlUinv, laurent_toFrac, hpa, map_pow, laurent_toFrac_coord,
      AddMonoidAlgebra.single_pow, one_pow, mul_assoc, mul_assoc,
      AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, one_mul, one_mul]
    have : u - v + ((r * (p + 1)) • yExp m n j + -u) = 0 := by simp only [v]; abel
    rw [this, ← AddMonoidAlgebra.one_def, mul_one]
  · calc toFrac R m n a * toFrac R m n (coord R m n j) ^ (r * (p + 1)) * ↑hU.unit⁻¹ *
          toFrac R m n (coord R m n j) ^ i * toFrac R m n (coord R m n j) ^ N *
          toFrac R m n (tupleCoord R m n x) ^ r
        = toFrac R m n a * toFrac R m n (coord R m n j) ^ (r * (p + 1)) *
            (↑hU.unit⁻¹ * (toFrac R m n (coord R m n j) ^ i *
              toFrac R m n (coord R m n j) ^ N * toFrac R m n (tupleCoord R m n x) ^ r)) := by
          ring
      _ = toFrac R m n a * toFrac R m n (coord R m n j) ^ (r * (p + 1)) := by
          rw [hU.val_inv_mul, mul_one]

end Stacks.DeRham.CoordinateCech

end
