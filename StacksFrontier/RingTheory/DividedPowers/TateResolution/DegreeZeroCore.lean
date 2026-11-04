module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic

/-! # A commutative algebra as a graded divided power algebra in degree zero

A commutative `R`-algebra `P` is a nonnegatively graded algebra with `P` in degree zero and
nothing in positive degree. The grading is trivially strictly graded commutative, its positive
even part is the zero submodule, and it therefore carries exactly one divided power structure.

## Main definitions

* `DividedPowers.TateResolution.degreeZeroGrade` — the grading concentrated in degree zero.
* `DividedPowers.TateResolution.degreeZeroDpow` and
  `DividedPowers.TateResolution.degreeZeroDividedPowers` — the divided powers on the (zero)
  positive even part of that grading.

## Main results

* `DividedPowers.TateResolution.positiveEvenPart_degreeZeroGrade` — the positive even part is
  zero, which is what makes every divided power axiom degenerate, and
  `DividedPowers.TateResolution.evenPart_degreeZeroGrade` — the even part is everything.
* `DividedPowers.TateResolution.degreeZeroDividedPowers_unique` — the divided power structure is
  the only one.

## Implementation notes

The grading is defined by pattern matching on `0` and `n + 1` rather than with an `if`, so that
both of its values hold by `rfl`. Its decomposition places an element in degree zero; the
inverse direction is an induction over the direct sum, where a summand in a positive degree is a
summand of `⊥` and therefore zero.

The divided power operation is `fun n x => if n = 0 ∧ x = 0 then 1 else 0`. It cannot simply be
zero: the positive even part is `{0}` rather than empty, and `dpow_zero` demands
`γ.dpow 0 0 = 1`. Every other axiom is then either an instance of `dpow_null`, because its
hypothesis forces the argument out of the positive even part, or a computation with the two
values `γ.dpow 0 0 = 1` and `γ.dpow (n + 1) 0 = 0`. Uniqueness is recorded as a separate result
since the structure is data.

## References

* [Stacks Project, Tag 09PG](https://stacks.math.columbia.edu/tag/09PG)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

open scoped DirectSum

variable (R : Type u) (P : Type v) [CommRing R] [CommRing P] [Algebra R P]

/-- The grading of a commutative algebra concentrated in degree zero. -/
public def degreeZeroGrade : ℕ → Submodule R P
  | 0 => ⊤
  | _ + 1 => ⊥

/-- The degree-zero piece of `degreeZeroGrade R P` is all of `P`. -/
@[simp]
public theorem degreeZeroGrade_zero : degreeZeroGrade R P 0 = ⊤ := rfl

/-- Every positive-degree piece of `degreeZeroGrade R P` is zero. -/
@[simp]
public theorem degreeZeroGrade_succ (n : ℕ) : degreeZeroGrade R P (n + 1) = ⊥ := rfl

/-- Every element is homogeneous of degree zero. -/
public theorem mem_degreeZeroGrade_zero (x : P) : x ∈ degreeZeroGrade R P 0 :=
  Submodule.mem_top

/-- There is nothing in positive degree. -/
public theorem degreeZeroGrade_eq_bot {n : ℕ} (hn : n ≠ 0) : degreeZeroGrade R P n = ⊥ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rfl

/-- A homogeneous element of positive degree is zero. -/
public theorem eq_zero_of_mem_degreeZeroGrade {n : ℕ} (hn : n ≠ 0) {x : P}
    (hx : x ∈ degreeZeroGrade R P n) : x = 0 := by
  rw [degreeZeroGrade_eq_bot R P hn] at hx
  exact hx

/-- The grading concentrated in degree zero is a graded monoid. -/
public instance instGradedMonoidDegreeZeroGrade :
    SetLike.GradedMonoid (degreeZeroGrade R P) where
  one_mem := mem_degreeZeroGrade_zero R P 1
  mul_mem := by
    intro i j x y hx hy
    rcases i with _ | i
    · rcases j with _ | j
      · exact mem_degreeZeroGrade_zero R P _
      · rw [eq_zero_of_mem_degreeZeroGrade R P (Nat.succ_ne_zero j) hy, mul_zero]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_mem_degreeZeroGrade R P (Nat.succ_ne_zero i) hx, zero_mul]
      exact Submodule.zero_mem _

/-- The decomposition of a degree-zero-concentrated algebra: place the element in degree
zero. -/
public noncomputable def degreeZeroDecompose :
    P →+ ⨁ n, degreeZeroGrade R P n :=
  (DirectSum.of (fun n => (degreeZeroGrade R P n : Submodule R P)) 0).comp
    (AddMonoidHom.mk' (fun x : P => (⟨x, mem_degreeZeroGrade_zero R P x⟩ :
      degreeZeroGrade R P 0)) fun _ _ => rfl)

/-- The grading concentrated in degree zero is a graded algebra, each element placed in
degree zero. -/
public noncomputable instance instGradedAlgebraDegreeZeroGrade :
    GradedAlgebra (degreeZeroGrade R P) where
  __ := instGradedMonoidDegreeZeroGrade R P
  __ := DirectSum.Decomposition.ofAddHom (degreeZeroGrade R P) (degreeZeroDecompose R P)
    (AddMonoidHom.ext fun _ => DirectSum.coeAddMonoidHom_of (degreeZeroGrade R P) 0 _)
    (by
      apply DirectSum.addHom_ext
      intro n x
      rcases n with _ | n
      · rw [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
        rfl
      · obtain rfl : x = 0 := Subtype.ext (eq_zero_of_mem_degreeZeroGrade R P n.succ_ne_zero x.2)
        rw [map_zero, map_zero, map_zero])

/-- The grading concentrated in degree zero is strictly graded commutative. -/
public instance instIsStrictlyGradedCommDegreeZeroGrade :
    IsStrictlyGradedComm (degreeZeroGrade R P) where
  graded_comm := by
    intro i j x y hx hy
    rcases i with _ | i
    · rcases j with _ | j
      · rw [Nat.mul_zero, pow_zero, one_smul, mul_comm]
      · rw [eq_zero_of_mem_degreeZeroGrade R P (Nat.succ_ne_zero j) hy]
        simp
    · rw [eq_zero_of_mem_degreeZeroGrade R P (Nat.succ_ne_zero i) hx]
      simp
  odd_sq_zero := by
    intro d x hx
    rw [eq_zero_of_mem_degreeZeroGrade R P (Nat.succ_ne_zero (2 * d)) hx]
    simp

/-- The even part of a degree-zero-concentrated grading is everything. -/
public theorem evenPart_degreeZeroGrade : evenPart (degreeZeroGrade R P) = ⊤ :=
  top_le_iff.mp (le_iSup_of_le 0 le_rfl)

/-- The positive even part of a degree-zero-concentrated grading is zero. -/
public theorem positiveEvenPart_degreeZeroGrade :
    positiveEvenPart (degreeZeroGrade R P) = ⊥ := by
  refine le_antisymm (iSup_le fun d => ?_) bot_le
  rw [degreeZeroGrade_eq_bot R P (by omega : 2 * (d + 1) ≠ 0)]

/-- An element of the positive even part of a degree-zero-concentrated grading is zero. -/
public theorem eq_zero_of_mem_positiveEvenPart_degreeZeroGrade {x : P}
    (hx : x ∈ positiveEvenPart (degreeZeroGrade R P)) : x = 0 := by
  rw [positiveEvenPart_degreeZeroGrade R P] at hx
  exact hx

/-- Zero lies in the positive even part, as it does in every submodule. -/
public theorem zero_mem_positiveEvenPart_degreeZeroGrade :
    (0 : P) ∈ positiveEvenPart (degreeZeroGrade R P) :=
  Submodule.zero_mem _

/-- The positive even part of a degree-zero-concentrated grading is exactly `{0}`. -/
public theorem mem_positiveEvenPart_degreeZeroGrade_iff {x : P} :
    x ∈ positiveEvenPart (degreeZeroGrade R P) ↔ x = 0 :=
  ⟨eq_zero_of_mem_positiveEvenPart_degreeZeroGrade R P,
    fun h => h ▸ zero_mem_positiveEvenPart_degreeZeroGrade R P⟩

section Dpow

variable {Q : Type v} [CommRing Q]

open Classical in
/-- The divided power operation of a degree-zero-concentrated grading: it is supported on the
single point `0` of its domain, where it must take the value `1` in index zero. -/
public noncomputable def degreeZeroDpow (n : ℕ) (x : Q) : Q :=
  if n = 0 ∧ x = 0 then 1 else 0

/-- The zeroth divided power of `0` is `1`. -/
@[simp]
public theorem degreeZeroDpow_zero_zero : degreeZeroDpow 0 (0 : Q) = 1 := by
  simp [degreeZeroDpow]

/-- Every divided power of positive index vanishes, everywhere. -/
public theorem degreeZeroDpow_eq_zero_of_ne {n : ℕ} {x : Q} (hn : n ≠ 0) :
    degreeZeroDpow n x = 0 := by
  simp [degreeZeroDpow, hn]

/-- Every divided power of positive index vanishes. -/
@[simp]
public theorem degreeZeroDpow_succ (n : ℕ) (x : Q) : degreeZeroDpow (n + 1) x = 0 :=
  degreeZeroDpow_eq_zero_of_ne n.succ_ne_zero

/-- Every divided power of positive index of `0` vanishes. -/
@[simp]
public theorem degreeZeroDpow_succ_zero (n : ℕ) : degreeZeroDpow (n + 1) (0 : Q) = 0 :=
  degreeZeroDpow_succ n 0

/-- Every divided power of a nonzero element vanishes. -/
public theorem degreeZeroDpow_of_ne_zero (n : ℕ) {x : Q} (hx : x ≠ 0) :
    degreeZeroDpow n x = 0 := by
  simp [degreeZeroDpow, hx]

end Dpow

/-- The zeroth divided power at a point of the positive even part, which is `0`. -/
public theorem degreeZeroDpow_zero_of_mem {x : P}
    (hx : x ∈ positiveEvenPart (degreeZeroGrade R P)) : degreeZeroDpow 0 x = 1 := by
  rw [eq_zero_of_mem_positiveEvenPart_degreeZeroGrade R P hx, degreeZeroDpow_zero_zero]

/-- Every positive divided power vanishes on the positive even part, which is `{0}`. -/
public theorem degreeZeroDpow_of_mem_of_ne {n : ℕ} (hn : n ≠ 0) {x : P}
    (hx : x ∈ positiveEvenPart (degreeZeroGrade R P)) : degreeZeroDpow n x = 0 := by
  rw [eq_zero_of_mem_positiveEvenPart_degreeZeroGrade R P hx]
  exact degreeZeroDpow_eq_zero_of_ne hn

/-- The unique divided power structure on a degree-zero-concentrated grading. -/
public noncomputable def degreeZeroDividedPowers :
    DividedPowerStructure (degreeZeroGrade R P) where
  dpow := degreeZeroDpow
  dpow_null hx := degreeZeroDpow_of_ne_zero _ fun h =>
    hx (h ▸ zero_mem_positiveEvenPart_degreeZeroGrade R P)
  dpow_zero hx := degreeZeroDpow_zero_of_mem R P hx
  dpow_one hx := by
    rw [degreeZeroDpow_of_mem_of_ne R P one_ne_zero hx,
      eq_zero_of_mem_positiveEvenPart_degreeZeroGrade R P hx]
  dpow_mem hn hx := by
    rw [degreeZeroDpow_of_mem_of_ne R P hn hx]
    exact zero_mem_positiveEvenPart_degreeZeroGrade R P
  dpow_mem_grade hn hx _ := by
    rw [degreeZeroDpow_of_mem_of_ne R P hn hx]
    exact Submodule.zero_mem _
  dpow_mul := by
    intro m n x hx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [degreeZeroDpow_zero_of_mem R P hx]
        simp
      · rw [degreeZeroDpow_zero_of_mem R P hx,
          degreeZeroDpow_of_mem_of_ne R P (by omega) hx, mul_zero,
          degreeZeroDpow_of_mem_of_ne R P (by omega) hx, mul_zero]
    · rw [degreeZeroDpow_of_mem_of_ne R P (by omega) hx, zero_mul,
        degreeZeroDpow_of_mem_of_ne R P (by omega) hx, mul_zero]
  dpow_mul_even := by
    intro n x y hn _ hy
    rw [eq_zero_of_mem_positiveEvenPart_degreeZeroGrade R P hy, mul_zero,
      degreeZeroDpow_of_mem_of_ne R P hn (zero_mem_positiveEvenPart_degreeZeroGrade R P),
      mul_zero]
  dpow_mul_odd := by
    intro n d e x y hn hx _
    rw [eq_zero_of_mem_degreeZeroGrade R P (Nat.succ_ne_zero (2 * d)) hx, zero_mul,
      degreeZeroDpow_of_mem_of_ne R P (by omega)
        (zero_mem_positiveEvenPart_degreeZeroGrade R P)]
  dpow_add := by
    intro n x y hx hy
    rw [eq_zero_of_mem_positiveEvenPart_degreeZeroGrade R P hx,
      eq_zero_of_mem_positiveEvenPart_degreeZeroGrade R P hy, add_zero]
    rcases n with _ | n
    · simp
    · refine (Finset.sum_eq_zero fun ij hij => ?_).symm
      rcases ij with ⟨_ | i, _ | j⟩ <;> simp_all
  dpow_dpow := by
    intro m n x hm hn hx
    rw [degreeZeroDpow_of_mem_of_ne R P hm hx,
      degreeZeroDpow_of_mem_of_ne R P hn (zero_mem_positiveEvenPart_degreeZeroGrade R P),
      degreeZeroDpow_of_mem_of_ne R P (Nat.mul_ne_zero hn hm) hx, mul_zero]

/-- The divided power operation of `degreeZeroDividedPowers R P` is `degreeZeroDpow`. -/
@[simp]
public theorem degreeZeroDividedPowers_dpow :
    (degreeZeroDividedPowers R P).dpow = degreeZeroDpow := rfl

/-- The degree-zero grading admits exactly one divided power structure. -/
public theorem degreeZeroDividedPowers_unique
    (γ : DividedPowerStructure (degreeZeroGrade R P)) :
    γ = degreeZeroDividedPowers R P := by
  refine DividedPowerStructure.ext (funext₂ fun n x => ?_)
  rw [degreeZeroDividedPowers_dpow]
  rcases eq_or_ne x 0 with rfl | hx
  · have hmem := zero_mem_positiveEvenPart_degreeZeroGrade R P
    rcases n with _ | n
    · rw [γ.dpow_zero hmem, degreeZeroDpow_zero_zero]
    · rw [degreeZeroDpow_succ,
        eq_zero_of_mem_positiveEvenPart_degreeZeroGrade R P (γ.dpow_mem n.succ_ne_zero hmem)]
  · rw [γ.dpow_null fun h => hx (eq_zero_of_mem_positiveEvenPart_degreeZeroGrade R P h),
      degreeZeroDpow_of_ne_zero _ hx]

end DividedPowers.TateResolution

end
