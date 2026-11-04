module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChosenPresentation

/-!
# The index family of a degree-by-degree recursion

A Tate resolution is built one degree at a time: having adjoined variables in degrees
`1, …, k`, one inspects the algebra they present and adjoins a family of new variables in
degree `k + 1`. This file carries out the recursion on the *index families* alone.

The rule is given as a single function
`newIdx : (ℕ → Type t) → ℕ → Type t`, where `newIdx f k` is the family of variables to adjoin
in degree `k + 1` to the algebra presented by the family `f`; the algebra presented by `f` is a
function of `f` by `chosenPresentation`, which is what makes a rule of this shape expressive
enough. The recursion is then an ordinary recursion on `ℕ` into `ℕ → Type t`: no dependent pair
of a family with data over it is needed.

`towerIndices newIdx k` is the family after `k` rungs; it is empty in degrees `≥ k`, and in
degrees `< k` it no longer changes, so the families converge to `towerLimit newIdx`, which is
the family a resolution is built on.

## Main definitions

* `DividedPowers.TateResolution.towerIndices` — the index family after `k` rungs.
* `DividedPowers.TateResolution.towerLimit` — the limiting index family.
* `DividedPowers.TateResolution.towerEmbed` — the degree-wise inclusion of the family after `k`
  rungs into the limiting family, and `towerRetract` its degree-wise retraction.
* `DividedPowers.TateResolution.towerComparison` — the induced algebra map.

## Main results

* `DividedPowers.TateResolution.isEmpty_towerIndices` — after `k` rungs no variable has been
  adjoined in degree `n + 1` for `n ≥ k`.
* `DividedPowers.TateResolution.towerIndices_stable` — the family in degree `n` is already
  final once `n < k`.
* `DividedPowers.TateResolution.towerLimit_eq` — the limiting family in degree `n` is exactly
  the family adjoined at rung `n`, so it is finite as soon as every rung adjoins finitely many
  variables.
* `DividedPowers.TateResolution.towerComparison_injective` — the comparison algebra map from
  the algebra after `k` rungs to the algebra on the limiting family is injective, so the former
  is a subalgebra of the latter.

## Implementation notes

The rung is recorded by `Function.update`, which is why `towerIndices newIdx (k + 1)` agrees
with `towerIndices newIdx k` away from `k` *propositionally* rather than definitionally. The
agreement is an equality of types, so an index is carried along it by `cast`;
`towerEmbed` performs that cast once, together with the case distinction that makes the
embedding total.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe t u v w

/-- The index family after `k` rungs of a degree recursion that adjoins the family
`newIdx f k` of variables in degree `k + 1` to the algebra presented by `f`. -/
public def towerIndices (newIdx : (ℕ → Type t) → ℕ → Type t) : ℕ → ℕ → Type t
  | 0 => fun _ => PEmpty
  | k + 1 => Function.update (towerIndices newIdx k) k (newIdx (towerIndices newIdx k) k)

variable {newIdx : (ℕ → Type t) → ℕ → Type t}

/-- Before any rung, the index family is empty in every degree. -/
public theorem towerIndices_zero (n : ℕ) : towerIndices newIdx 0 n = PEmpty := rfl

/-- Rung `k + 1` leaves the index family unchanged away from degree `k`. -/
public theorem towerIndices_succ_of_ne {k n : ℕ} (h : n ≠ k) :
    towerIndices newIdx (k + 1) n = towerIndices newIdx k n :=
  Function.update_of_ne h _ _

/-- Rung `k + 1` puts `newIdx (towerIndices newIdx k) k` in degree `k`. -/
public theorem towerIndices_succ_self (k : ℕ) :
    towerIndices newIdx (k + 1) k = newIdx (towerIndices newIdx k) k :=
  Function.update_self _ _ _

/-- After `k` rungs nothing has been adjoined in degree `n + 1` for `n ≥ k`. -/
public theorem isEmpty_towerIndices : ∀ {k n : ℕ}, k ≤ n → IsEmpty (towerIndices newIdx k n)
  | 0, n, _ => by
    rw [towerIndices_zero n]
    exact inferInstanceAs (IsEmpty PEmpty)
  | k + 1, n, h => by
    have hne : n ≠ k := by omega
    rw [towerIndices_succ_of_ne hne]
    exact isEmpty_towerIndices (by omega)

/-- Once the recursion has passed degree `n`, the family in degree `n` no longer changes. -/
public theorem towerIndices_stable {k n : ℕ} (hn : n < k) :
    ∀ {m : ℕ}, k ≤ m → towerIndices newIdx m n = towerIndices newIdx k n := by
  intro m hkm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · rw [towerIndices_succ_of_ne (by omega : n ≠ m)]
      exact ih (by omega)
    · have : k = m + 1 := by omega
      rw [this]

/-- The limiting index family: in degree `n` it is the family adjoined at rung `n`. -/
public def towerLimit (newIdx : (ℕ → Type t) → ℕ → Type t) (n : ℕ) : Type t :=
  towerIndices newIdx (n + 1) n

/-- The limiting family in degree `n` is the family adjoined at rung `n`. -/
public theorem towerLimit_eq (n : ℕ) :
    towerLimit newIdx n = newIdx (towerIndices newIdx n) n :=
  towerIndices_succ_self n

/-- After `k` rungs the family in degree `n < k` is the limiting family in degree `n`. -/
public theorem towerIndices_eq_towerLimit {k n : ℕ} (hn : n < k) :
    towerIndices newIdx k n = towerLimit newIdx n :=
  towerIndices_stable (Nat.lt_succ_self n) (by omega)

/-- The degree-wise inclusion of the family after `k` rungs into the limiting family: an index
of degree `n + 1` with `n < k` is already final, and there is none with `n ≥ k`. -/
public def towerEmbed (newIdx : (ℕ → Type t) → ℕ → Type t) (k n : ℕ) :
    towerIndices newIdx k n → towerLimit newIdx n :=
  fun x =>
    if h : n < k then cast (towerIndices_eq_towerLimit h) x
    else (isEmpty_towerIndices (Nat.not_lt.mp h)).elim x

/-- The degree-wise retraction of the limiting family onto the family after `k` rungs: an index
of degree `n + 1` with `n < k` is already an index of the family after `k` rungs, and one with
`n ≥ k` is not. -/
public def towerRetract (newIdx : (ℕ → Type t) → ℕ → Type t) (k n : ℕ) :
    towerLimit newIdx n → Option (towerIndices newIdx k n) :=
  fun y =>
    if h : n < k then some (cast (towerIndices_eq_towerLimit h).symm y) else none

/-- `towerRetract` is a retraction of `towerEmbed`. -/
public theorem towerRetract_towerEmbed (k n : ℕ) (x : towerIndices newIdx k n) :
    towerRetract newIdx k n (towerEmbed newIdx k n x) = some x := by
  by_cases h : n < k
  · simp [towerRetract, towerEmbed, h]
  · exact (isEmpty_towerIndices (Nat.not_lt.mp h)).elim x

/-- If every rung adjoins finitely many variables, the limiting family is finite in each
degree. -/
public theorem finite_towerLimit (hfin : ∀ (f : ℕ → Type t) (n : ℕ), Finite (newIdx f n))
    (n : ℕ) : Finite (towerLimit newIdx n) :=
  (towerLimit_eq n).symm ▸ hfin (towerIndices newIdx n) n

/-- If every rung adjoins finitely many variables, the family after `k` rungs is finite in each
degree. -/
public theorem finite_towerIndices (hfin : ∀ (f : ℕ → Type t) (n : ℕ), Finite (newIdx f n)) :
    ∀ (k n : ℕ), Finite (towerIndices newIdx k n)
  | 0, n => by
    rw [towerIndices_zero n]
    exact inferInstanceAs (Finite PEmpty)
  | k + 1, n => by
    rcases eq_or_ne n k with rfl | hne
    · rw [towerIndices_succ_self]
      exact hfin _ _
    · rw [towerIndices_succ_of_ne hne]
      exact finite_towerIndices hfin k n

/-- The comparison from the algebra after `k` rungs to the algebra on the limiting family: it
sends coefficients to coefficients and each variable to the variable of the same index in the
limiting family, and respects the grading and the divided powers. -/
public noncomputable def towerComparison (R : Type u) (P : Type v) [CommRing R] [CommRing P]
    [Algebra R P] (newIdx : (ℕ → Type (max u v w)) → ℕ → Type (max u v w)) (k : ℕ) :
    (chosenPresentation.{u, v, w} R P (towerIndices newIdx k)).A →ₐ[R]
      (chosenPresentation.{u, v, w} R P (towerLimit newIdx)).A :=
  (chosenPresentation.{u, v, w} R P (towerIndices newIdx k)).comparison
    (chosenPresentation.{u, v, w} R P (towerLimit newIdx)) (towerEmbed newIdx k)

/-- **The algebra after `k` rungs is a subalgebra of the algebra on the limiting family**: the
comparison `towerComparison` is injective. -/
public theorem towerComparison_injective (R : Type u) (P : Type v) [CommRing R] [CommRing P]
    [Algebra R P] (newIdx : (ℕ → Type (max u v w)) → ℕ → Type (max u v w)) (k : ℕ) :
    Function.Injective (towerComparison.{u, v, w} R P newIdx k) :=
  IndexedPresentation.comparison_injective _ _ _ (towerRetract newIdx k)
    (towerRetract_towerEmbed k)

end DividedPowers.TateResolution

end
