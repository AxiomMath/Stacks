module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.Smoothing.StandardSmoothPresentation

/-!
# Making a localization of a presentation standard smooth
-/

/-!
# Making a localization of a presentation standard smooth

Stacks tag 00T8, with the definition of standard smooth being Stacks tag 00T6
(Definition 10.137.5).

Throughout, `R` is a commutative ring with unit and `R[x_1, …, x_m]` denotes the
polynomial ring in `m` variables over `R`, modelled as `MvPolynomial (Fin m) R`.
Partial derivatives are the usual formal partial derivatives `MvPolynomial.pderiv`.

Given integers `n ≥ c ≥ 0` and polynomials `g_1, …, g_c ∈ R[y_1, …, y_n]`, the
presentation `P = R[y_1, …, y_n]/(g_1, …, g_c)` is a *standard smooth algebra over `R`*
when the determinant of the `c × c` matrix of partial derivatives of `g_1, …, g_c` with
respect to the *first* `c` variables `y_1, …, y_c` maps to an invertible element of `P`.

The result: let `f_1, …, f_c ∈ R[x_1, …, x_n]` and let `h` be the determinant of the
`c × c` matrix of partial derivatives of `f_1, …, f_c` with respect to the first `c`
variables. Regarding the `f_i` and `h` as elements of `R[x_1, …, x_{n+1}]`, set
`S = R[x_1, …, x_{n+1}]/(f_1, …, f_c, x_{n+1} h - 1)`. Then `S` is standard smooth over
`R`, witnessed by the presentation in which the `n+1` variables are taken in the order
`x_1, …, x_c, x_{n+1}, x_{c+1}, …, x_n` and the `c+1` relations are
`f_1, …, f_c, x_{n+1} h - 1`.
-/

@[expose] public section

open MvPolynomial Matrix

namespace Stacks.StandardSmooth

variable {R : Type*} [CommRing R]

/-- The `c × c` Jacobian matrix of the family `g : Fin c → R[y_0, ..., y_{n-1}]`
with respect to the first `c` variables `y_0, ..., y_{c-1}`.  Here `hc : c ≤ n`
allows us to view the first `c` variable indices `Fin c` inside `Fin n` via
`Fin.castLE`.  The `(j, i)` entry is `∂ g_j / ∂ y_i`. -/
noncomputable def jacobianFirst {n c : ℕ} (hc : c ≤ n) (g : Fin c → MvPolynomial (Fin n) R) :
    Matrix (Fin c) (Fin c) (MvPolynomial (Fin n) R) :=
  Matrix.of fun j i => pderiv (Fin.castLE hc i) (g j)

/-- `jacobianFirst` is the transpose of the matrix whose determinant is `jacobianDet`, so the
two determinants agree. -/
theorem det_jacobianFirst {n c : ℕ} (hc : c ≤ n) (g : Fin c → MvPolynomial (Fin n) R) :
    (jacobianFirst hc g).det = jacobianDet hc g := by
  rw [jacobianDet, ← Matrix.det_transpose]
  rfl

/-- An `R`-algebra `A` is *standard smooth over `R`* if it is isomorphic, as an
`R`-algebra, to a standard smooth presentation. -/
def IsStandardSmooth (A : Type*) [CommRing A] [Algebra R A] : Prop :=
  ∃ (n c : ℕ) (hc : c ≤ n) (g : Fin c → MvPolynomial (Fin n) R),
    IsStandardSmoothPresentation hc g ∧
      Nonempty (A ≃ₐ[R] (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range g)))

/-! ### The construction of Stacks Tag 00T8

We are given `f : Fin c → R[x_0, ..., x_{n-1}]` with `c ≤ n`, and we set
`h = det (jacobianFirst f)`.  We work over `n + 1` variables.

To realize the reordering `x_0, ..., x_{c-1}, x_n, x_c, ..., x_{n-1}` of the
problem, we provide a relabeling injection `reorder : Fin (n+1) → Fin (n+1)`
that sends the chosen "first `c+1`" variable slots to the actual variables
`x_0, ..., x_{c-1}, x_n`.  Concretely, the chosen first `c+1` variables are, in
order, `x_0, ..., x_{c-1}` followed by `x_n`. -/

/-- The injection picking out the `c+1` "first" variable slots in the chosen
order: the first `c` slots are the variables `x_0, ..., x_{c-1}` and the last slot
is the variable `x_n` (the `(n+1)`-st variable, of index `n` in `Fin (n+1)`). -/
def reorderSel {n c : ℕ} (hc : c ≤ n) : Fin (c + 1) → Fin (n + 1) := fun j =>
  if h : (j : ℕ) < c then Fin.castLE (by omega) (Fin.castLE hc ⟨j, h⟩) else Fin.last n

/-- The first `c` relations: the original polynomials `f_0, ..., f_{c-1}`, viewed
as elements of `R[x_0, ..., x_n]` (they do not involve `x_n`), via the inclusion
`Fin n ↪ Fin (n+1)` on variables. -/
noncomputable def liftF {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R) :
    Fin c → MvPolynomial (Fin (n + 1)) R := fun j => MvPolynomial.rename (Fin.castSucc) (f j)

/-- The polynomial `h ∈ R[x_0, ..., x_{n-1}]`, the determinant of the Jacobian of
`f` with respect to the first `c` variables. -/
noncomputable def hPoly {n c : ℕ} (hc : c ≤ n) (f : Fin c → MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R :=
  (jacobianFirst hc f).det

/-- The full family of `c + 1` relations `g_0, ..., g_c` over `R[x_0, ..., x_n]`:
the first `c` are the lifted `f_j`, and the last is `x_n * h - 1`. -/
noncomputable def relations {n c : ℕ} (hc : c ≤ n) (f : Fin c → MvPolynomial (Fin n) R) :
    Fin (c + 1) → MvPolynomial (Fin (n + 1)) R := fun j =>
  if h : (j : ℕ) < c then liftF f ⟨j, h⟩
  else X (Fin.last n) * MvPolynomial.rename Fin.castSucc (hPoly hc f) - 1

/-- The algebra `S` of Stacks Tag 00T8. -/
abbrev SAlg {n c : ℕ} (hc : c ≤ n) (f : Fin c → MvPolynomial (Fin n) R) : Type _ :=
  MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span (Set.range (relations hc f))

/-! ### Main statements -/

/-- `reorderSel` on a `castSucc` index (i.e. `i < c`). -/
lemma reorderSel_castSucc {n c : ℕ} (hc : c ≤ n) (i : Fin c) :
    reorderSel hc (Fin.castSucc i) = Fin.castSucc (Fin.castLE hc i) := by
  unfold reorderSel
  rw [dite_eq_left (by simp)]
  apply Fin.ext
  simp [Fin.castLE, Fin.castSucc, Fin.castAdd]

/-- `reorderSel` on the last index equals the last variable. -/
lemma reorderSel_last {n c : ℕ} (hc : c ≤ n) : reorderSel hc (Fin.last c) = Fin.last n := by
  unfold reorderSel
  rw [dite_eq_right (by simp)]

/-- `relations` on a `castSucc` index. -/
lemma relations_castSucc {n c : ℕ} (hc : c ≤ n) (f : Fin c → MvPolynomial (Fin n) R) (j : Fin c) :
    relations hc f (Fin.castSucc j) = MvPolynomial.rename Fin.castSucc (f j) := by
  unfold relations liftF
  rw [dite_eq_left (by simp)]
  congr 2

/-- `relations` on the last index. -/
lemma relations_last {n c : ℕ} (hc : c ≤ n) (f : Fin c → MvPolynomial (Fin n) R) :
    relations hc f (Fin.last c) =
      X (Fin.last n) * MvPolynomial.rename Fin.castSucc (hPoly hc f) - 1 := by
  unfold relations
  rw [dite_eq_right (by simp)]

/-- Renaming variables commutes with taking the determinant of a matrix. -/
private theorem det_map_rename {ι σ τ : Type*} [Fintype ι] [DecidableEq ι] (e : σ → τ)
    (M : Matrix ι ι (MvPolynomial σ R)) : (M.map (rename e)).det = rename e M.det :=
  (RingHom.map_det (rename e : MvPolynomial σ R →ₐ[R] MvPolynomial τ R).toRingHom M).symm

/-- The last variable does not occur in a polynomial renamed along `Fin.castSucc`. -/
private theorem pderiv_last_rename_castSucc {n : ℕ} (p : MvPolynomial (Fin n) R) :
    pderiv (Fin.last n) (rename Fin.castSucc p) = 0 :=
  pderiv_rename_eq_zero_of_not_mem_range Fin.castSucc (Fin.last n)
    (fun ⟨s, hs⟩ => (Fin.castSucc_lt_last s).ne hs) p

/-- The central computation underlying the theorem: the determinant of the
`(c+1) × (c+1)` Jacobian matrix of the relations `g_0, ..., g_c` with respect to
the chosen first `c + 1` variables `x_0, ..., x_{c-1}, x_n` equals `h^2` (as an
element of `R[x_0, ..., x_n]`), where `h` is regarded inside `R[x_0, ..., x_n]`. -/
theorem jacobian_det_eq_h_sq {n c : ℕ} (hc : c ≤ n) (f : Fin c → MvPolynomial (Fin n) R) :
    (Matrix.of fun (j i : Fin (c + 1)) => pderiv (reorderSel hc i) (relations hc f j)).det =
      (MvPolynomial.rename Fin.castSucc (hPoly hc f)) ^ 2 := by
  set M : Matrix (Fin (c + 1)) (Fin (c + 1)) (MvPolynomial (Fin (n + 1)) R) :=
    Matrix.of fun (j i : Fin (c + 1)) => pderiv (reorderSel hc i) (relations hc f j) with hM
  -- last column: entry at last row
  have hlast_last :
    M (Fin.last c) (Fin.last c) = MvPolynomial.rename Fin.castSucc (hPoly hc f) := by
    simp only [hM, Matrix.of_apply, reorderSel_last, relations_last]
    rw [map_sub, pderiv_mul, pderiv_X, pderiv_last_rename_castSucc]
    simp
  -- last column: entry at non-last rows is zero
  have hlast_zero : ∀ j' : Fin c, M (Fin.castSucc j') (Fin.last c) = 0 := by
    intro j'
    simp only [hM, Matrix.of_apply, reorderSel_last, relations_castSucc]
    exact pderiv_last_rename_castSucc (f j')
  -- submatrix (drop last row & col) equals renamed jacobianFirst
  have hsub :
    M.submatrix (Fin.last c).succAbove (Fin.last c).succAbove =
      (jacobianFirst hc f).map (MvPolynomial.rename Fin.castSucc) := by
    ext j' i'
    simp only [Matrix.submatrix_apply, Fin.succAbove_last_apply, hM, Matrix.of_apply,
      Matrix.map_apply, jacobianFirst, reorderSel_castSucc, relations_castSucc]
    rw [pderiv_rename (Fin.castSucc_injective n) (Fin.castLE hc i') (f j')]
  -- cofactor expansion along the last column
  rw [Matrix.det_succ_column M (Fin.last c), Finset.sum_eq_single (Fin.last c)]
  · rw [hlast_last, hsub]
    rw [det_map_rename, ← hPoly]
    have : ((-1 : MvPolynomial (Fin (n + 1)) R)) ^ ((Fin.last c : ℕ) + (Fin.last c : ℕ)) = 1 := by
      rw [← two_mul]
      simp [pow_mul]
    rw [this]
    ring
  · intro i _ hine
    -- i ≠ last, so i = castSucc of something, entry is zero
    obtain ⟨i0, rfl⟩ := Fin.exists_castSucc_eq.mpr hine
    rw [hlast_zero i0]
    ring
  · exact fun h => absurd (Finset.mem_univ _) h

/-! ### The variable-reordering permutation and the main theorem -/

/-- The variable-reordering permutation of `Fin (n+1)`.  It sends the chosen
"first `c+1`" variable slots `reorderSel hc i` to the genuine first `c+1` slots
`Fin.castLE _ i`.  Concretely it fixes `0, …, c-1`, sends `n ↦ c`, and shifts
`c, …, n-1` up to `c+1, …, n`.  (This is the inverse of the "place `x_n` into slot
`c`" relabeling.) -/
def reorderPerm {n c : ℕ} (hc : c ≤ n) : Equiv.Perm (Fin (n + 1)) where
  toFun k :=
    if k.val < c then k
    else
      if h : k.val = n then ⟨c, by omega⟩
      else
        ⟨k.val + 1, by
          have := k.isLt; omega⟩
  invFun k :=
    if k.val < c then k
    else
      if h : k.val = c then Fin.last n
      else
        ⟨k.val - 1, by
          have := k.isLt; omega⟩
  left_inv k := by
    apply Fin.ext
    simp only [Fin.last]
    split_ifs <;> simp_all +decide <;> omega
  right_inv k := by
    -- arithmetic.  `toFun`/`invFun` are mutually inverse bijections of `[0,n]`:
    -- `toFun` fixes `[0,c)`, sends `n ↦ c`, shifts `[c,n) ↦ (c,n]`;
    -- `invFun` fixes `[0,c)`, sends `c ↦ n`, shifts `(c,n] ↦ [c,n)`.
    -- Close by case analysis on `k.val < c` / `= c` / else and `omega` (the only
    -- snag is reducing `(Fin.last n).val` to `n`, e.g. via `Fin.val_last`).
    apply Fin.ext
    have hk := k.isLt
    rcases lt_trichotomy k.val c with h1 | h1 | h1
    · -- k.val < c : invFun fixes k, toFun fixes k
      simp only [ite_eq_left h1]
    · -- k.val = c : invFun k = last n, toFun (last n) = ⟨c, _⟩
      have hnc : ¬(n : ℕ) < c := by omega
      simp only [ite_eq_right (by omega : ¬k.val < c), dite_eq_left h1, Fin.last, ite_eq_right hnc,
        dite_eq_left trivial]
      omega
    · -- c < k.val : invFun k = ⟨k.val - 1, _⟩, toFun shifts back
      have h1' : ¬k.val < c := by omega
      have h2' : ¬k.val = c := by omega
      have hlt : ¬k.val - 1 < c := by omega
      simp only [ite_eq_right h1', dite_eq_right h2', ite_eq_right hlt,
        dite_eq_right (by omega : ¬k.val - 1 = n)]
      omega

/-- **Orientation lemma.**  The permutation `reorderPerm` carries each chosen
"first" slot `reorderSel hc i` to the genuine first slot `Fin.castLE _ i`.  This
is what makes the chain rule (`pderiv_rename`) align the reordered Jacobian of
`relations` with the Jacobian of the renamed family `g'` taken with respect to
its genuine first `c+1` variables. -/
lemma reorderPerm_reorderSel {n c : ℕ} (hc : c ≤ n) (i : Fin (c + 1)) :
    reorderPerm hc (reorderSel hc i) = Fin.castLE (Nat.succ_le_succ hc) i := by
  -- If `i.val < c`: `reorderSel` gives `castLE … i` with value `i.val < c`, so
  --   `reorderPerm` (first branch) fixes it; both sides have value `i.val`.
  -- If `i = last c`: `reorderSel` gives `Fin.last n` (value `n`), `reorderPerm`
  --   (second branch, `k.val = n`) returns `⟨c, _⟩`; RHS `castLE … (last c)` has
  --   value `c`.  Conclude by `Fin.ext` + `omega`.
  have hi := i.isLt
  unfold reorderPerm reorderSel
  simp only [Equiv.coe_fn_mk]
  by_cases h : (i : ℕ) < c
  · rw [dite_eq_left h, ite_eq_left
        (show ((Fin.castLE (by omega) (Fin.castLE hc ⟨(i : ℕ), h⟩) : Fin (n + 1))).val < c by
          simpa using h)]
    apply Fin.ext
    simp [Fin.castLE]
  · rw [dite_eq_right h]
    have hnc : ¬(Fin.last n).val < c := by
      rw [Fin.val_last]
      omega
    rw [ite_eq_right hnc, dite_eq_left (Fin.val_last n)]
    apply Fin.ext
    simp only [Fin.val_castLE]
    omega

/-- The reordered relation family `g'` over the same `n+1` variables: it is the
original `relations hc f` with the variables permuted by `reorderPerm hc`.  By the
orientation lemma, the genuine first `c+1` variables of `g'` are the chosen
reordered variables of `relations hc f`. -/
noncomputable def reorderedRelations {n c : ℕ} (hc : c ≤ n) (f : Fin c → MvPolynomial (Fin n) R) :
    Fin (c + 1) → MvPolynomial (Fin (n + 1)) R := fun j =>
  MvPolynomial.rename (reorderPerm hc) (relations hc f j)

/-- **The reordered presentation is standard smooth.**  Its Jacobian determinant
(w.r.t. the genuine first `c+1` variables) maps to a unit in the quotient.

Argument:
1. By the orientation lemma `reorderPerm_reorderSel` and the chain rule
   `pderiv_rename` (for the injective `reorderPerm`), the `(j,i)` entry of
   `jacobianFirst hc' (reorderedRelations hc f)` equals
   `rename (reorderPerm hc) (pderiv (reorderSel hc i) (relations hc f j))`.
   Hence `(jacobianFirst hc' g').det = rename (reorderPerm hc) (det of the
   reordered Jacobian of `relations`)` by `RingHom.map_det`.
2. By `jacobian_det_eq_h_sq`, that inner determinant is
   `(rename Fin.castSucc (hPoly hc f))^2`, so
   `(jacobianFirst hc' g').det = (rename (reorderPerm hc) (rename Fin.castSucc (hPoly hc f)))^2`.
3. It suffices that `Ideal.Quotient.mk J (rename (reorderPerm hc)
   (rename Fin.castSucc (hPoly hc f)))` is a unit; its square is then a unit by
   `IsUnit.pow`.
4. Unit witness: in the quotient by `J = span (range g')`, the image of
   `g' (last c) = rename (reorderPerm hc) (X (last n) * rename castSucc h - 1)` is
   `0`, i.e. `(rename e (X (last n))) * (rename e (rename castSucc h)) = 1`.  So
   `rename e (rename castSucc h)` is a unit with explicit inverse
   `mk (rename e (X (last n)))`, via `isUnit_of_mul_eq_one`.  Membership of
   `g' (last c)` in `J` is `Ideal.subset_span ⟨last c, rfl⟩`. -/
lemma reorderedRelations_isStandardSmoothPresentation {n c : ℕ} (hc : c ≤ n)
    (f : Fin c → MvPolynomial (Fin n) R) :
    IsStandardSmoothPresentation (Nat.succ_le_succ hc) (reorderedRelations hc f) := by
  -- against the file definitions, with `jacobian_det_eq_h_sq` and the orientation
  -- lemma as inputs.  Direction of `pderiv_rename` confirmed: we need
  -- `Fin.castLE hc' i = reorderPerm hc (reorderSel hc i)`, which is exactly the
  -- orientation lemma `reorderPerm_reorderSel`.  Key Mathlib lemmas:
  -- `pderiv_rename` (e injective), `RingHom.map_det`, `map_pow`, `map_mul`,
  -- `map_sub`, `Ideal.subset_span`, `Ideal.Quotient.eq_zero_iff_mem` (or
  -- `Quotient.mk` of an ideal member is 0), `isUnit_of_mul_eq_one`/
  -- `IsUnit.of_mul_eq_one`, `IsUnit.pow`.
  set e := reorderPerm hc with he
  set hc' := Nat.succ_le_succ hc
  -- Step 1 & 2: compute the Jacobian determinant.
  have hentry :
    jacobianFirst hc' (reorderedRelations hc f) =
      (Matrix.of fun (j i : Fin (c + 1)) => pderiv (reorderSel hc i) (relations hc f j)).map
        (MvPolynomial.rename (e : Fin (n + 1) → Fin (n + 1))) := by
    ext j i
    simp only [jacobianFirst, reorderedRelations, Matrix.of_apply, Matrix.map_apply]
    rw [← reorderPerm_reorderSel hc i, ← he,
      pderiv_rename e.injective (reorderSel hc i) (relations hc f j)]
  have hdet :
    (jacobianFirst hc' (reorderedRelations hc f)).det =
      (MvPolynomial.rename (e : Fin (n + 1) → Fin (n + 1))
          (MvPolynomial.rename Fin.castSucc (hPoly hc f))) ^
        2 := by
    rw [hentry, det_map_rename, jacobian_det_eq_h_sq hc f, map_pow]
  -- Step 3 & 4: the unit witness.
  rw [IsStandardSmoothPresentation, ← det_jacobianFirst, hdet, map_pow]
  apply IsUnit.pow
  -- show mk J (rename e (rename castSucc (hPoly hc f))) is a unit
  set J := Ideal.span (Set.range (reorderedRelations hc f))
  -- The last relation lies in J, so its image is 0.
  have hmem : reorderedRelations hc f (Fin.last c) ∈ J := Ideal.subset_span ⟨Fin.last c, rfl⟩
  have hzero : (Ideal.Quotient.mk J) (reorderedRelations hc f (Fin.last c)) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [reorderedRelations, relations_last, map_sub, map_mul, map_sub, map_mul, map_one, map_one,
    sub_eq_zero] at hzero
  -- hzero : mk (rename e (X (last n))) * mk (rename e (rename castSucc h)) = 1
  exact .of_mul_eq_one _ ((mul_comm _ _).trans hzero)

/-- **The algebra `SAlg hc f` is isomorphic to the reordered presentation.**

The `R`-algebra automorphism `Φ = renameEquiv R (reorderPerm hc)` of
`MvPolynomial (Fin (n+1)) R` carries `I = span (range (relations hc f))` onto
`J = span (range (reorderedRelations hc f))`, because
`J = span (Φ '' range (relations hc f)) = I.map Φ` by `Ideal.map_span` together
with `Set.range_comp`/`Set.image_range`.  Then `Ideal.quotientEquivAlg I J Φ`
provides the desired `R`-algebra isomorphism `SAlg hc f ≃ₐ[R] MvPoly/J`. -/
lemma SAlg_algEquiv_reorderedRelations {n c : ℕ} (hc : c ≤ n)
    (f : Fin c → MvPolynomial (Fin n) R) :
    Nonempty
      (SAlg hc f ≃ₐ[R]
        (MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span (Set.range (reorderedRelations hc f)))) := by
  -- `Ideal.quotientEquivAlg` transport along the algebra automorphism
  -- `Φ = renameEquiv R (reorderPerm hc)`.  The ideal-image identity
  -- `span (range (reorderedRelations hc f)) = (span (range (relations hc f))).map Φ`
  -- follows from `Ideal.map_span`, `Set.image_range`/`Set.range_comp` since
  -- `reorderedRelations hc f = (Φ : _ →+* _) ∘ relations hc f`.  Then
  -- `⟨Ideal.quotientEquivAlg _ _ Φ this⟩` gives the witness.
  set Φ : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
    MvPolynomial.renameEquiv R (reorderPerm hc)
  have hJeq :
    Ideal.span (Set.range (reorderedRelations hc f)) =
      (Ideal.span (Set.range (relations hc f))).map (Φ : _ →+* _) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
  exact ⟨Ideal.quotientEquivAlg _ _ Φ hJeq⟩

/-- **Theorem (Stacks Tag 00T8).**  With `f : Fin c → R[x_0, ..., x_{n-1}]`,
`h = det(jacobianFirst f)`, and
`S = R[x_0, ..., x_n] / (f_0, ..., f_{c-1}, x_n * h - 1)`, the algebra `S` is
standard smooth over `R`.  The witnessing presentation reorders the variables so
that the first `c + 1` variables (in the chosen order) are
`x_0, ..., x_{c-1}, x_n`, and uses the relations `g_0, ..., g_c`. -/
@[stacks 00T8]
theorem isStandardSmooth_SAlg {n c : ℕ} (hc : c ≤ n) (f : Fin c → MvPolynomial (Fin n) R) :
    IsStandardSmooth (R := R) (SAlg hc f) := by
  -- Witness the standard-smooth structure with `n' = n+1`, `c' = c+1`, and the
  -- reordered relation family `g' = reorderedRelations hc f`.  The two halves of
  -- the definition are exactly the two lemmas above.
  exact
    ⟨n + 1, c + 1, Nat.succ_le_succ hc, reorderedRelations hc f,
      reorderedRelations_isStandardSmoothPresentation hc f, SAlg_algEquiv_reorderedRelations hc f⟩

end Stacks.StandardSmooth

end
