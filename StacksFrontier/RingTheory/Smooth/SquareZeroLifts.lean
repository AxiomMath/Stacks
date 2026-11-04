module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Lifts along a square-zero surjection and their differences

Let `π : E →ₐ[R] F` be a surjection of `R`-algebras whose kernel squares to zero and let
`ζ : C →ₐ[R] F` be a map of `R`-algebras. A *lift* of `ζ` is a map `q : C →ₐ[R] E` with
`π ∘ q = ζ`. This file records the elementary algebra of such lifts which the infinitesimal
lifting argument of Stacks 04AM uses.

* The differences `q₂ - q₁` of two lifts are the elements of an `E`-submodule
  `Stacks.SquareZeroLift.diff π ζ` of `C →ₗ[R] E`: the `R`-linear maps with values in the
  kernel of `π` satisfying the Leibniz rule relative to a lift.
* A lift plus an element of that submodule is again a lift
  (`Stacks.SquareZeroLift.addDiff`).
* The algebras `Stacks.SquareZeroLift.thick π n` of `n`-tuples of elements of `E` with a common
  image in `F` are again square-zero thickenings of `F`, and a tuple of lifts is a lift into
  them. Two ring maps between them, `Stacks.SquareZeroLift.thickTranslate` and
  `Stacks.SquareZeroLift.thickScale`, express the translation of a pair of lifts by a difference
  and the scaling of a difference by an element of `E`; they are what makes the difference of two
  lifts a functorial, additive and linear notion in the geometric argument.

## Main definitions

* `Stacks.SquareZeroLift.IsSqZero`: the kernel of `π` squares to zero.
* `Stacks.SquareZeroLift.diff`: the module of differences of lifts.
* `Stacks.SquareZeroLift.addDiff`: a lift translated by a difference.
* `Stacks.SquareZeroLift.thick`, `Stacks.SquareZeroLift.thickπ`,
  `Stacks.SquareZeroLift.thickEval`, `Stacks.SquareZeroLift.thickLift`.
* `Stacks.SquareZeroLift.thickTranslate`, `Stacks.SquareZeroLift.thickScale`.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

namespace Stacks.SquareZeroLift

universe u v w x

variable {R : Type u} {C : Type v} {E : Type w} {F : Type x} [CommRing R] [CommRing C]
  [CommRing E] [CommRing F] [Algebra R C] [Algebra R E] [Algebra R F]

/-- The kernel of a map of algebras squares to zero. -/
def IsSqZero (π : E →ₐ[R] F) : Prop :=
  ∀ a b : E, π a = 0 → π b = 0 → a * b = 0

/-- A square-zero kernel is nilpotent. -/
theorem isNilpotent_ker_of_isSqZero {π : E →ₐ[R] F} (hsq : IsSqZero π) :
    IsNilpotent (RingHom.ker π) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  exact fun a ha b hb => (Ideal.mem_bot).2 (hsq a b ha hb)

/-! ### Differences of lifts -/

/-- **The differences of lifts of `ζ` along `π`**: the `R`-linear maps `D : C → E` with values in
the kernel of `π` satisfying `D (a * b) = q a * D b + q b * D a` for every lift `q` of `ζ`. When
`π` has square-zero kernel these are exactly the differences of two lifts. -/
def diff (π : E →ₐ[R] F) (ζ : C →ₐ[R] F) : Submodule E (C →ₗ[R] E) where
  carrier := {D | (∀ c, π (D c) = 0) ∧
    ∀ q : C →ₐ[R] E, π.comp q = ζ → ∀ a b, D (a * b) = q a * D b + q b * D a}
  add_mem' := by
    rintro D D' ⟨h₀, h₁⟩ ⟨h₀', h₁'⟩
    refine ⟨fun c => by simp [h₀ c, h₀' c], fun q hq a b => ?_⟩
    simp only [LinearMap.add_apply, h₁ q hq a b, h₁' q hq a b]
    ring
  zero_mem' := ⟨fun c => by simp, fun q _ a b => by simp⟩
  smul_mem' := by
    rintro e D ⟨h₀, h₁⟩
    refine ⟨fun c => by simp [h₀ c], fun q hq a b => ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul, h₁ q hq a b]
    ring

variable {π : E →ₐ[R] F} {ζ : C →ₐ[R] F}

/-- A difference takes values in the kernel of `π`. -/
theorem map_apply_eq_zero_of_mem_diff {D : C →ₗ[R] E} (hD : D ∈ diff π ζ) (c : C) :
    π (D c) = 0 :=
  hD.1 c

/-- A difference satisfies the Leibniz rule relative to every lift. -/
theorem leibniz_of_mem_diff {D : C →ₗ[R] E} (hD : D ∈ diff π ζ) {q : C →ₐ[R] E}
    (hq : π.comp q = ζ) (a b : C) : D (a * b) = q a * D b + q b * D a :=
  hD.2 q hq a b

/-- A difference vanishes at `1`, provided `ζ` has a lift. -/
theorem map_one_of_mem_diff {D : C →ₗ[R] E} (hD : D ∈ diff π ζ) {q : C →ₐ[R] E}
    (hq : π.comp q = ζ) : D 1 = 0 := by
  have h := leibniz_of_mem_diff hD hq 1 1
  rw [mul_one, map_one q, one_mul] at h
  linear_combination -h

/-- Two lifts of `ζ` differ by an element of the kernel of `π`. -/
private theorem map_sub_eq_zero_of_comp_eq {q q' : C →ₐ[R] E} (hq : π.comp q = ζ)
    (hq' : π.comp q' = ζ) (c : C) : π (q' c - q c) = 0 := by
  rw [map_sub, ← AlgHom.comp_apply, ← AlgHom.comp_apply, hq, hq', sub_self]

/-- **Membership in the differences, tested on one lift.** When `π` has square-zero kernel, the
Leibniz rule relative to a single lift implies it relative to every lift. -/
theorem mem_diff_of_leibniz (hsq : IsSqZero π) {D : C →ₗ[R] E} (h₀ : ∀ c, π (D c) = 0)
    {q : C →ₐ[R] E} (hq : π.comp q = ζ) (h₁ : ∀ a b, D (a * b) = q a * D b + q b * D a) :
    D ∈ diff π ζ := by
  refine ⟨h₀, fun q' hq' a b => ?_⟩
  have e1 := hsq _ _ (map_sub_eq_zero_of_comp_eq hq hq' a) (h₀ b)
  have e2 := hsq _ _ (map_sub_eq_zero_of_comp_eq hq hq' b) (h₀ a)
  rw [h₁ a b]
  linear_combination -e1 - e2

/-- **The difference of two lifts is a difference.** -/
theorem sub_mem_diff (hsq : IsSqZero π) {q₁ q₂ : C →ₐ[R] E} (h₁ : π.comp q₁ = ζ)
    (h₂ : π.comp q₂ = ζ) : q₂.toLinearMap - q₁.toLinearMap ∈ diff π ζ := by
  have hk := map_sub_eq_zero_of_comp_eq h₁ h₂
  refine ⟨hk, fun q hq a b => ?_⟩
  have hq' := map_sub_eq_zero_of_comp_eq h₁ hq
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, map_mul]
  have e1 := hsq _ _ (hk a) (hk b)
  have e2 := hsq _ _ (hq' a) (hk b)
  have e3 := hsq _ _ (hq' b) (hk a)
  linear_combination e1 - e2 - e3

/-- **A lift translated by a difference.** -/
def addDiff (hsq : IsSqZero π) {q : C →ₐ[R] E} (hq : π.comp q = ζ) {D : C →ₗ[R] E}
    (hD : D ∈ diff π ζ) : C →ₐ[R] E where
  toFun c := q c + D c
  map_one' := by rw [map_one, map_one_of_mem_diff hD hq, add_zero]
  map_mul' a b := by
    have h := hsq _ _ (hD.1 a) (hD.1 b)
    rw [map_mul, leibniz_of_mem_diff hD hq]
    linear_combination -h
  map_zero' := by simp
  map_add' a b := by simp only [map_add]; ring
  commutes' r := by
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one (A := C) r, D.map_smul,
      map_one_of_mem_diff hD hq, smul_zero, add_zero]

/-- `addDiff hsq hq hD` sends `c` to `q c + D c`. -/
@[simp]
theorem addDiff_apply (hsq : IsSqZero π) {q : C →ₐ[R] E} (hq : π.comp q = ζ) {D : C →ₗ[R] E}
    (hD : D ∈ diff π ζ) (c : C) : addDiff hsq hq hD c = q c + D c :=
  rfl

/-- A lift translated by a difference is again a lift of `ζ`. -/
theorem comp_addDiff (hsq : IsSqZero π) {q : C →ₐ[R] E} (hq : π.comp q = ζ) {D : C →ₗ[R] E}
    (hD : D ∈ diff π ζ) : π.comp (addDiff hsq hq hD) = ζ := by
  ext c
  rw [AlgHom.comp_apply, addDiff_apply, map_add, hD.1 c, add_zero, ← AlgHom.comp_apply, hq]

/-- The underlying linear map of `addDiff hsq hq hD` is `q + D`. -/
theorem addDiff_toLinearMap (hsq : IsSqZero π) {q : C →ₐ[R] E} (hq : π.comp q = ζ)
    {D : C →ₗ[R] E} (hD : D ∈ diff π ζ) :
    (addDiff hsq hq hD).toLinearMap = q.toLinearMap + D :=
  rfl

/-- Translating a lift by the difference to a second lift gives the second lift. -/
theorem addDiff_sub (hsq : IsSqZero π) {q₁ q₂ : C →ₐ[R] E} (h₁ : π.comp q₁ = ζ)
    (h₂ : π.comp q₂ = ζ) : addDiff hsq h₁ (sub_mem_diff hsq h₁ h₂) = q₂ := by
  ext c
  simp

/-! ### Tuples of elements with a common image -/

/-- **The `n`-fold fibre product of `E` over `F`**: the tuples of elements of `E` with a common
image in `F`. -/
def thick (π : E →ₐ[R] F) (n : ℕ) : Subalgebra R (Fin n → E) where
  carrier := {v | ∀ i j, π (v i) = π (v j)}
  mul_mem' {v w} hv hw i j := by
    simp only [Pi.mul_apply, map_mul, hv i j, hw i j]
  add_mem' {v w} hv hw i j := by
    simp only [Pi.add_apply, map_add, hv i j, hw i j]
  algebraMap_mem' r i j := rfl

variable (π) in
/-- The `i`-th projection of `Stacks.SquareZeroLift.thick`. -/
def thickEval {n : ℕ} (i : Fin n) : thick π n →ₐ[R] E :=
  (Pi.evalAlgHom R (fun _ => E) i).comp (thick π n).val

/-- `thickEval π i` sends a tuple to its `i`-th entry. -/
@[simp]
theorem thickEval_apply {n : ℕ} (i : Fin n) (v : thick π n) : thickEval π i v = v.1 i :=
  rfl

variable (π) in
/-- The common image in `F` of a tuple in `Stacks.SquareZeroLift.thick`. -/
def thickπ (n : ℕ) : thick π (n + 1) →ₐ[R] F :=
  π.comp (thickEval π 0)

/-- Every projection of `thick π (n + 1)`, followed by `π`, is `thickπ π n`. -/
theorem comp_thickEval {n : ℕ} (i : Fin (n + 1)) :
    π.comp (thickEval π i) = thickπ π n := by
  ext v
  exact v.2 i 0

/-- `thickπ π n` is surjective when `π` is. -/
theorem thickπ_surjective (hπ : Function.Surjective π) (n : ℕ) :
    Function.Surjective (thickπ π n) := fun a => by
  obtain ⟨e, rfl⟩ := hπ a
  exact ⟨⟨fun _ => e, fun _ _ => rfl⟩, rfl⟩

/-- `thickπ π n` has square-zero kernel when `π` has. -/
theorem isSqZero_thickπ (hsq : IsSqZero π) (n : ℕ) : IsSqZero (thickπ π n) := by
  intro v w hv hw
  apply Subtype.ext
  funext i
  have hv' : π (v.1 i) = 0 := by rw [v.2 i 0]; exact hv
  have hw' : π (w.1 i) = 0 := by rw [w.2 i 0]; exact hw
  exact hsq _ _ hv' hw'

/-- Two maps into `Stacks.SquareZeroLift.thick` with the same projections agree. -/
theorem thick_algHom_ext {D : Type*} [CommRing D] [Algebra R D] {n : ℕ}
    {g g' : D →ₐ[R] thick π n} (h : ∀ i, (thickEval π i).comp g = (thickEval π i).comp g') :
    g = g' := by
  ext d i
  exact AlgHom.congr_fun (h i) d

/-- **A tuple of lifts is a lift into `Stacks.SquareZeroLift.thick`.** -/
def thickLift {n : ℕ} (q : Fin n → (C →ₐ[R] E)) (hq : ∀ i, π.comp (q i) = ζ) :
    C →ₐ[R] thick π n :=
  (AlgHom.pi q).codRestrict _ fun c i j => by
    change π (q i c) = π (q j c)
    rw [← AlgHom.comp_apply, hq i, ← AlgHom.comp_apply, hq j]

/-- The `i`-th projection of `thickLift q hq` is `q i`. -/
@[simp]
theorem thickEval_comp_thickLift {n : ℕ} (q : Fin n → (C →ₐ[R] E))
    (hq : ∀ i, π.comp (q i) = ζ) (i : Fin n) : (thickEval π i).comp (thickLift q hq) = q i :=
  rfl

/-- `thickLift q hq` is a lift of `ζ` along `thickπ π n`. -/
theorem thickπ_comp_thickLift {n : ℕ} (q : Fin (n + 1) → (C →ₐ[R] E))
    (hq : ∀ i, π.comp (q i) = ζ) : (thickπ π n).comp (thickLift q hq) = ζ := by
  rw [thickπ, AlgHom.comp_assoc, thickEval_comp_thickLift, hq]

/-! ### Translation and scaling -/

/-- **Translation of a pair by a difference**, `(a, b, c) ↦ (c, c + b - a)`: a ring map from
triples to pairs, which carries a triple of lifts `(q₁, q₂, q₃)` to the pair `(q₃, q₃ + q₂ - q₁)`.
It is multiplicative because the kernel of `π` squares to zero. -/
def thickTranslate (hsq : IsSqZero π) : thick π 3 →ₐ[R] thick π 2 where
  toFun v := ⟨![v.1 2, v.1 2 + v.1 1 - v.1 0], by
    intro i j
    have h : ∀ k : Fin 2, π (![v.1 2, v.1 2 + v.1 1 - v.1 0] k) = π (v.1 2) := by
      intro k
      fin_cases k
      · rfl
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, map_sub, map_add,
          v.2 1 0, add_sub_cancel_right]
    rw [h i, h j]⟩
  map_one' := by
    apply Subtype.ext
    funext k
    fin_cases k <;> simp
  map_mul' v w := by
    apply Subtype.ext
    funext k
    fin_cases k
    · rfl
    · have hv10 : π (v.1 1 - v.1 0) = 0 := by rw [map_sub, v.2 1 0, sub_self]
      have hw10 : π (w.1 1 - w.1 0) = 0 := by rw [map_sub, w.2 1 0, sub_self]
      have hv02 : π (v.1 0 - v.1 2) = 0 := by rw [map_sub, v.2 0 2, sub_self]
      have hw02 : π (w.1 0 - w.1 2) = 0 := by rw [map_sub, w.2 0 2, sub_self]
      have e1 := hsq _ _ hv10 hw10
      have e2 := hsq _ _ hw02 hv10
      have e3 := hsq _ _ hv02 hw10
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Subalgebra.coe_mul,
        Pi.mul_apply]
      linear_combination e2 + e3
  map_zero' := by
    apply Subtype.ext
    funext k
    fin_cases k <;> simp
  map_add' v w := by
    apply Subtype.ext
    funext k
    fin_cases k
    · rfl
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Subalgebra.coe_add,
        Pi.add_apply]
      ring
  commutes' r := by
    apply Subtype.ext
    funext k
    fin_cases k
    · rfl
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Subalgebra.coe_algebraMap,
        Pi.algebraMap_apply, add_sub_cancel_right]

/-- The first entry of `thickTranslate hsq v` is `v 2`. -/
theorem thickEval_zero_thickTranslate (hsq : IsSqZero π) (v : thick π 3) :
    thickEval π 0 (thickTranslate hsq v) = v.1 2 :=
  rfl

/-- The second entry of `thickTranslate hsq v` is `v 2 + v 1 - v 0`. -/
theorem thickEval_one_thickTranslate (hsq : IsSqZero π) (v : thick π 3) :
    thickEval π 1 (thickTranslate hsq v) = v.1 2 + v.1 1 - v.1 0 :=
  rfl

/-- `thickTranslate hsq` commutes with the maps `thickπ` to `F`. -/
theorem thickπ_comp_thickTranslate (hsq : IsSqZero π) :
    (thickπ π 1).comp (thickTranslate hsq) = thickπ π 2 := by
  ext v
  exact v.2 2 0

/-- **Scaling of a pair by an element**, `(a, b) ↦ (a, a + e (b - a))`: a ring map from pairs to
pairs, which carries a pair of lifts `(q₁, q₂)` to `(q₁, q₁ + e (q₂ - q₁))`. -/
def thickScale (hsq : IsSqZero π) (e : E) : thick π 2 →ₐ[R] thick π 2 where
  toFun v := ⟨![v.1 0, v.1 0 + e * (v.1 1 - v.1 0)], by
    intro i j
    have h : ∀ k : Fin 2, π (![v.1 0, v.1 0 + e * (v.1 1 - v.1 0)] k) = π (v.1 0) := by
      intro k
      fin_cases k
      · rfl
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, map_add, map_mul,
          map_sub, v.2 1 0, sub_self, mul_zero, add_zero]
    rw [h i, h j]⟩
  map_one' := by
    apply Subtype.ext
    funext k
    fin_cases k <;> simp
  map_mul' v w := by
    apply Subtype.ext
    funext k
    fin_cases k
    · rfl
    · have hv10 : π (v.1 1 - v.1 0) = 0 := by rw [map_sub, v.2 1 0, sub_self]
      have hw10 : π (w.1 1 - w.1 0) = 0 := by rw [map_sub, w.2 1 0, sub_self]
      have e1 := hsq _ _ hv10 hw10
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Subalgebra.coe_mul,
        Pi.mul_apply]
      linear_combination (e - e ^ 2) * e1
  map_zero' := by
    apply Subtype.ext
    funext k
    fin_cases k <;> simp
  map_add' v w := by
    apply Subtype.ext
    funext k
    fin_cases k
    · rfl
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Subalgebra.coe_add,
        Pi.add_apply]
      ring
  commutes' r := by
    apply Subtype.ext
    funext k
    fin_cases k
    · rfl
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Subalgebra.coe_algebraMap,
        Pi.algebraMap_apply, sub_self, mul_zero, add_zero]

/-- The first entry of `thickScale hsq e v` is `v 0`. -/
theorem thickEval_zero_thickScale (hsq : IsSqZero π) (e : E) (v : thick π 2) :
    thickEval π 0 (thickScale hsq e v) = v.1 0 :=
  rfl

/-- The second entry of `thickScale hsq e v` is `v 0 + e * (v 1 - v 0)`. -/
theorem thickEval_one_thickScale (hsq : IsSqZero π) (e : E) (v : thick π 2) :
    thickEval π 1 (thickScale hsq e v) = v.1 0 + e * (v.1 1 - v.1 0) :=
  rfl

/-- `thickScale hsq e` commutes with the map `thickπ π 1` to `F`. -/
theorem thickπ_comp_thickScale (hsq : IsSqZero π) (e : E) :
    (thickπ π 1).comp (thickScale hsq e) = thickπ π 1 :=
  rfl

end Stacks.SquareZeroLift

end
