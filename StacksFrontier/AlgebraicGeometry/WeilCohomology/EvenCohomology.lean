module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# The even part of a `𝐙`-graded algebra

Let `H = ⨁_{n ∈ 𝐙} H^n` be a `𝐙`-graded `F`-algebra. Tag 0FIE of the Stacks Project applies the
theory of Chern classes of Section 45.12 to `⨁_{i ≥ 0} H^{2i}(i)`; after a choice of coordinate
on the Tate line this is the even part `⨁_{i ≥ 0} H^{2i}` of `H` in nonnegative degrees, graded by
`i`. This file constructs it and proves the algebra the application needs.

## Main definitions

* `Stacks.WeilCohomology.evenPart`: `⨁_{i ≥ 0} H^{2i}`, a subalgebra of `H`.
* `Stacks.WeilCohomology.evenGrade`: its grading, `H^{2i}` read in it.
* `Stacks.WeilCohomology.evenPartMap`: the restriction of a degree-preserving map.

## Main results

* `Stacks.WeilCohomology.isInternal_evenGrade`: `⨁_{i ≥ 0} H^{2i}` is a direct sum.
* `Stacks.WeilCohomology.mul_comm_of_mem_evenPart`: it is commutative when `H` is graded
  commutative.
* `Stacks.WeilCohomology.mem_of_forall_map_mem`: for a jointly injective family of graded maps,
  a class all of whose images lie in degree `n` lies in degree `n`.

## References

* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
-/

@[expose] public noncomputable section

open DirectSum

namespace Stacks.WeilCohomology

variable {F : Type*} [Field F]

/-! ### Graded pieces detected componentwise -/

section Graded

variable {H : Type*} [Ring H] [Algebra F H] (𝒜 : ℤ → Submodule F H) [GradedAlgebra 𝒜]

/-- A class all of whose components outside the range of `f` vanish lies in the span of the
pieces `𝒜 (f i)`. -/
theorem mem_iSup_of_decompose_eq_zero {ι : Type*} (f : ι → ℤ) {y : H}
    (hy : ∀ m, m ∉ Set.range f → (decompose 𝒜 y m : H) = 0) : y ∈ ⨆ i, 𝒜 (f i) := by
  classical
  rw [← sum_support_decompose 𝒜 y]
  refine Submodule.sum_mem _ fun m hm => ?_
  by_cases hmr : m ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hmr
    exact Submodule.mem_iSup_of_mem i (decompose 𝒜 y (f i)).2
  · exact ((DFinsupp.mem_support_iff.mp hm) (Subtype.ext (by simpa using hy m hmr))).elim

/-- The components outside the range of `f` of a class in the span of the pieces `𝒜 (f i)`
vanish. -/
theorem decompose_eq_zero_of_mem_iSup {ι : Type*} (f : ι → ℤ) {y : H}
    (hy : y ∈ ⨆ i, 𝒜 (f i)) {m : ℤ} (hm : m ∉ Set.range f) : (decompose 𝒜 y m : H) = 0 := by
  classical
  induction hy using Submodule.iSup_induction' with
  | mem i x hx =>
    exact decompose_of_mem_ne 𝒜 hx fun h => hm ⟨i, h⟩
  | zero => simp
  | add x y _ _ hx hy => simp [decompose_add, hx, hy]

/-- A graded `F`-algebra map commutes with taking components. -/
theorem decompose_map {H' : Type*} [Ring H'] [Algebra F H'] (𝒜' : ℤ → Submodule F H')
    [GradedAlgebra 𝒜'] (g : H →ₐ[F] H') (hg : ∀ n, ∀ a ∈ 𝒜 n, g a ∈ 𝒜' n) (y : H) (n : ℤ) :
    (decompose 𝒜' (g y) n : H') = g (decompose 𝒜 y n) := by
  classical
  conv_lhs => rw [← sum_support_decompose 𝒜 y, map_sum]
  rw [decompose_sum, DFinsupp.finset_sum_apply, Submodule.coe_sum]
  rw [Finset.sum_eq_single n]
  · exact decompose_of_mem_same 𝒜' (hg n _ (decompose 𝒜 y n).2)
  · intro m _ hmn
    exact decompose_of_mem_ne 𝒜' (hg m _ (decompose 𝒜 y m).2) hmn
  · intro hn
    rw [DFinsupp.notMem_support_iff.mp hn]
    simp

/-- **Degrees are detected by a jointly injective family of graded maps.** If every image of `y`
lies in degree `n`, so does `y`. -/
theorem mem_of_forall_map_mem {κ : Type*} {H' : κ → Type*} [∀ k, Ring (H' k)]
    [∀ k, Algebra F (H' k)] (𝒜' : ∀ k, ℤ → Submodule F (H' k)) [∀ k, GradedAlgebra (𝒜' k)]
    (g : ∀ k, H →ₐ[F] H' k) (hg : ∀ k n, ∀ a ∈ 𝒜 n, g k a ∈ 𝒜' k n)
    (hinj : Function.Injective fun y : H => fun k => g k y) {y : H} {n : ℤ}
    (hy : ∀ k, g k y ∈ 𝒜' k n) : y ∈ 𝒜 n := by
  have := mem_iSup_of_decompose_eq_zero 𝒜 (fun _ : Unit => n) (y := y) fun m hm =>
    hinj (funext fun k => ?_)
  · simpa using this
  simp only [map_zero]
  rw [← decompose_map 𝒜 (𝒜' k) (g k) (hg k),
    decompose_of_mem_ne (𝒜' k) (hy k) fun h => hm ⟨(), h⟩]

/-- **Spans of graded pieces are detected by a jointly injective family of graded maps.** -/
theorem mem_iSup_of_forall_map_mem {κ : Type*} {H' : κ → Type*} [∀ k, Ring (H' k)]
    [∀ k, Algebra F (H' k)] (𝒜' : ∀ k, ℤ → Submodule F (H' k)) [∀ k, GradedAlgebra (𝒜' k)]
    (g : ∀ k, H →ₐ[F] H' k) (hg : ∀ k n, ∀ a ∈ 𝒜 n, g k a ∈ 𝒜' k n)
    (hinj : Function.Injective fun y : H => fun k => g k y) {ι : Type*} (f : ι → ℤ) {y : H}
    (hy : ∀ k, g k y ∈ ⨆ i, 𝒜' k (f i)) : y ∈ ⨆ i, 𝒜 (f i) := by
  refine mem_iSup_of_decompose_eq_zero 𝒜 f fun m hm => hinj (funext fun k => ?_)
  simp only [map_zero]
  rw [← decompose_map 𝒜 (𝒜' k) (g k) (hg k)]
  exact decompose_eq_zero_of_mem_iSup (𝒜' k) f (hy k) hm

end Graded

/-! ### The even part -/

section Even

variable {H : Type*} [Ring H] [Algebra F H] (𝒜 : ℤ → Submodule F H) [SetLike.GradedMonoid 𝒜]

/-- `H^{2i} ∪ H^{2j} ⊆ H^{2(i+j)}`. -/
theorem mul_mem_even {i j : ℕ} {a b : H} (ha : a ∈ 𝒜 (2 * (i : ℤ))) (hb : b ∈ 𝒜 (2 * (j : ℤ))) :
    a * b ∈ 𝒜 (2 * ((i + j : ℕ) : ℤ)) := by
  have := SetLike.GradedMul.mul_mem ha hb
  rwa [show 2 * (i : ℤ) + 2 * (j : ℤ) = 2 * ((i + j : ℕ) : ℤ) by push_cast; ring] at this

/-- `1 ∈ H^0`, the degree-zero piece written as an even degree. -/
theorem one_mem_even : (1 : H) ∈ 𝒜 (2 * ((0 : ℕ) : ℤ)) := by
  simpa using SetLike.GradedOne.one_mem (A := 𝒜)

/-- **`⨁_{i ≥ 0} H^{2i}`**, the even part of `H` in nonnegative degrees, as a subalgebra. -/
def evenPart : Subalgebra F H :=
  Submodule.toSubalgebra (⨆ i : ℕ, 𝒜 (2 * (i : ℤ)))
    (Submodule.mem_iSup_of_mem 0 (one_mem_even 𝒜))
    (fun x y hx hy => by
      induction hx using Submodule.iSup_induction' with
      | mem i x hx =>
        induction hy using Submodule.iSup_induction' with
        | mem j y hy => exact Submodule.mem_iSup_of_mem (i + j) (mul_mem_even 𝒜 hx hy)
        | zero => simp
        | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
      | zero => simp
      | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h')

/-- A class lies in `⨁_{i ≥ 0} H^{2i}` exactly when it lies in the span of the pieces `H^{2i}`
with `i ≥ 0`. -/
theorem mem_evenPart_iff {x : H} : x ∈ evenPart 𝒜 ↔ x ∈ ⨆ i : ℕ, 𝒜 (2 * (i : ℤ)) := Iff.rfl

/-- A class of `H^{2i}` with `i ≥ 0` lies in `⨁_{i ≥ 0} H^{2i}`. -/
theorem mem_evenPart_of_mem {i : ℕ} {x : H} (hx : x ∈ 𝒜 (2 * (i : ℤ))) : x ∈ evenPart 𝒜 :=
  Submodule.mem_iSup_of_mem i hx

/-- **The grading of `⨁_{i ≥ 0} H^{2i}`**: its `i`-th piece is `H^{2i}`. -/
def evenGrade (i : ℕ) : AddSubgroup (evenPart 𝒜) :=
  ((𝒜 (2 * (i : ℤ))).comap (evenPart 𝒜).val.toLinearMap).toAddSubgroup

/-- A class of `⨁_{i ≥ 0} H^{2i}` lies in its `i`-th piece exactly when it lies in `H^{2i}`. -/
theorem mem_evenGrade {i : ℕ} {x : evenPart 𝒜} :
    x ∈ evenGrade 𝒜 i ↔ (x : H) ∈ 𝒜 (2 * (i : ℤ)) := Iff.rfl

/-- A degree-preserving `F`-algebra map carries `⨁_{i ≥ 0} H^{2i}` into itself. -/
theorem map_mem_evenPart {H' : Type*} [Ring H'] [Algebra F H'] (𝒜' : ℤ → Submodule F H')
    [SetLike.GradedMonoid 𝒜'] (g : H →ₐ[F] H') (hg : ∀ n, ∀ a ∈ 𝒜 n, g a ∈ 𝒜' n) {x : H}
    (hx : x ∈ evenPart 𝒜) : g x ∈ evenPart 𝒜' := by
  rw [mem_evenPart_iff] at hx ⊢
  induction hx using Submodule.iSup_induction' with
  | mem i x hx => exact Submodule.mem_iSup_of_mem i (hg _ _ hx)
  | zero => simp
  | add x y _ _ h h' => rw [map_add]; exact add_mem h h'

/-- The restriction of a degree-preserving `g` to `⨁_{i ≥ 0} H^{2i}`. -/
def evenPartMap {H' : Type*} [Ring H'] [Algebra F H'] (𝒜' : ℤ → Submodule F H')
    [SetLike.GradedMonoid 𝒜'] (g : H →ₐ[F] H') (hg : ∀ n, ∀ a ∈ 𝒜 n, g a ∈ 𝒜' n) :
    evenPart 𝒜 →ₐ[F] evenPart 𝒜' :=
  (g.comp (evenPart 𝒜).val).codRestrict (evenPart 𝒜') fun x => map_mem_evenPart 𝒜 𝒜' g hg x.2

/-- The restriction of `g` acts as `g` on underlying classes. -/
@[simp]
theorem coe_evenPartMap {H' : Type*} [Ring H'] [Algebra F H'] (𝒜' : ℤ → Submodule F H')
    [SetLike.GradedMonoid 𝒜'] (g : H →ₐ[F] H') (hg : ∀ n, ∀ a ∈ 𝒜 n, g a ∈ 𝒜' n)
    (x : evenPart 𝒜) : (evenPartMap 𝒜 𝒜' g hg x : H') = g x := rfl

/-- **The even part is commutative** in a graded commutative algebra. -/
theorem mul_comm_of_mem_evenPart
    (hcomm : ∀ (i j : ℤ) (a b : H), a ∈ 𝒜 i → b ∈ 𝒜 j →
      a * b = (Int.negOnePow (i * j) : ℤ) • (b * a))
    {x y : H} (hx : x ∈ evenPart 𝒜) (hy : y ∈ evenPart 𝒜) : x * y = y * x := by
  rw [mem_evenPart_iff] at hx hy
  induction hx using Submodule.iSup_induction' with
  | mem i x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem j y hy =>
      rw [hcomm _ _ x y hx hy]
      have : Int.negOnePow (2 * (i : ℤ) * (2 * (j : ℤ))) = 1 := by
        rw [Int.negOnePow_eq_one_iff]
        exact ⟨2 * (i : ℤ) * j, by ring⟩
      rw [this]
      simp
    | zero => simp
    | add y y' _ _ h h' => rw [mul_add, add_mul, h, h']
  | zero => simp
  | add x x' _ _ h h' => rw [add_mul, mul_add, h, h']

end Even

section Internal

variable {H : Type*} [Ring H] [Algebra F H] (𝒜 : ℤ → Submodule F H) [GradedAlgebra 𝒜]

/-- The pieces `H^{2i}`, `i ≥ 0`, are independent. -/
theorem iSupIndep_even : iSupIndep fun i : ℕ => 𝒜 (2 * (i : ℤ)) :=
  iSupIndep.comp (Decomposition.isInternal 𝒜).submodule_iSupIndep
    (f := fun i : ℕ => 2 * (i : ℤ)) fun i j h => by simpa using h

/-- **`⨁_{i ≥ 0} H^{2i}` is the direct sum of its pieces.** -/
theorem isInternal_evenGrade : DirectSum.IsInternal (evenGrade 𝒜) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro f hf
    ext j
    have hfj : ((f j : evenPart 𝒜) : H) ∈ 𝒜 (2 * (j : ℤ)) := (f j).2
    suffices h : ((f j : evenPart 𝒜) : H) = 0 by
      rw [show ((f j : evenPart 𝒜) : H) = 0 from h]
      rfl
    have hsum := DirectSum.coeAddMonoidHom_eq_dfinsuppSum (A := evenGrade 𝒜) f
    rw [hf] at hsum
    have h0 := congrArg (fun x : evenPart 𝒜 =>
      (decompose 𝒜 (x : H) (2 * (j : ℤ)) : H)) hsum
    simp only [ZeroMemClass.coe_zero, decompose_zero, DFinsupp.coe_zero, Pi.zero_apply] at h0
    rw [DFinsupp.sum, AddSubmonoidClass.coe_finset_sum, decompose_sum,
      DFinsupp.finset_sum_apply, Submodule.coe_sum, Finset.sum_eq_single j] at h0
    · rw [decompose_of_mem_same 𝒜 hfj] at h0
      exact h0.symm
    · intro i _ hij
      exact decompose_of_mem_ne 𝒜 (f i).2 (by omega)
    · intro hj
      rw [DFinsupp.notMem_support_iff.mp hj]
      simp
  · rintro ⟨x, hx⟩
    have hx' : x ∈ ⨆ i : ℕ, 𝒜 (2 * (i : ℤ)) := hx
    induction hx' using Submodule.iSup_induction' with
    | mem i y hy =>
      refine ⟨DirectSum.of (fun i => evenGrade 𝒜 i) i ⟨⟨y, hx⟩, hy⟩, ?_⟩
      rw [DirectSum.coeAddMonoidHom_of]
    | zero => exact ⟨0, by rw [map_zero]; rfl⟩
    | add y z hy hz h h' =>
      obtain ⟨d, hd⟩ := h hy
      obtain ⟨e, he⟩ := h' hz
      exact ⟨d + e, by rw [map_add, hd, he]; rfl⟩

end Internal

end Stacks.WeilCohomology

end
