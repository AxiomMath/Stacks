module

public import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# A family of submodules indexed by `ℕ`, extended to `ℤ`

An algebra concentrated in nonnegative degrees is graded by `ℤ` once its family of homogeneous
pieces is extended by the zero submodule in negative degrees. The extension is by the zero
*submodule* of the same algebra rather than by a zero module, so that the graded multiplication
is the algebra's multiplication in every degree.

Two facts about the extension are used wherever it appears: in a negative degree it is the zero
submodule, and so an element lying in a negative degree is zero.

## Main definitions

* `Stacks.IntGraded.extend`: the extension of a family `ℕ → Submodule R A` to `ℤ → Submodule R A`
  by the zero submodule.

## Main results

* `Stacks.IntGraded.extend_natCast`: in a nonnegative degree `n` the extension is `P n`.
* `Stacks.IntGraded.extend_eq_bot_of_neg`: in a negative degree the extension is the zero
  submodule.
* `Stacks.IntGraded.eq_zero_of_mem_extend_of_neg`: an element of the extension in a negative
  degree is zero.
-/

@[expose] public section

universe u v

namespace Stacks.IntGraded

variable {R : Type u} [Semiring R] {A : Type v} [AddCommMonoid A] [Module R A]

/-- The family `P` of submodules, indexed by `ℕ`, read as a family indexed by `ℤ` that is the
zero submodule in every negative degree. -/
def extend (P : ℕ → Submodule R A) : ℤ → Submodule R A
  | (n : ℕ) => P n
  | .negSucc _ => ⊥

/-- In a nonnegative degree `n`, the extension of `P` is `P n`. -/
@[simp]
theorem extend_natCast (P : ℕ → Submodule R A) (n : ℕ) : extend P (n : ℤ) = P n := rfl

/-- The extension is the zero submodule in a negative degree. -/
theorem extend_eq_bot_of_neg (P : ℕ → Submodule R A) {n : ℤ} (hn : n < 0) : extend P n = ⊥ := by
  obtain k | k := n
  · exact absurd hn (not_lt.2 (Int.natCast_nonneg k))
  · rfl

/-- An element of the extension in a negative degree is zero. -/
theorem eq_zero_of_mem_extend_of_neg (P : ℕ → Submodule R A) {n : ℤ} (hn : n < 0) {x : A}
    (hx : x ∈ extend P n) : x = 0 :=
  (Submodule.mem_bot R).1 (extend_eq_bot_of_neg P hn ▸ hx)

end Stacks.IntGraded

end
