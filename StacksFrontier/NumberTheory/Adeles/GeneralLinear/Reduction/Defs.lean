module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.CuspForm
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.Ideles

/-!
# Upper triangular elements of `GL_n(A)` and the statements of reduction theory

Let `K` be a global function field over the finite field `k`. This file fixes the notation for
the reduction theory of `GL_n(A)` (Harder): the embeddings `GL_n(O) → GL_n(A)` and
`GL_n(K) → GL_n(A)`, the scalar matrices, upper triangular elements with prescribed diagonal,
and the three statements proved in the modules of this directory:

* `Stacks.Adeles.GeneralLinear.ReductionTheory` — every `x ∈ GL_n(A)` is `κ b γ` with
  `κ ∈ GL_n(O)`, `γ ∈ GL_n(K)` and `b` upper triangular whose consecutive diagonal entries
  satisfy `N(div a_i - div a_{i+1}) ≥ c₀` for a constant `c₀ > 0` depending only on `K` and `n`;
* `Stacks.Adeles.GeneralLinear.CuspVanishing` — a cusp form vanishes at an upper triangular `b`
  as soon as, for some `0 < r < n`, all `N(div a_i - div a_j)` with `i < r ≤ j` are large;
* `Stacks.Adeles.GeneralLinear.FiniteSupportModCenter` — there is a finite set `S ⊆ GL_n(A)`
  such that every cusp form, with values in any `Λ`, vanishes outside
  `GL_n(O) · Z(A) · S · GL_n(K)` (Harder's finiteness theorem).

Here `div a` is `Stacks.Adeles.GlobalFunctionField.idelDiv` and `N` is
`Stacks.Adeles.GlobalFunctionField.divNorm`, `N(D) = q^{deg D}`.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GeneralLinear

open Stacks.Adeles.GlobalFunctionField

variable {K : Type u} [Field K] {n : ℕ}

variable (K n) in
/-- `GL_n(O) → GL_n(A)`. -/
public abbrev mapO : GL (Fin n) (integralAdeles K) →* GL (Fin n) (AdeleRing K) :=
  GeneralLinearGroup.map (integralAdeles K).subtype

variable (K n) in
/-- `GL_n(K) → GL_n(A)`, through the principal adeles. -/
public abbrev mapK : GL (Fin n) (principalAdeles K) →* GL (Fin n) (AdeleRing K) :=
  GeneralLinearGroup.map (principalAdeles K).subtype

variable (n) in
/-- The scalar matrix `z · 1 ∈ GL_n(A)` of an idele `z`. -/
public def scalarGL : (AdeleRing K)ˣ →* GL (Fin n) (AdeleRing K) :=
  Units.map (algebraMap (AdeleRing K) (Matrix (Fin n) (Fin n) (AdeleRing K))).toMonoidHom

/-- The matrix of `scalarGL n z` is `z · 1`. -/
public theorem coe_scalarGL (z : (AdeleRing K)ˣ) :
    (scalarGL n z : Matrix (Fin n) (Fin n) (AdeleRing K)) =
      Matrix.scalar (Fin n) (z : AdeleRing K) :=
  rfl

/-- Scalar matrices are central in `GL_n(A)`. -/
public theorem scalarGL_mul_comm (z : (AdeleRing K)ˣ) (g : GL (Fin n) (AdeleRing K)) :
    scalarGL n z * g = g * scalarGL n z :=
  Units.ext (Algebra.commutes _ _)

/-- `b` is upper triangular with diagonal entries `a i`. -/
public def IsUpperTriangularWith (b : GL (Fin n) (AdeleRing K)) (a : Fin n → (AdeleRing K)ˣ) :
    Prop :=
  (∀ i j : Fin n, j < i → (b : Matrix (Fin n) (Fin n) (AdeleRing K)) i j = 0) ∧
    ∀ i, (b : Matrix (Fin n) (Fin n) (AdeleRing K)) i i = a i

variable (k : Type u) [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K]

variable (K n) in
/-- **Reduction theory for `GL_n(A)`**: there is `c₀ > 0` such that every `x ∈ GL_n(A)` is
`κ b γ` with `κ ∈ GL_n(O)`, `γ ∈ GL_n(K)` and `b` upper triangular with diagonal `a` satisfying
`c₀ ≤ N(div a_i - div a_{i+1})` for all `i`. -/
public def ReductionTheory : Prop :=
  ∃ c₀ : ℚ, 0 < c₀ ∧ ∀ x : GL (Fin n) (AdeleRing K),
    ∃ (κ : GL (Fin n) (integralAdeles K)) (γ : GL (Fin n) (principalAdeles K))
      (b : GL (Fin n) (AdeleRing K)) (a : Fin n → (AdeleRing K)ˣ),
      x = mapO K n κ * b * mapK K n γ ∧ IsUpperTriangularWith b a ∧
        ∀ i j : Fin n, (j : ℕ) = i + 1 →
          c₀ ≤ divNorm K (idelDiv k K (a i) - idelDiv k K (a j))

variable (K n) in
/-- **Vanishing of cusp forms near the cusps**: there is `M` such that every unramified cusp form
on `GL_n(A)`, with values in any `Λ`, vanishes at every upper triangular `b` with diagonal `a`
for which some `0 < r < n` has `M ≤ N(div a_i - div a_j)` for all `i < r ≤ j`. -/
public def CuspVanishing : Prop :=
  ∃ M : ℚ, ∀ (Λ : Type w) [AddCommMonoid Λ] (f : GL (Fin n) (AdeleRing K) → Λ),
    IsUnramifiedCuspFormGL n f → ∀ (b : GL (Fin n) (AdeleRing K)) (a : Fin n → (AdeleRing K)ˣ),
      IsUpperTriangularWith b a → ∀ r : ℕ, 0 < r → r < n →
        (∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) →
          M ≤ divNorm K (idelDiv k K (a i) - idelDiv k K (a j))) → f b = 0

variable (K n) in
/-- **Harder's finiteness theorem**: there is a finite set `S ⊆ GL_n(A)` such that every
unramified cusp form on `GL_n(A)`, with values in any `Λ`, vanishes outside
`GL_n(O) · Z(A) · S · GL_n(K)`. -/
public def FiniteSupportModCenter : Prop :=
  ∃ S : Finset (GL (Fin n) (AdeleRing K)), ∀ (Λ : Type w) [AddCommMonoid Λ]
    (f : GL (Fin n) (AdeleRing K) → Λ), IsUnramifiedCuspFormGL n f →
      ∀ x, f x ≠ 0 → ∃ s ∈ S, ∃ (κ : GL (Fin n) (integralAdeles K))
        (z : (AdeleRing K)ˣ) (γ : GL (Fin n) (principalAdeles K)),
        x = mapO K n κ * scalarGL n z * s * mapK K n γ

end Stacks.Adeles.GeneralLinear

end
