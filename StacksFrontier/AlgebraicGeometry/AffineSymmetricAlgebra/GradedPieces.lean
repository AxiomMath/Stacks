module

public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The `ℤ`-graded pieces of a symmetric algebra, and their base change

The symmetric algebra of an `R`-module `M` is graded by the submodules
`SymPow.symmetricPower n R M = (range (SymmetricAlgebra.ι R M)) ^ n`, indexed by `ℕ`. A sheaf of
graded algebras is graded by `ℤ`, so **this file extends the grading to `ℤ` by zero** and records
the three facts a graded-algebra structure needs: the product of a degree-`i` and a degree-`j`
element has degree `i + j`, the unit has degree `0`, and a degree equality transports the base
change of a graded piece.

## Main definitions

* `Stacks.SymGraded.gradedPiece`: the degree-`n` piece for `n : ℤ`, the `n`-th symmetric power
  for `n ≥ 0` and `⊥` otherwise. It is defined by a match on `Int`, so that
  `gradedPiece M (n : ℕ) = symmetricPower n R M` holds by `rfl`.
* `Stacks.SymGraded.symMulₗ`: the graded multiplication, as an `R`-bilinear map of graded pieces.
* `Stacks.SymGraded.baseChangeBil`: the base change of an `R`-bilinear map along an `R`-algebra
  `A`, as an `A`-bilinear map of base changes.

## Main results

* `Stacks.SymGraded.mul_mem_gradedPiece`: the grading is multiplicative.
* `Stacks.SymGraded.baseChangeBil_tmul`: the base change of a bilinear map on pure tensors.
* `Stacks.SymGraded.heq_tensor_of_eq`: two base changes of equal submodules are heterogeneously
  equal as soon as they agree after the induced identification.

## Implementation notes

`baseChangeBil` is `LinearMap.liftBaseChange` applied to `LinearMap.baseChangeHom`: an
`R`-bilinear `m : P →ₗ[R] Q →ₗ[R] S` is read as an `R`-linear map from `P` into the `A`-module
`A ⊗ Q →ₗ[A] A ⊗ S`, and `liftBaseChange` turns that into an `A`-linear map out of `A ⊗ P`. That
route gives `A`-linearity in both variables, with computation rule `baseChangeBil_tmul`.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.SymGraded

/-! ### Base change of a bilinear map -/

section BaseChange

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  {P Q S : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  [AddCommGroup S] [Module R S]

/-- **Base change of a bilinear map.** An `R`-bilinear map `P × Q ⟶ S` induces an `A`-bilinear
map `(A ⊗_R P) × (A ⊗_R Q) ⟶ A ⊗_R S`. -/
def baseChangeBil (m : P →ₗ[R] Q →ₗ[R] S) :
    A ⊗[R] P →ₗ[A] (A ⊗[R] Q →ₗ[A] A ⊗[R] S) :=
  (LinearMap.baseChangeHom R A Q S ∘ₗ m).liftBaseChange A

/-- On pure tensors, `baseChangeBil A m (a ⊗ x) (b ⊗ y) = (a * b) ⊗ m x y`. -/
@[simp]
theorem baseChangeBil_tmul (m : P →ₗ[R] Q →ₗ[R] S) (a b : A) (x : P) (y : Q) :
    baseChangeBil A m (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) = (a * b) ⊗ₜ[R] m x y := by
  show (a • (LinearMap.baseChangeHom R A Q S (m x))) (b ⊗ₜ[R] y) = _
  rw [LinearMap.smul_apply, LinearMap.baseChangeHom_apply, LinearMap.baseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul]

end BaseChange

/-! ### Heterogeneous equality across a degree equality -/

section Heq

variable {R : Type u} [CommRing R] {T : Type u} [AddCommGroup T] [Module R T]
  {A : Type u} [AddCommGroup A] [Module R A]

/-- The identification of the base changes of two equal submodules. -/
def tensorCongr {p q : Submodule R T} (h : p = q) : A ⊗[R] p ≃ₗ[R] A ⊗[R] q :=
  TensorProduct.congr (LinearEquiv.refl R A) (LinearEquiv.ofEq p q h)

/-- The identification of the base change of a submodule with itself is the identity. -/
theorem tensorCongr_self (p : Submodule R T) (h : p = p) (z : A ⊗[R] p) :
    tensorCongr (A := A) h z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a w =>
      exact TensorProduct.congr_tmul _ _ a w
  | add z w hz hw => rw [map_add, hz, hw]

/-- The identification `tensorCongr h` sends `a ⊗ x` to `a ⊗ x`, with `x` viewed in `q`. -/
theorem tensorCongr_tmul {p q : Submodule R T} (h : p = q) (a : A) (x : p) :
    tensorCongr (A := A) h (a ⊗ₜ[R] x) = a ⊗ₜ[R] (⟨(x : T), h ▸ x.2⟩ : q) :=
  TensorProduct.congr_tmul _ _ a x

/-- **Heterogeneous equality of base changes of equal submodules.** -/
theorem heq_tensor_of_eq {p q : Submodule R T} (h : p = q) {x : A ⊗[R] p} {y : A ⊗[R] q}
    (hxy : tensorCongr (A := A) h x = y) : HEq x y := by
  subst h
  exact heq_of_eq ((tensorCongr_self p _ x).symm.trans hxy)

end Heq

/-! ### The `ℤ`-graded pieces -/

variable {R : Type u} [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- **The degree-`n` graded piece of the symmetric algebra, for `n : ℤ`**: the `n`-th symmetric
power for `n ≥ 0`, and the zero submodule for `n < 0`. The definition is by a match on `Int` so
that its value at a natural number is the symmetric power by `rfl`. -/
@[ega "II 1.7.1"]
def gradedPiece : ℤ → Submodule R (SymmetricAlgebra R M)
  | .ofNat n => SymPow.symmetricPower n R M
  | .negSucc _ => ⊥

/-- In degree `n : ℕ` the graded piece is the `n`-th symmetric power. -/
theorem gradedPiece_natCast (n : ℕ) :
    gradedPiece (R := R) M (n : ℤ) = SymPow.symmetricPower n R M := rfl

/-- In negative degree the graded piece is zero. -/
theorem gradedPiece_negSucc (n : ℕ) : gradedPiece (R := R) M (Int.negSucc n) = ⊥ := rfl

/-- The degree-zero graded piece is the submodule `1`, spanned by the unit. -/
theorem gradedPiece_zero : gradedPiece (R := R) M 0 = 1 := pow_zero _

/-- The unit of the symmetric algebra has degree zero. -/
theorem one_mem_gradedPiece : (1 : SymmetricAlgebra R M) ∈ gradedPiece (R := R) M 0 := by
  rw [gradedPiece_zero, Submodule.one_eq_span]
  exact Submodule.mem_span_singleton_self 1

/-- **The grading is multiplicative.** -/
theorem mul_mem_gradedPiece (i j : ℤ) {x y : SymmetricAlgebra R M}
    (hx : x ∈ gradedPiece (R := R) M i) (hy : y ∈ gradedPiece (R := R) M j) :
    x * y ∈ gradedPiece (R := R) M (i + j) := by
  match i, j with
  | .ofNat a, .ofNat b =>
      show x * y ∈ SymPow.symmetricPower (a + b) R M
      rw [SymPow.symmetricPower, pow_add]
      exact Submodule.mul_mem_mul hx hy
  | .ofNat _, .negSucc _ => simp [show y = 0 from hy]
  | .negSucc _, _ => simp [show x = 0 from hx]

/-- **The graded multiplication of the symmetric algebra**, as an `R`-bilinear map of graded
pieces. -/
def symMulₗ (i j : ℤ) :
    gradedPiece (R := R) M i →ₗ[R] gradedPiece (R := R) M j →ₗ[R] gradedPiece (R := R) M (i + j) :=
  LinearMap.mk₂ R
    (fun x y => ⟨(x : SymmetricAlgebra R M) * (y : SymmetricAlgebra R M),
      mul_mem_gradedPiece M i j x.2 y.2⟩)
    (fun x x' y => Subtype.ext (add_mul _ _ _))
    (fun c x y => Subtype.ext (by simp))
    (fun x y y' => Subtype.ext (mul_add _ _ _))
    (fun c x y => Subtype.ext (mul_smul_comm c (x : SymmetricAlgebra R M) _))

/-- The graded multiplication is the multiplication of the symmetric algebra. -/
@[simp]
theorem symMulₗ_coe (i j : ℤ) (x : gradedPiece (R := R) M i) (y : gradedPiece (R := R) M j) :
    ((symMulₗ M i j x y : gradedPiece (R := R) M (i + j)) : SymmetricAlgebra R M) =
      (x : SymmetricAlgebra R M) * (y : SymmetricAlgebra R M) := rfl

/-- The unit of the symmetric algebra, as a degree-zero element. -/
def oneG : gradedPiece (R := R) M 0 := ⟨1, one_mem_gradedPiece M⟩

/-- The underlying element of `oneG M` is `1`. -/
@[simp]
theorem oneG_coe : ((oneG (R := R) M : gradedPiece (R := R) M 0) : SymmetricAlgebra R M) = 1 := rfl

/-- A degree-one generator of the symmetric algebra lies in the degree-one graded piece. -/
theorem ι_mem_gradedPiece_one (m : M) :
    SymmetricAlgebra.ι R M m ∈ gradedPiece (R := R) M 1 := by
  show SymmetricAlgebra.ι R M m ∈ SymPow.symmetricPower 1 R M
  rw [SymPow.symmetricPower, pow_one]
  exact ⟨m, rfl⟩

/-- **The degree-one inclusion** `M ⟶ Sym^1_R(M)`. -/
def ιG : M →ₗ[R] gradedPiece (R := R) M 1 where
  toFun m := ⟨SymmetricAlgebra.ι R M m, ι_mem_gradedPiece_one M m⟩
  map_add' a b := Subtype.ext (map_add (SymmetricAlgebra.ι R M) a b)
  map_smul' c a := Subtype.ext (map_smul (SymmetricAlgebra.ι R M) c a)

/-- The underlying element of `ιG M m` is `SymmetricAlgebra.ι R M m`. -/
@[simp]
theorem ιG_coe (m : M) :
    ((ιG (R := R) M m : gradedPiece (R := R) M 1) : SymmetricAlgebra R M) =
      SymmetricAlgebra.ι R M m := rfl

/-- The graded multiplication of two degree-one elements is symmetric. -/
theorem symMulₗ_comm_one (x y : gradedPiece (R := R) M 1) :
    symMulₗ (R := R) M 1 1 x y = symMulₗ (R := R) M 1 1 y x :=
  Subtype.ext (mul_comm (x : SymmetricAlgebra R M) y)

end Stacks.SymGraded
