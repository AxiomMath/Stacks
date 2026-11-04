module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Thicken

/-!
# The Čech nerve as small algebras, with its thickenings

For a `κ`-small flat `A'`-algebra `C'` (with `κ` uncountable), `nerve n` is the `n`-th term of
the Čech nerve of `A' → C'` as a `κ`-small algebra, and `nerveThk n` its thickening along a
square-zero ideal `I ⊆ A'`. The face `0` is a base change of thickenings
(`isBaseChange_nerve_face_zero`).
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
  (C' : Type u) [CommRing C'] [Algebra A' C'] (hC : Cardinal.mk C' < κ)

/-- The `n`-th term of the Čech nerve of `A' → C'`, as a `κ`-small algebra. -/
abbrev nerve (n : ℕ) : SmallAlg A' κ :=
  SmallAlg.mk (A' := A') (cech A' C' n) (card_cech_lt A' C' hκ hC n)

/-- The `(n + 1)`-st term of the Čech nerve is the tensor product of the `n`-th term with `C'`
over `A'`. -/
theorem nerve_succ_eq (n : ℕ) :
    nerve (A' := A') hκ C' hC (n + 1) =
      SmallAlg.mk ((nerve (A' := A') hκ C' hC n).obj ⊗[A'] C')
        (card_cech_lt A' C' hκ hC (n + 1)) := rfl

variable (I : Ideal A') (hI : I ^ 2 = ⊥)

include hI in
/-- The thickening along `I` of the `(n + 1)`-st term of the Čech nerve is a base change, by `C'`,
of the thickening of the `n`-th term, via the map induced by the face `0`. -/
theorem isBaseChange_nerve_face_zero (n : ℕ) :
    IsBaseChange (thk I hI (nerve (A' := A') hκ C' hC n)) C'
      (thk I hI (nerve (A' := A') hκ C' hC (n + 1)))
      (thkHom I hI (N' := nerve (A' := A') hκ C' hC (n + 1)) (face A' C' n 0)) := by
  have := isBaseChange_includeLeft (F := C') I hI (nerve (A' := A') hκ C' hC n)
    (card_cech_lt A' C' hκ hC (n + 1))
  refine ⟨this.ker_eq, fun x ↦ ?_⟩
  exact face_zero_apply n x

end AlgebraicGeometry.Stack.GroupoidLift

end
