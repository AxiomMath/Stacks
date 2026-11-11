module

public import Mathlib.Algebra.Central.TensorProduct
public import StacksCore.RingTheory.SimpleRing.Centralizer

/-!
# The centralizer of a central simple subalgebra is central simple

Let `A` be a finite-dimensional central simple algebra over a field `F` and `B ⊆ A` a central
simple subalgebra with centralizer `C`. Stacks 074U says that `A = B ⊗[F] C` (this is
`Subalgebra.tensorCentralizerEquiv`) where `C` is central simple. This file supplies the
parenthetical claim: `C` is central (by descending centrality of `A ≅ B ⊗[F] C` to the right
tensor factor) and simple (`Subalgebra.centralizer_isSimple`).
-/

@[expose] public section

variable {F A : Type*} [Field F] [Ring A] [Algebra F A]
  [Algebra.IsCentral F A] [IsSimpleRing A] [FiniteDimensional F A]

/-- The centralizer of a central simple subalgebra `B` of a finite-dimensional central simple
algebra `A` is central: centrality of `A ≅ B ⊗[F] C_A(B)` descends to the right factor. -/
theorem Subalgebra.isCentral_centralizer_of_isCentral (B : Subalgebra F A) [IsSimpleRing B]
    [Algebra.IsCentral F B] :
    Algebra.IsCentral F (Subalgebra.centralizer F (B : Set A)) := by
  have : Nontrivial B := ⟨1, 0, fun h ↦ one_ne_zero (α := A) (congrArg Subtype.val h)⟩
  have := Algebra.IsCentral.of_algEquiv F _ _ B.tensorCentralizerEquiv
  exact Algebra.IsCentral.right_of_tensor_of_field F B _

/-- **Stacks 074U**, parenthetical claim: the centralizer `C` of a central simple subalgebra `B`
of a finite-dimensional central simple algebra `A` is central simple. Together with
`Subalgebra.tensorCentralizerEquiv` (`A ≅ B ⊗[F] C`) this is the whole lemma. -/
@[stacks 074U "the centralizer is central simple"]
theorem Subalgebra.isCentral_isSimpleRing_centralizer (B : Subalgebra F A) [IsSimpleRing B]
    [Algebra.IsCentral F B] :
    Algebra.IsCentral F (Subalgebra.centralizer F (B : Set A)) ∧
      IsSimpleRing (Subalgebra.centralizer F (B : Set A)) :=
  ⟨B.isCentral_centralizer_of_isCentral, B.centralizer_isSimple⟩
