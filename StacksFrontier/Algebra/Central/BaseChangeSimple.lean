module

public import StacksCore.Algebra.Central.TensorProduct
public import StacksCore.RingTheory.SimpleRing.TensorProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of a finite central simple algebra

Stacks tag 074H: if `A` is a finite central simple algebra over a field `k` and `L / k` is a field
extension, then `L ⊗[k] A` is a finite central simple algebra over `L`. This combines
`Module.Finite.base_change` (finiteness), `Algebra.IsCentral.baseChange` (centrality) and
`Algebra.TensorProduct.isSimpleRing'` (simplicity, Stacks tag 074F).
-/

@[expose] public section

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

open scoped TensorProduct

/-- **Stacks 074H.** If `A` is a finite central simple algebra over a field `k` and `L / k` is a
field extension, then `L ⊗[k] A` is a finite central simple algebra over `L`: it is
finite-dimensional over `L`, central over `L`, and simple.

Stacks writes the base change as `A ⊗_k k'`; here it is `L ⊗[k] A`, whose `L`-algebra structure
comes from the left factor. -/
@[stacks 074H]
theorem Algebra.IsCentral.finiteDimensional_isCentral_isSimpleRing_baseChange (L : Type*)
    [Field L] [Algebra k L] [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A] :
    FiniteDimensional L (L ⊗[k] A) ∧ Algebra.IsCentral L (L ⊗[k] A) ∧
      IsSimpleRing (L ⊗[k] A) :=
  ⟨Module.Finite.base_change k L A, inferInstance, inferInstance⟩
