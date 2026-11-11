module

public import StacksCore.Algebra.Central.TensorProduct
public import StacksCore.RingTheory.SimpleRing.TensorProduct
public import StacksCore.RingTheory.TensorProduct.Finite

/-!
# The tensor product of finite central simple algebras

Stacks tag 074G: over a field `k`, the tensor product of two finite central simple `k`-algebras
is again finite, central and simple. The three properties come from

* `Module.Finite.tensorProduct` (finiteness, upstream),
* the `Algebra.IsCentral k (A ⊗[k] B)` instance of `StacksCore.Algebra.Central.TensorProduct`, built
  from Stacks tag 0749 (centralizers in a tensor product),
* `Algebra.TensorProduct.isSimpleRing` (Stacks tag 074F).
-/

@[expose] public section

open scoped TensorProduct

variable {k A B : Type*} [Field k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]

/-- **Stacks 074G.** The tensor product of finite central simple algebras over a field `k` is
finite, central, and simple. -/
@[stacks 074G "finite, central and simple"]
theorem Algebra.TensorProduct.finite_isCentral_isSimpleRing
    [Module.Finite k A] [Algebra.IsCentral k A] [IsSimpleRing A]
    [Module.Finite k B] [Algebra.IsCentral k B] [IsSimpleRing B] :
    Module.Finite k (A ⊗[k] B) ∧ Algebra.IsCentral k (A ⊗[k] B) ∧ IsSimpleRing (A ⊗[k] B) :=
  ⟨inferInstance, inferInstance, inferInstance⟩
