module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Countability of a tensor product with a finite module

Let `R` be a commutative semiring, let `M` be a countable `R`-module and let `P` be a finite
`R`-module.  Then `M ⊗[R] P` is countable.  Neither `R` nor `P` is assumed countable: a
generating family for `P` indexed by `Fin n` gives a surjection `R^n ⟶ P`, tensoring it with
`M` keeps it surjective by right exactness of the tensor product, and `M ⊗[R] R^n` is
isomorphic to `M^n`, which is countable.

## Main results

* `TensorProduct.countable`: the tensor product of a countable module with a finite module is
  countable.

## References

* [Stacks Project, Tag 0CRP](https://stacks.math.columbia.edu/tag/0CRP), where this bounds the
  cohomology of a derived tensor product with a perfect object.
-/

@[expose] public section

namespace TensorProduct

/-- **The tensor product of a countable module with a finite module is countable.** A finite
module `P` is a quotient of `R^n`, so `M ⊗[R] P` is a quotient of `M ⊗[R] R^n ≅ M^n`; no
countability of the base ring or of `P` is needed. -/
theorem countable {R : Type*} [CommSemiring R] {M P : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid P] [Module R P] [Countable M] [Module.Finite R P] : Countable (M ⊗[R] P) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  have hpow : Countable (M ⊗[R] (Fin n → R)) :=
    (TensorProduct.piScalarRight R R M (Fin n)).injective.countable
  exact (LinearMap.lTensor_surjective M hf).countable

end TensorProduct

end
