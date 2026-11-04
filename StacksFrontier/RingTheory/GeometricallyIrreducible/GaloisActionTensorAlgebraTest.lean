module

public import StacksFrontier.RingTheory.GeometricallyIrreducible.GaloisAction

/-!
# Regression tests: `Algebra.TensorProduct.rightAlgebra` stays local to `GaloisAction`

`StacksFrontier.RingTheory.GeometricallyIrreducible.GaloisAction` once exported
`attribute [instance] Algebra.TensorProduct.rightAlgebra`. On `K ⊗[k] K` that made instance
search find the right-factor structure `a ↦ 1 ⊗ a` instead of Mathlib's global
`Algebra.TensorProduct.leftAlgebra`, `a ↦ a ⊗ 1`, in every importer, and Mathlib's
`Algebra.TensorProduct.algebraMap_apply` failed to typecheck.

These examples, in a module importing `GaloisAction`, check that the default is Mathlib's again,
and that the right-linear API of `GaloisAction` is still available once an importer activates
`rightAlgebra` itself.
-/

open scoped TensorProduct

section Default

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- The default `K`-algebra structure on `K ⊗[k] K` is Mathlib's left one. -/
example (a : K) : algebraMap K (K ⊗[k] K) a = a ⊗ₜ[k] 1 :=
  Algebra.TensorProduct.algebraMap_apply a

/-- The same, through `rw`. -/
example (a : K) : algebraMap K (K ⊗[k] K) a = a ⊗ₜ[k] 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

end Default

section RightLinear

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {k K kbar : Type} [Field k] [Field K] [Field kbar] [Algebra k K] [Algebra k kbar]

/-- With `rightAlgebra` activated, the `K`-structure on `kbar ⊗[k] K` is the right one. -/
example (a : K) : algebraMap K (kbar ⊗[k] K) a = 1 ⊗ₜ[k] a :=
  Algebra.TensorProduct.right_algebraMap_apply a

/-- The Galois action commutes with the right `K`-action. -/
example [IsGalois k kbar] : SMulCommClass (kbar ≃ₐ[k] kbar) K (kbar ⊗[k] K) := inferInstance

/-- The invariants of the Galois action are the image of `K`, through the right factor. -/
example [IsGalois k kbar] : Algebra.IsInvariant K (kbar ⊗[k] K) (kbar ≃ₐ[k] kbar) :=
  inferInstance

end RightLinear
