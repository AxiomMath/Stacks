module

public import StacksFrontier.RingTheory.Dualizing.BaseBimodule
public import StacksFrontier.RingTheory.Dualizing.DerivedHomPerfectTensor

/-!
# The tensor factor of Stacks 0BZE, normalized

Stacks 0BZE, as `Dualizing.exists_derivedHom_iso_derivedTensor` proves it, produces a differential
graded `(R, A)`-bimodule `M` with `RHom_R(A, -) ≅ - ⊗_R^𝐋 M`, and the bimodule it produces is the
tensor factor `N ⊗_E A` of a Tate resolution. This file restates that conclusion with the bimodule
normalized: the tensor factor may always be taken to be `Dualizing.baseBimodule` of an ordinary
right differential graded `A`-module, so the left `R`-action on it is scalar multiplication.

The normalization costs nothing, because by `Dualizing.bimodule_eq_baseBimodule` a differential
graded bimodule over the base ring in degree zero *equals* the one attached to its right module.
It matters because it removes a step that the chapter had recorded as missing. The docstring of
`Dualizing.InvertibleKernel.exists_derivedHom_iso_derivedTensor_factor_class_of_invertible_ker`
used to argue that passing from the bimodule shape of Stacks 0BZE to the derived change-of-rings
shape of Stacks 06Y6 needs a bimodule map from the Tate factor to the conormal inverse shift,
because `Dualizing.derivedTensorBimoduleFunctor` "tensors over `R` using the left `R`-action of
`M`, which for the Tate factor `N_E ⊗_E A` is not the one induced by `R → A`". That reason does
not hold: there is only one left action of the base ring in degree zero on any complex, and it is
the one induced by the structure homomorphism. So no bimodule map has to be produced, and no
appeal to the second assertion of Stacks 09S3 is needed to move between the two factors.

## Main results

* `Dualizing.exists_derivedHom_iso_derivedTensor_baseBimodule` — **Stacks 0BZE with the tensor
  factor normalized**: for `A` perfect over `R`, derived coextension of scalars along `R → A` is
  derived tensoring over `R` with `Dualizing.baseBimodule` of an ordinary right differential graded
  module over `A` placed in degree zero.

## Implementation notes

What still separates this from the derived change-of-rings shape of Stacks 06Y6 — the shape
`Stacks0BZE.bundle` and the chapter's carriers of Stacks 0BZE are stated in — is the chain-level
comparison: an identification of the differential graded relative tensor product
`M ⊗_{baseAlgebra R} Dualizing.baseBimodule _ X` with the ordinary total tensor complex of the
underlying complexes, as a complex of `A`-modules. Given that identification,
`CochainComplex.DerivedTensor.exists_derivedTensorNatTrans_isIso_of_quasiIso` accepts any functor
carrying a left-derived counit into `extendScalarsLarge f ⋙ tensorRightLarge L`, and the
comparison with the canonical bundle follows with no further input.

Universes: the differential graded chapter of this tree is single-universe (Tag 09JJ), so the
statement is at module universe equal to the ring universe. Transport to an arbitrary module
universe is `StacksDraft.DerivedRingEquivIso.derivedHomRingEquivIso` applied to
`ULift.ringEquiv`.

## References

* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 09S3](https://stacks.math.columbia.edu/tag/09S3)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded DifferentialGradedModule

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **Stacks 0BZE with the tensor factor normalized.** For `A` perfect as an `R`-module, derived
coextension of scalars `RHom_R(A, -) : D(R) ⥤ D(A)` is derived tensoring over `R` with
`Dualizing.baseBimodule` of an ordinary right differential graded module over `A` placed in degree
zero; in particular the left `R`-action on the tensor factor is scalar multiplication, which is
the action induced by the structure homomorphism.

The bimodule `Dualizing.exists_derivedHom_iso_derivedTensor` produces is already of this form, by
`Dualizing.bimodule_eq_baseBimodule`, so the normalization is a rewrite along an equality of
bimodules and assumes nothing beyond Stacks 0BZE itself. -/
theorem exists_derivedHom_iso_derivedTensor_baseBimodule
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hperf : StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := R) A) :
    ∃ X : DifferentialGradedModule (DifferentialGradedAlgebra.degreeZero R A),
      Nonempty (Dualizing.derivedHom.{u, u, u} (algebraMap R A) ≅
        derivedTensorBimoduleFunctor (baseBimodule _ X)) := by
  obtain ⟨M, ⟨e⟩, -⟩ := exists_derivedHom_iso_derivedTensor hperf
  refine ⟨M.rightModule, ⟨e ≪≫ ?_⟩⟩
  exact eqToIso (congrArg derivedTensorBimoduleFunctor
    (bimodule_eq_baseBimodule (DifferentialGradedAlgebra.degreeZero R A) M))

end Dualizing

end
