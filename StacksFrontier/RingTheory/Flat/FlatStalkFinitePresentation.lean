module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Descending finiteness of a module along a flat local homomorphism

Stacks 05I7 says that a finite type quasi-coherent module which is flat over the base at a point
of a morphism locally of finite presentation has a finitely presented stalk there. Its proof has
two halves. The geometric half is Stacks 05I5: after an elementary étale neighbourhood of the
image point, the pullback of the module is finitely presented near the point. The algebraic half
is the descent back down: the ring map from the stalk at the point to the stalk of the pullback
at the point above it is flat and local, so finite presentation of the pullback's stalk over the
upper ring forces finite presentation of the original stalk over the lower one.

This file supplies that algebraic half. The two inputs are already in the library: a flat local
homomorphism of local rings is faithfully flat (Stacks 00HR,
`Module.FaithfullyFlat.of_flat_of_isLocalHom`), and finite presentation of a module descends
along a faithfully flat ring map (Stacks 03C4 part (2),
`Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat`). What is added here is the
composite in the shape the stalk argument uses, namely with the upper module given abstractly
together with a proof that it is the base change, rather than as a literal tensor product: the
stalk of a pullback is not syntactically a tensor product.

## Main results

* `Module.FinitePresentation.of_isBaseChange_of_flat_of_isLocalHom` and
  `Module.FinitePresentation.of_tensorProduct_of_flat_of_isLocalHom` descend finite presentation
  along a flat local homomorphism of local rings.
* `Module.Finite.of_isBaseChange_of_flat_of_isLocalHom` and
  `Module.Finite.of_tensorProduct_of_flat_of_isLocalHom` do the same for finite generation,
  which is Stacks 03C4 part (1) in the same shape.

## Implementation notes

The hypothesis that the homomorphism is local is `IsLocalHom (algebraMap R T)` on two rings each
carrying `IsLocalRing`; no residue field condition is imposed, since faithful flatness only needs
the maximal ideal to pull back into the maximal ideal.

## References

* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 03C4](https://stacks.math.columbia.edu/tag/03C4)
* [Stacks Project, Tag 00HR](https://stacks.math.columbia.edu/tag/00HR)
-/

@[expose] public section

open scoped TensorProduct

universe u v w t

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] {T : Type v} [CommRing T] [IsLocalRing T]
  [Algebra R T] [Module.Flat R T] [IsLocalHom (algebraMap R T)]
  {M : Type w} [AddCommGroup M] [Module R M]

/-- **Finite generation descends along a flat local homomorphism.** If `R → T` is a flat local
homomorphism of local rings and the base change of an `R`-module `M` to `T` is a finite
`T`-module, then `M` is a finite `R`-module.

This is Stacks 03C4 part (1) together with Stacks 00HR. -/
public theorem Finite.of_isBaseChange_of_flat_of_isLocalHom {N : Type t} [AddCommGroup N]
    [Module R N] [Module T N] [IsScalarTower R T N] (f : M →ₗ[R] N) (h : IsBaseChange T f)
    [Module.Finite T N] : Module.Finite R M := by
  have : Module.FaithfullyFlat R T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Module.Finite T (T ⊗[R] M) := Module.Finite.equiv h.equiv.symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat T

/-- **Finite generation descends along a flat local homomorphism**, for the base change written
as a tensor product. -/
public theorem Finite.of_tensorProduct_of_flat_of_isLocalHom
    [Module.Finite T (T ⊗[R] M)] : Module.Finite R M :=
  Finite.of_isBaseChange_of_flat_of_isLocalHom
    (TensorProduct.mk R T M 1) (TensorProduct.isBaseChange R M T)

/-- **Finite presentation descends along a flat local homomorphism.** If `R → T` is a flat local
homomorphism of local rings and the base change of an `R`-module `M` to `T` is a finitely
presented `T`-module, then `M` is a finitely presented `R`-module.

This is the algebraic half of Stacks 05I7: Stacks 03C4 part (2) together with Stacks 00HR. The
upper module is given abstractly with a proof `h` that it is the base change, because the stalk
of a pullback is not syntactically a tensor product. -/
public theorem FinitePresentation.of_isBaseChange_of_flat_of_isLocalHom {N : Type t}
    [AddCommGroup N] [Module R N] [Module T N] [IsScalarTower R T N] (f : M →ₗ[R] N)
    (h : IsBaseChange T f) [Module.FinitePresentation T N] : Module.FinitePresentation R M :=
  have : Module.FaithfullyFlat R T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat f h

/-- **Finite presentation descends along a flat local homomorphism**, for the base change written
as a tensor product. -/
public theorem FinitePresentation.of_tensorProduct_of_flat_of_isLocalHom
    [Module.FinitePresentation T (T ⊗[R] M)] : Module.FinitePresentation R M :=
  FinitePresentation.of_isBaseChange_of_flat_of_isLocalHom
    (TensorProduct.mk R T M 1) (TensorProduct.isBaseChange R M T)

end Module

end
