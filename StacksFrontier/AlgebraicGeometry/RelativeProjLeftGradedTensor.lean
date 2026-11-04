module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleTensor
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjQuasicoherent

/-!
# The tensor product of two left graded modules in Situation 01NN

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LeftGradedModuleTensor.lean` forms the relative
tensor product `ℳ ⊗_A 𝒩` of two left graded modules over a sheaf of graded algebras `A` whose
multiplication is commutative, on a site whose structure sheaf is presented as the sheaf of rings
underlying a sheaf of commutative rings. This file instantiates it at
`Stacks.RelativeProj.Situation`, the relative `Proj` situation of Tag 01NN, whose graded algebra
`𝒜` lives on the opens of a scheme and carries exactly that commutativity as its `mul_comm`
field.

This is what property (6) of Tag 01O7 needs in order to be stateable: that property speaks of
`(ℳ ⊗_𝒜 𝒩)~` for two left graded `𝒜`-modules.

## Main definitions

* `Stacks.RelativeProj.Situation.leftGradedTensor` is **the left graded `𝒜`-module `ℳ ⊗_𝒜 𝒩`**
  of two left graded `𝒜`-modules in Situation 01NN.

## Main results

* `Stacks.RelativeProj.Situation.leftGradedTensor_piece`: **degree `n` of `ℳ ⊗_𝒜 𝒩` is degree
  `n` of the graded relative tensor product** of `ℳ`, read as a right graded module, with `𝒩`.

## Implementation notes

The instantiation is not automatic and is the content of this file: the general construction asks
for the module universe to be the join of the universes of the site, and for the base to be the
sheaf of rings underlying a sheaf of commutative rings. In Situation 01NN the site is the opens
of a scheme over `Type u` with morphisms in `Type u`, so that join is `u` and the module universe
`u` of the situation's own graded modules is the right one; and the situation's base is the
structure sheaf of the scheme, which is already presented in that form. Both facts are needed and
neither is forced by the statement, so they are recorded here by the declarations type-checking.

The associated module `(ℳ ⊗_𝒜 𝒩)~` on the relative `Proj` needs quasi-coherence of the pieces of
the tensor product; that is proved in
`StacksFrontier/AlgebraicGeometry/RelativeProjLeftGradedTensorQcoh.lean`, where
`Stacks.RelativeProj.Situation.tensorModuleSheaf` is `(ℳ ⊗_𝒜 𝒩)~`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u}) (ℳ 𝒩 : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)

/-- **The relative tensor product `ℳ ⊗_𝒜 𝒩` of two left graded `𝒜`-modules** in Situation 01NN,
as a left graded `𝒜`-module. The commutativity of `𝒜` that the construction needs is the
situation's own `mul_comm` field. -/
noncomputable def leftGradedTensor : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra :=
  ℳ.relativeTensor 𝒩 s.mul_comm

/-- **Degree `n` of `ℳ ⊗_𝒜 𝒩` is degree `n` of the graded relative tensor product** of `ℳ`,
read as a right graded `𝒜`-module, with `𝒩`. -/
@[simp]
theorem leftGradedTensor_piece (n : ℤ) :
    (s.leftGradedTensor ℳ 𝒩).piece n =
      SheafOfModules.RelativeTensor.gradedTensor (ℳ.toGradedModule s.mul_comm) 𝒩 n := rfl

end Stacks.RelativeProj.Situation

end
