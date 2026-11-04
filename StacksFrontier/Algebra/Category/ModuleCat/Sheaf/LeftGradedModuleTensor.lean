module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedBimoduleTensorAction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleBimodule

/-!
# The relative tensor product of two left graded modules over a commutative graded algebra

Let `O` be a sheaf of commutative rings on a site, let `A` be a sheaf of graded `O`-algebras
whose multiplication is commutative, and let `ℳ` and `𝒩` be left graded `A`-modules. This file
makes `ℳ ⊗_A 𝒩` a left graded `A`-module. Its degree `n` is degree `n` of the graded relative
tensor product of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedRelativeTensor.lean`, and a
homogeneous section `a` of `A` acts on `x ⊗ y` by `x ⊗ (a y)`.

This is the tensor product in property (6) of Tag 01O7, which speaks of `(ℳ ⊗_𝒜 𝒩)~` for two
left graded modules over the graded algebra `𝒜` of Situation 01NN.

## Main definitions

* `SheafOfModules.LeftGradedModule.relativeTensor` is **the left graded `A`-module
  `ℳ ⊗_A 𝒩`** of two left graded `A`-modules over a commutative `A`.

## Main results

* `SheafOfModules.LeftGradedModule.relativeTensor_piece`: **degree `n` of `ℳ ⊗_A 𝒩` is degree
  `n` of the graded relative tensor product of `ℳ`, read as a right graded module, with `𝒩`.**
* `SheafOfModules.LeftGradedModule.relativeTensor_smul_tmul`: **the action on a local section
  `x ⊗ y` is `x ⊗ (a y)`.**
* `SheafOfModules.LeftGradedModule.toGradedBimodule_toLeftGradedModule`: the left graded module
  underlying the bimodule read off a left graded module is that same left graded module, on the
  nose. This is what makes the degree-piece statement above be about `𝒩` itself rather than
  about a round trip of it.

## Implementation notes

The construction composes the following existing ones.

* `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedRelativeTensor.lean` forms `P ⊗_A N` for
  `P` a *right* graded module and `N` a *left* one, as a family of sheaves of modules indexed by
  the degree, with no action on it.
* `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedBimoduleTensorAction.lean` puts a right
  `B`-action back on that family, assembling it into a right graded `B`-module
  `SheafOfModules.RelativeTensor.gradedTensorRight`, but only when the right-hand factor is a
  graded `(A, B)`-bimodule: the action is `x ⊗ y ↦ x ⊗ (y b)`, and it respects the `A`-balancing
  because the bimodule's two actions commute.
* `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LeftGradedModuleBimodule.lean` supplies, from
  commutativity of `A`, both of the missing readings of a left graded module: as a right graded
  module, for the left-hand factor, and as a graded `(A, A)`-bimodule, for the right-hand one.
* `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleLeftRight.lean` reads the right
  graded module that comes out back as a left graded module.

The degree-piece identification is definitional, not a transport: the pieces and the action of
the bimodule read off `𝒩` are those of `𝒩`, its laws are proofs of the same propositions, and
`SheafOfModules.RelativeTensor.gradedTensorRight_piece` and
`SheafOfModules.GradedModule.toLeftGradedModule_piece` are themselves `rfl`. The whole chain is
therefore `rfl`, and no `eqToHom` appears anywhere below.

The action on `ℳ ⊗_A 𝒩` is the one carried by the second factor. Over a commutative `A` the
action through the first factor agrees with it, but that comparison is not proved here and is not
needed: a left graded module asks for one action, not for two.

The module universe is written `max u v`, as in the two files the construction goes through: an
internal hom of presheaves of modules has sections indexed by the morphisms of the site, so the
module universe and the universes of the site are related in exactly that one place.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 0FR5](https://stacks.math.columbia.edu/tag/0FR5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t v u

namespace SheafOfModules

namespace LeftGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  {A : GradedAlgebra.{t, max u v} (toRingCat J Osharp)}
  (ℳ 𝒩 : LeftGradedModule.{t, max u v, max u v} A)

/-- **The left graded module underlying the graded `(A, A)`-bimodule read off a left graded
module is that same left graded module**, on the nose: the pieces and the action are those of the
module it was built from, and the laws are proofs of one and the same proposition. -/
theorem toGradedBimodule_toLeftGradedModule (hcomm : A.MulComm) :
    (𝒩.toGradedBimodule hcomm).toLeftGradedModule = 𝒩 := rfl

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- **The relative tensor product `ℳ ⊗_A 𝒩` of two left graded modules** over a sheaf of graded
algebras whose multiplication is commutative, as a left graded `A`-module: degree `n` is degree
`n` of the graded relative tensor product of `ℳ`, read as a right graded module, with `𝒩`, and a
homogeneous section `a` of `A` acts on `x ⊗ y` by `x ⊗ (a y)`. -/
noncomputable def relativeTensor (hcomm : A.MulComm) :
    LeftGradedModule.{t, max u v, max u v} A :=
  (RelativeTensor.gradedTensorRight (ℳ.toGradedModule hcomm)
    (𝒩.toGradedBimodule hcomm)).toLeftGradedModule hcomm

/-- **Degree `n` of `ℳ ⊗_A 𝒩` is degree `n` of the graded relative tensor product** of `ℳ`,
read as a right graded module, with `𝒩`. -/
@[simp]
theorem relativeTensor_piece (hcomm : A.MulComm) (n : ℤ) :
    (ℳ.relativeTensor 𝒩 hcomm).piece n =
      RelativeTensor.gradedTensor (ℳ.toGradedModule hcomm) 𝒩 n := rfl

/-- **The left action of `a` on a local section `x ⊗ y` of `ℳ ⊗_A 𝒩` is `x ⊗ (a y)`.** The two
sides lie in the pieces of the degrees `i + n` and `n + i`, which agree only propositionally, so
the statement is heterogeneous, as the action laws of a left graded module already are. -/
theorem relativeTensor_smul_tmul (hcomm : A.MulComm) (n i : ℤ) (p : TensorIndex n) (U : Cᵒᵖ)
    (x : ((ℳ.toGradedModule hcomm).piece p.1.1).val.obj U) (y : (𝒩.piece p.1.2).val.obj U)
    (a : (A.piece i).val.obj U) :
    HEq ((ℳ.relativeTensor 𝒩 hcomm).smul i n U a
        (RelativeTensor.tmul (ℳ.toGradedModule hcomm) 𝒩 n p U x y))
      (RelativeTensor.tmul (ℳ.toGradedModule hcomm) 𝒩 (n + i)
        (RelativeTensor.actIndex p i (n + i) rfl) U x
        ((𝒩.toGradedModule hcomm).smul p.1.2 i U y a)) :=
  (GradedModule.toLeftGradedModule_smul_heq _ hcomm i n U a _).trans
    (heq_of_eq (RelativeTensor.gradedTensorRight_smul_tmul (ℳ.toGradedModule hcomm)
      (𝒩.toGradedBimodule hcomm) n i p U x y a))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The second factor of the action on `x ⊗ y`, which the statement above writes with the
exchanged action of `𝒩`, is the left action of `𝒩`. Composed with
`SheafOfModules.LeftGradedModule.relativeTensor_smul_tmul` this says that `a` acts on `x ⊗ y` by
`x ⊗ (a y)` with `a y` the action of `𝒩` itself; it is stated separately because the two lie in
the pieces of the degrees `q + i` and `i + q`, and only the first is the degree of the summand
`x ⊗ (a y)` belongs to. -/
theorem relativeTensor_tmul_factor_heq (hcomm : A.MulComm) (q i : ℤ) (U : Cᵒᵖ)
    (y : (𝒩.piece q).val.obj U) (a : (A.piece i).val.obj U) :
    HEq ((𝒩.toGradedModule hcomm).smul q i U y a) (𝒩.smul i q U a y) :=
  𝒩.toGradedModule_smul_heq hcomm q i U y a

end Sheafify

end LeftGradedModule

end SheafOfModules

end
