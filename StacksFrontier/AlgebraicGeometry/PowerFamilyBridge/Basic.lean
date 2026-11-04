module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.InverseSection.Reindex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence

/-!
# The two constructions of the tensor powers of an invertible module agree, in every degree

Stacks Tag 01CU is realised by two families of tensor powers, over two different classes
realising Stacks Tag 01CS.

* `Stacks.SheafOfModules.TensorPower.tensorPower`, which carries the Tag 01CU attribute, is the
  image of the structure sheaf under the `n`-th power of the autoequivalence "tensor on the right
  by `L`". Its hypothesis is that `(Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj L` is
  an equivalence, supplied from `Stacks.SheafOfModules.IsInvertible`.
* `AlgebraicGeometry.SheafOfModules.tensorPow` is the iterated tensor product of `L`, with the
  negative powers given by a *chosen* tensor inverse. Its hypothesis is
  `AlgebraicGeometry.SheafOfModules.IsInvertible`. This is the family the ampleness theory of
  Tags 01PS, 01VH, 01VN and 0891 is written over, through `Stacks.Ample.tensorPowModule`.

Neither hypothesis is found by instance search from the other, so without a bridge Tag 01CU's
powers cannot even be *written down* for a module invertible in the ampleness theory's sense.
This file supplies that bridge, and an isomorphism between the two families in every degree.

## Main definitions

* `Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow`: **the comparison of the two families, for
  every `n : ℤ`**, including the negative degrees.
* `Stacks.PowerFamilyBridge.natIso`, `Stacks.PowerFamilyBridge.negIso`: the nonnegative and
  nonpositive halves, from which it is assembled.

## Main results

* `Stacks.PowerFamilyBridge.instIsInvertible`: the bridge *instance*. An
  `AlgebraicGeometry.SheafOfModules.IsInvertible` module is
  `Stacks.SheafOfModules.IsInvertible`, so Tag 01CU's tensor powers and the whole Tag 01CU API
  apply to it with no local `letI` and no explicit argument.

## Implementation notes

**The negative degrees come from full faithfulness, not from a second addition law.** Both
families have a successor comparison in every integer degree —
`Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso`, which is
`Stacks.Equivalence.powSuccIso`, and `AlgebraicGeometry.SheafOfModules.tensorPowSuccIso`, which
is the chosen inverse's. Only these two comparisons are used, and no addition law
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)`, so the usual argument "the `(-n)`-th power is a tensor inverse
of the `n`-th, and tensor inverses are unique" is not the one run here.

What makes the descent to negative degrees work instead is that the successor comparison is
`⊗ L` applied to the previous power, and `⊗ L` is an *equivalence*, hence fully faithful.
So from an isomorphism of the `(n+1)`-st powers one recovers an isomorphism of the `n`-th powers
by `CategoryTheory.Functor.preimageIso`. The two statements
`Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso` and
`AlgebraicGeometry.SheafOfModules.tensorPowSuccIso` are phrased in the
`Stacks.SheafOfModules.Tensor.sheafTensor` and the monoidal `⊗` spellings respectively;
`AlgebraicGeometry.SheafOfModules.tensorIso` converts, and
`((Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj L).obj` is the former spelling
definitionally, which is why no bridge is needed at that step.

**Every exponent equation is given by an explicit `show`.** Left to be inferred from the
surrounding composition the exponent is a metavariable and `push_cast` reports being stuck on
it.

**The two halves are stated at `(k : ℤ)` and `-(k : ℤ)` for `k : ℕ`** and assembled by matching
on `Int.ofNat`/`Int.negSucc`, which is the shape `Stacks.TensorPowers.intTensorPow` is itself
defined by.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.PowerFamilyBridge

attribute [local implicit_reducible] structureSheaf
  Stacks.SheafOfModules.TensorSheafification.sheafify
  Stacks.SheafOfModules.Tensor.sheafTensor

attribute [local irreducible] PresheafOfModules.sheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-! ### The bridge instance -/

/-- **The two classes realising Stacks Tag 01CS, as an instance.** A module invertible in the
sense `AlgebraicGeometry.SheafOfModules.tensorPow` and the ampleness theory use is invertible in
the sense Tag 01CU's `Stacks.SheafOfModules.TensorPower.tensorPower` asks for. This is
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`, declared as an
instance so that instance search crosses the gap on its own: with it,
`Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor` fires and Tag 01CU's powers
become writable under the ampleness theory's hypothesis alone. -/
instance instIsInvertible [AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L] :
    Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 L :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible 𝒪 h𝒪 L).mpr
    inferInstance

/-- The same bridge read the other way: a module invertible in the sense Tag 01CU's tensor
powers are stated with is invertible in the sense the ampleness theory uses. Deliberately *not*
an instance — with `Stacks.PowerFamilyBridge.instIsInvertible` the pair would be a cycle for
instance search. The instance is given in the direction that lets Tag 01CU's powers be written
under the ampleness theory's hypothesis; this direction is supplied by hand where a consumer
starts from Tag 01CU's hypothesis instead. -/
theorem algebraicGeometryIsInvertible [Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible 𝒪 h𝒪 L).mp
    inferInstance

/-! ### The comparison of the two families -/

open AlgebraicGeometry.SheafOfModules Stacks.SheafOfModules.TensorPower
open Stacks.InverseSection (tensorPowReindexIso)

variable [AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

/-- **The two tensor-power families agree in every nonnegative degree.** By induction: in degree
zero both are the structure sheaf, and the step tensors the previous comparison with `L`, using
the successor comparison of each family. -/
def natIso : (k : ℕ) → tensorPower 𝒪 h𝒪 L (k : ℤ) ≅ tensorPow 𝒪 h𝒪 L (k : ℤ)
  | 0 =>
      tensorPowerReindex 𝒪 h𝒪 L (show ((0 : ℕ) : ℤ) = 0 by norm_num) ≪≫
        eqToIso (tensorPower_zero 𝒪 h𝒪 L) ≪≫ (tensorPowZeroIso 𝒪 h𝒪 L).symm ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L (show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num)
  | (k + 1) =>
      tensorPowerReindex 𝒪 h𝒪 L (show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring) ≪≫
        (tensorPowerSuccIso 𝒪 h𝒪 L (k : ℤ)).symm ≪≫
        (tensorIso 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (k : ℤ)) L).symm ≪≫
        whiskerRightIso (natIso k) L ≪≫
        (tensorPowSuccIso 𝒪 h𝒪 L (k : ℤ)).symm ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L
          (show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring)

/-- **The two tensor-power families agree in every nonpositive degree.** The step down is the
successor comparison of each family read backwards: it exhibits both sides as `⊗ L` applied to
the next power down, and `⊗ L` is fully faithful, so
`CategoryTheory.Functor.preimageIso` returns the comparison one degree lower. -/
def negIso : (k : ℕ) → tensorPower 𝒪 h𝒪 L (-(k : ℤ)) ≅ tensorPow 𝒪 h𝒪 L (-(k : ℤ))
  | 0 =>
      tensorPowerReindex 𝒪 h𝒪 L (show -((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) by norm_num) ≪≫
        natIso 𝒪 h𝒪 L 0 ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L (show ((0 : ℕ) : ℤ) = -((0 : ℕ) : ℤ) by norm_num)
  | (k + 1) =>
      tensorPowerReindex 𝒪 h𝒪 L
          (show -((k + 1 : ℕ) : ℤ) = -((k : ℤ) + 1) by push_cast; ring) ≪≫
        Functor.preimageIso
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).flip.obj L)
          (tensorPowerSuccIso 𝒪 h𝒪 L (-((k : ℤ) + 1)) ≪≫
            tensorPowerReindex 𝒪 h𝒪 L (show -((k : ℤ) + 1) + 1 = -(k : ℤ) by ring) ≪≫
            negIso k ≪≫
            tensorPowReindexIso 𝒪 h𝒪 L (show -(k : ℤ) = -((k : ℤ) + 1) + 1 by ring) ≪≫
            tensorPowSuccIso 𝒪 h𝒪 L (-((k : ℤ) + 1)) ≪≫
            tensorIso 𝒪 h𝒪 (tensorPow 𝒪 h𝒪 L (-((k : ℤ) + 1))) L) ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L
          (show -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring)

/-- **The two constructions of the integer tensor powers of an invertible sheaf of modules
agree, in every integer degree.** On the left, Stacks Tag 01CU's
`Stacks.SheafOfModules.TensorPower.tensorPower`, the image of the structure sheaf under a power
of the autoequivalence "tensor by `L`"; on the right,
`AlgebraicGeometry.SheafOfModules.tensorPow`, the iterated tensor product, whose negative powers
use a chosen tensor inverse.

The hypothesis is the ampleness theory's invertibility class alone; Tag 01CU's own hypothesis is
produced by `Stacks.PowerFamilyBridge.instIsInvertible`. -/
def tensorPowerIsoTensorPow (n : ℤ) : tensorPower 𝒪 h𝒪 L n ≅ tensorPow 𝒪 h𝒪 L n :=
  match n with
  | Int.ofNat k =>
      tensorPowerReindex 𝒪 h𝒪 L (show (Int.ofNat k) = ((k : ℕ) : ℤ) by rfl) ≪≫
        natIso 𝒪 h𝒪 L k ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L (show ((k : ℕ) : ℤ) = (Int.ofNat k) by rfl)
  | Int.negSucc k =>
      tensorPowerReindex 𝒪 h𝒪 L
          (show (Int.negSucc k) = -((k + 1 : ℕ) : ℤ) by
            rw [Int.negSucc_eq]; push_cast; ring) ≪≫
        negIso 𝒪 h𝒪 L (k + 1) ≪≫
        tensorPowReindexIso 𝒪 h𝒪 L
          (show -((k + 1 : ℕ) : ℤ) = (Int.negSucc k) by
            rw [Int.negSucc_eq]; push_cast; ring)

end Stacks.PowerFamilyBridge

end
