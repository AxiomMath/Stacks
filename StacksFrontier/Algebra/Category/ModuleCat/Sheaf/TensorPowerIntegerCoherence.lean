module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleBraidingSelf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCommutativity

/-!
# The coherent multiplication of the integer tensor powers of an invertible sheaf of modules

Let `O` be a sheaf of commutative rings on a site and let `L` be an invertible sheaf of
`O`-modules in the sense of Tag 01CS.
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPower.lean` defines the integer tensor
powers `L^{⊗ n}` and the successor comparison `L^{⊗ n} ⊗_O L ≅ L^{⊗ (n + 1)}`, and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerCommutativity.lean` packages the
multiplication isomorphisms `L^{⊗ n} ⊗_O L^{⊗ m} ≅ L^{⊗ (n + m)}` asserted by Tag 01CU, with
the unit, associativity and commutativity constraints whose "formulation is omitted" there, into
the structure `Stacks.SheafOfModules.TensorPower.TensorPowerCoherence`, and proves that one
exists. This file *chooses* one and names its multiplication, so that the five coherence laws
become statements about a single isomorphism rather than about a bundled datum.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.tensorPowerCoherence`: a choice of coherent multiplication
  data, from `tensorPowerCoherence_exists`.
* `Stacks.SheafOfModules.TensorPower.coherentMulIso`: the multiplication isomorphism
  `L^{⊗ n} ⊗_O L^{⊗ m} ≅ L^{⊗ (n + m)}` of that chosen datum, for `n m : ℤ`.

## Main results

* `coherentMulIso_zero_left`, `coherentMulIso_zero_right`, `coherentMulIso_one_right`,
  `coherentMulIso_assoc` and `coherentMulIso_comm`: its five coherence laws, stated against the
  *fixed* structural isomorphisms `Stacks.SheafOfModules.Invertible.tensorProduct…` of the sheaf
  tensor product. Those agree with the `tensorSheaf…` spelling of the coherence structure's own
  fields definitionally, so each law is the corresponding field.
* `Stacks.SheafOfModules.TensorPower.tensorSheafBraiding_tensorPower_self`: a tensor power of an
  invertible sheaf braids trivially with itself, read off from the commutativity law.

## Implementation notes

`coherentMulIso` is *not*
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerMultiplication.lean`'s
`Stacks.SheafOfModules.TensorPower.tensorPowerMulIso`. The latter is built directly from
`CategoryTheory.Equivalence.powAdd`, and only its degree-`(n, 0)` and degree-`(n, 1)`
normalisations are available in that spelling: the tensor powers are built from
`tensorRightFunctor` while `Stacks.MonoidalCategory.mul`, which carries associativity and
commutativity, is built from `tensorRight`, and the chosen quasi-inverses those two use at
negative exponents have no common normal form. `coherentMulIso` is the multiplication of a
coherence datum, so it carries all five laws; it is the one to use when associativity or
commutativity of the multiplication is needed.

`Stacks.SheafOfModules.Invertible.tensorPowerMulIso` in
`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Basic.lean` is a third, earlier
multiplication, defined for natural-number exponents only and through a `PowerSystem` rather
than through the monoidal structure.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Choose the canonical coherent multiplication data on tensor powers. -/
noncomputable def tensorPowerCoherence
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] : TensorPowerCoherence O hO L :=
  Classical.choice (tensorPowerCoherence_exists O hO L)

/-- The multiplication isomorphism of the chosen coherent multiplication data. -/
noncomputable def coherentMulIso
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((tensorPower O hO L n))).obj ((tensorPower O hO L m))) ≅
      tensorPower O hO L (n + m) :=
  (tensorPowerCoherence O hO L).mulIso n m

/-- Multiplication by the zeroth power on the left is the canonical unitor. -/
@[simp↓]
theorem coherentMulIso_zero_left
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℤ) :
    coherentMulIso O hO L 0 n ≪≫ tensorPowerReindex O hO L (Int.zero_add n) =
      Invertible.tensorProductLeftUnitor O hO (tensorPower O hO L n) :=
  (tensorPowerCoherence O hO L).mul_zero_left n

/-- Multiplication by the zeroth power on the right is the canonical unitor. -/
@[simp↓]
theorem coherentMulIso_zero_right
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℤ) :
    coherentMulIso O hO L n 0 ≪≫ tensorPowerReindex O hO L (Int.add_zero n) =
      Invertible.tensorProductRightUnitor O hO (tensorPower O hO L n) :=
  (tensorPowerCoherence O hO L).mul_zero_right n

/-- Multiplication by the first power is the comparison induced by the
successor step in the defining integer iteration. -/
@[simp↓]
theorem coherentMulIso_one_right
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℤ) :
    coherentMulIso O hO L n 1 =
      Invertible.tensorProductIso O hO (Iso.refl _) (tensorPowerOneIso O hO L) ≪≫
        tensorPowerSuccIso O hO L n :=
  (tensorPowerCoherence O hO L).mul_one_right n

set_option maxHeartbeats 1000000 in
/-- Multiplication of powers is associative for the canonical tensor associator. -/
theorem coherentMulIso_assoc
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m k : ℤ) :
    Invertible.tensorProductIso O hO (coherentMulIso O hO L n m) (Iso.refl _) ≪≫
        coherentMulIso O hO L (n + m) k =
      Invertible.tensorProductAssociator O hO
          (tensorPower O hO L n) (tensorPower O hO L m) (tensorPower O hO L k) ≪≫
        Invertible.tensorProductIso O hO (Iso.refl _) (coherentMulIso O hO L m k) ≪≫
        coherentMulIso O hO L n (m + k) ≪≫
        tensorPowerReindex O hO L (Int.add_assoc n m k).symm :=
  (tensorPowerCoherence O hO L).mul_assoc n m k

/-- Multiplication of powers is commutative for the canonical tensor braiding. -/
theorem coherentMulIso_comm
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℤ) :
    coherentMulIso O hO L n m =
      Invertible.tensorProductBraiding O hO (tensorPower O hO L n) (tensorPower O hO L m) ≪≫
        coherentMulIso O hO L m n ≪≫
        tensorPowerReindex O hO L (Int.add_comm m n) :=
  (tensorPowerCoherence O hO L).mul_comm n m

/-- **The braiding of a tensor power of an invertible sheaf of modules with itself is the
identity.** The commutativity law of the coherent multiplication in degrees `(n, n)` says the
multiplication is unchanged by precomposing with that braiding, and
`tensorSheafBraiding_self_eq_refl_of_commutativity` turns that into the triviality of the
braiding itself. -/
theorem tensorSheafBraiding_tensorPower_self
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℤ) :
    tensorSheafBraiding O hO (tensorPower O hO L n) (tensorPower O hO L n) = Iso.refl _ :=
  tensorSheafBraiding_self_eq_refl_of_commutativity O hO L n (coherentMulIso O hO L n n)
    (coherentMulIso_comm O hO L n n)

end Stacks.SheafOfModules.TensorPower

end
