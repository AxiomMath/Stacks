module

public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.IntegerSucc
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerMul

/-!
# The snake hypothesis holds for the chosen tensor inverse of an invertible sheaf of modules

`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/IntegerSucc.lean` proves the zig-zag identity and
the successor equation for the integer addition law at a negative second exponent from one
hypothesis: that the two inverse laws `TensorInverse.mulIso` and `TensorInverse.mulIso'` of the
base object are *snake-compatible*.  That hypothesis cannot be an instance there — the abstract
powers are built from arbitrary data in a monoidal category with no braiding — but for the tensor
inverse that the tensor powers of an invertible sheaf of modules actually use it is free.

`AlgebraicGeometry.SheafOfModules.tensorInverse` is
`Stacks.TensorPowers.tensorInverseOfTensorLeft`, whose second inverse law is the first one
precomposed with the braiding *by definition*.  `Stacks.Monoidal.braiding_eval_snake` turns that
into snake-compatibility given the triviality of the self-braiding of the sheaf, which is
`Stacks.SelfBraidingInvertible.hasTrivialSelfBraiding`.  So the hypothesis is discharged by
instance search and the results of the sibling file are unconditional for sheaves of modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.tensorInverse_snake`: **the two inverse laws of the chosen
  tensor inverse of an invertible sheaf of modules are snake-compatible.**
* `AlgebraicGeometry.SheafOfModules.tensorPow_predIso_zigzag` and
  `AlgebraicGeometry.SheafOfModules.tensorPow_subNatIso_succ`: the zig-zag identity and the
  successor equation at a negative second exponent, with no hypothesis left.

## Implementation notes

The monoidal and braided structures are `Stacks.SheafInternalHom.monoidalCategory` and
`Stacks.SheafInternalHom.braidedCategory`, brought in as local instances exactly as in
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerMul.lean`: they are the structures the
tensor powers of a sheaf of modules are formed in.

`tensorInverse_snake` is closed by `exact`, not by `rw`: the second inverse law is the braiding
followed by the first by `rfl`, and `Iso.trans_hom` is also `rfl`, so the goal is already an
instance of `Stacks.Monoidal.braiding_eval_snake` at the default transparency level — while `rw`
works at implicit transparency and would not see it.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory
open Stacks.TensorPowers

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{v})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable (L : _root_.SheafOfModules.{v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) [IsInvertible 𝒪 h𝒪 L]

/-- **The two inverse laws of the chosen tensor inverse of an invertible sheaf of modules are
snake-compatible.**  `AlgebraicGeometry.SheafOfModules.tensorInverse` is
`Stacks.TensorPowers.tensorInverseOfTensorLeft`, so its second law is the braiding followed by its
first, and `Stacks.Monoidal.braiding_eval_snake` concludes from the triviality of the
self-braiding of an invertible sheaf. -/
theorem tensorInverse_snake :
    (α_ L (tensorInverse 𝒪 h𝒪 L).inv L).hom ≫
        L ◁ (tensorInverse 𝒪 h𝒪 L).mulIso'.hom ≫ (ρ_ L).hom =
      (tensorInverse 𝒪 h𝒪 L).mulIso.hom ▷ L ≫ (λ_ L).hom :=
  Stacks.Monoidal.braiding_eval_snake (tensorInverse 𝒪 h𝒪 L).mulIso.hom

/-- **The zig-zag identity for the tensor powers of an invertible sheaf of modules**, with no
hypothesis: stepping down a degree by `Stacks.TensorPowers.TensorInverse.predIso` and contracting
against the second inverse law undoes `Stacks.TensorPowers.TensorInverse.succIso`. -/
theorem tensorPow_predIso_zigzag (m : ℤ) :
    (((tensorInverse 𝒪 h𝒪 L).predIso m).hom ▷ L) ≫
        (α_ (tensorPow 𝒪 h𝒪 L m) (tensorInverse 𝒪 h𝒪 L).inv L).hom ≫
        tensorPow 𝒪 h𝒪 L m ◁ (tensorInverse 𝒪 h𝒪 L).mulIso'.hom ≫
          (ρ_ (tensorPow 𝒪 h𝒪 L m)).hom =
      ((tensorInverse 𝒪 h𝒪 L).succIso (m - 1)).inv ≫
        (reindex L (tensorInverse 𝒪 h𝒪 L).inv
          (show m - 1 + 1 = m from by omega)).hom :=
  Stacks.TensorPowers.TensorInverse.predIso_zigzag _ (tensorInverse_snake 𝒪 h𝒪 L) m

/-- **The successor equation for the multiplication of the tensor powers of an invertible sheaf of
modules at a negative second exponent**, with no hypothesis.  This is
`Stacks.TensorPowers.TensorInverse.subNatIso_succ` with its snake hypothesis discharged. -/
theorem tensorPow_subNatIso_succ (n : ℤ) (j : ℕ)
    (sBinv : tensorPow 𝒪 h𝒪 L (-(j : ℤ)) ⟶ tensorPow 𝒪 h𝒪 L (-((j : ℤ) + 1)) ⊗ L)
    (sR : tensorPow 𝒪 h𝒪 L (n - ((j + 1 : ℕ) : ℤ)) ⊗ L ⟶ tensorPow 𝒪 h𝒪 L (n - (j : ℤ)))
    (hsB : sBinv ≫
        ((reindex L (tensorInverse 𝒪 h𝒪 L).inv
            (show -((j : ℤ) + 1) = -(j : ℤ) - 1 from by omega)).hom ▷ L) ≫
          ((tensorInverse 𝒪 h𝒪 L).succIso (-(j : ℤ) - 1)).inv ≫
            (reindex L (tensorInverse 𝒪 h𝒪 L).inv
              (show -(j : ℤ) - 1 + 1 = -(j : ℤ) from by omega)).hom = 𝟙 _)
    (hsR : sR =
      ((reindex L (tensorInverse 𝒪 h𝒪 L).inv
            (show n - ((j + 1 : ℕ) : ℤ) = n - (j : ℤ) - 1 from by omega)).hom ▷ L) ≫
        ((tensorInverse 𝒪 h𝒪 L).succIso (n - (j : ℤ) - 1)).inv ≫
          (reindex L (tensorInverse 𝒪 h𝒪 L).inv
            (show n - (j : ℤ) - 1 + 1 = n - (j : ℤ) from by omega)).hom) :
    tensorPow 𝒪 h𝒪 L n ◁ sBinv ≫
        (α_ (tensorPow 𝒪 h𝒪 L n) (tensorPow 𝒪 h𝒪 L (-((j : ℤ) + 1))) L).inv ≫
          (((tensorInverse 𝒪 h𝒪 L).subNatIso n (j + 1)).hom ▷ L) ≫ sR =
      ((tensorInverse 𝒪 h𝒪 L).subNatIso n j).hom :=
  Stacks.TensorPowers.TensorInverse.subNatIso_succ _ (tensorInverse_snake 𝒪 h𝒪 L) n j
    sBinv sR hsB hsR

end AlgebraicGeometry.SheafOfModules

end
