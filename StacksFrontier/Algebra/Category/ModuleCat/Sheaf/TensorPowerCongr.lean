module

public import StacksFrontier.AlgebraicGeometry.Picard.Group.TensorConstraints
public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwiner
public import StacksFrontier.CategoryTheory.Equivalence.PowObjIsoSelf
public import StacksCore.Tactic.StacksAttribute

/-!
# Integer tensor powers depend only on the isomorphism class, and the powers of the unit

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `L` be a sheaf of `O`-modules
which is invertible, in the sense that tensoring on the right by `L` is an autoequivalence. The
`n`th tensor power `L^{⊗ n}` (`Stacks.SheafOfModules.TensorPower.tensorPower`) is the image of the
structure sheaf under the `n`th power of that autoequivalence, for `n : ℤ`. This file shows that
`L^{⊗ n}` depends only on the isomorphism class of `L`, and that every integer tensor power of the
structure sheaf is the structure sheaf.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.tensorPowerCongr`: the isomorphism `L^{⊗ n} ≅ L'^{⊗ n}`
  induced by an isomorphism `L ≅ L'`, for every integer `n`.
* `Stacks.SheafOfModules.TensorPower.unitTensorPowerIso`: the isomorphism `O^{⊗ n} ≅ O`, for
  every integer `n`.

## Main results

* `tensorPowerCongr_zero` and `tensorPowerCongr_one`, `unitTensorPowerIso_zero` and
  `unitTensorPowerIso_one`: the values of these isomorphisms at the exponents `0` and `1`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The integer tensor powers of a sheaf of modules depend only on its isomorphism class.** An
isomorphism `L ≅ L'` of invertible sheaves of `O`-modules induces `L^{⊗ n} ≅ L'^{⊗ n}` for every
`n : ℤ`. -/
noncomputable def tensorPowerCongr
    {L L' : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L').IsEquivalence] (e : L ≅ L') (n : ℤ) :
    tensorPower O hO L n ≅ tensorPower O hO L' n :=
  Stacks.Equivalence.powIntertwineObj ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L').asEquivalence (𝟭 _)
    (fun M => ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).mapIso e) n
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- At `n = 0` both tensor powers are the structure sheaf and the comparison is the identity. -/
theorem tensorPowerCongr_zero
    {L L' : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L').IsEquivalence] (e : L ≅ L') :
    tensorPowerCongr O hO e 0 = Iso.refl _ :=
  rfl

/-- At `n = 1` the comparison of first tensor powers is the comparison of the tensor products of
the structure sheaf with `L` and with `L'`. -/
theorem tensorPowerCongr_one
    {L L' : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L').IsEquivalence] (e : L ≅ L') :
    tensorPowerCongr O hO e 1 =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO))).mapIso e :=
  rfl

/-- **Every integer tensor power of the structure sheaf is the structure sheaf.** The isomorphism
`O^{⊗ n} ≅ O`, for every `n : ℤ`. -/
noncomputable def unitTensorPowerIso
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO))).IsEquivalence] (n : ℤ) :
    tensorPower O hO (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) n ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  Stacks.Equivalence.powObjIsoSelf
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO))).asEquivalence
    (fun M => tensorLeftFunctorObjUnitIso O hO M) n
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- At `n = 0` the zeroth tensor power is the structure sheaf and the identification is the
identity. -/
theorem unitTensorPowerIso_zero
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO))).IsEquivalence] :
    unitTensorPowerIso O hO 0 = Iso.refl _ :=
  rfl

/-- At `n = 1` the identification is the right unit constraint `O ⊗_O O ≅ O`. -/
theorem unitTensorPowerIso_one
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO))).IsEquivalence] :
    unitTensorPowerIso O hO 1 =
      tensorLeftFunctorObjUnitIso O hO
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO)) :=
  rfl

end Stacks.SheafOfModules.TensorPower

end
