module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCongr
public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerSucc

/-!
# The congruence of integral tensor powers satisfies a successor law

`Stacks.SheafOfModules.TensorPower.tensorPowerCongr` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerCongr.lean` carries an isomorphism
`L ≅ L'` of invertible sheaves of modules to an isomorphism `L^{⊗ n} ≅ L'^{⊗ n}` of the integral
tensor powers of [Stacks, Tag 01CU], in every integer degree. It is built from
`Stacks.Equivalence.powIntertwineObj`, whose recursion lowers the exponent *at a shifted object*,
so it was accompanied only by its values in the degrees `0` and `1`, where both sides are
already named.

This file supplies the equation an induction on the degree needs: the comparison at `n + 1` is
the comparison at `n` tensored on the right by `L`, read between the successor comparisons
`Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso` of the two families and corrected by the
degree-one comparison obtained by applying the native tensor bifunctor's `mapIso`.

## Main results

* `Stacks.SheafOfModules.TensorPower.tensorPowerCongr_succIso`: **the successor law for
  `tensorPowerCongr`, in every integer degree.**

## Implementation notes

There is nothing to prove here: the statement is
`Stacks.Equivalence.powIntertwineObj_succIso` of
`StacksFrontier/CategoryTheory/Equivalence/PowIntertwinerSucc.lean` read at the two tensoring
autoequivalences, along the identity functor, at the structure sheaf. Every identification it
needs is definitional — `tensorPowerSuccIso O hO L n` *is*
`Stacks.Equivalence.powSuccIso` for the native right-tensor autoequivalence at the unit, the
`n`-th power of the autoequivalence applied to the unit *is* `tensorPower O hO L n`, and the
identity functor's action on morphisms is the identity — so a single `exact` crosses the whole
distance.

The reason it is worth recording is that two files in this repository state that no such
equation is available: the implementation notes of
`StacksFrontier/AlgebraicGeometry/PowerFamilyBridge/Recursion.lean` and the section "Why this is
not `tensorPowerCongr`" of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/LaurentCongr.lean`. Both predate
`PowIntertwinerSucc`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules.TensorSheafification (structureSheaf structureRingPresheaf)

universe v u w

namespace Stacks.SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The successor law for the congruence of integral tensor powers.** For an isomorphism
`e : L ≅ L'` of invertible sheaves of modules, the comparison `L^{⊗ (n+1)} ≅ L'^{⊗ (n+1)}` of
[Stacks, Tag 01CU] is the comparison in the degree `n` tensored on the right by `L'`, preceded by
`e` in the top factor, read between the successor comparisons of the two families:

`succIso_L ≫ congr (n+1) = (L^{⊗ n} ⊗ e) ≫ (congr n ⊗ L') ≫ succIso_{L'}`.

This is `Stacks.Equivalence.powIntertwineObj_succIso` at the two autoequivalences
`- ⊗ L` and `- ⊗ L'` along the identity functor, evaluated at the structure sheaf; every
identification involved is definitional. Together with
`Stacks.SheafOfModules.TensorPower.tensorPowerCongr_zero` it determines the family in every
integer degree, because the successor comparisons are isomorphisms and tensoring on the right by
`L'` is an equivalence. -/
theorem tensorPowerCongr_succIso
    {L L' : _root_.SheafOfModules.{w} (structureSheaf O hO)}
    [((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
    [((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L').IsEquivalence]
    (e : L ≅ L') (n : ℤ) :
    (tensorPowerSuccIso O hO L n).hom ≫ (tensorPowerCongr O hO e (n + 1)).hom =
      (((Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj
          (tensorPower O hO L n)).mapIso e).hom ≫
        ((Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
            L').map
            (tensorPowerCongr O hO e n).hom ≫
          (tensorPowerSuccIso O hO L' n).hom :=
  Stacks.Equivalence.powIntertwineObj_succIso
    ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence
    ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L').asEquivalence
    (𝟭 _) (fun M => ((Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).mapIso e) n
    (_root_.SheafOfModules.unit (structureSheaf O hO))

end Stacks.SheafOfModules.TensorPower

end
