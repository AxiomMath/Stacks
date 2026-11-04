module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerIntegerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafOverSlice

/-!
# A multiplicative generator for a tensor power trivialized over a slice

Let `O` be a sheaf of commutative rings on a site, let `L` be an invertible sheaf of
`O`-modules in the sense of Tag 01CS, and suppose `L` is trivial over the slice of some object
`U`, via a chosen isomorphism `e : L.over U ≅ unit`. Restriction to the slice is a functor, so
it carries the recursive structure of the integer tensor powers `L^{⊗ n}` (Tag 01CU) along with
it: this file builds the induced trivialization `(L^{⊗ n}).over U ≅ unit` of every natural-number
power by recursion directly through the coherent multiplication `coherentMulIso`, and proves
that this family is multiplicative in the sense that `coherentMulIso`, read through the
restriction functor, carries the product of two generators to the generator of the sum.

This is deliberately *not* built from the degree-indexed autoequivalence comparisons
`tensorPowerCongr`/`unitTensorPowerIso`: those normalise a single power comparison against the
recursive definition of `Equivalence.zpow`, but neither is known to be compatible with
`coherentMulIso`, which is the multiplication the twisted graded algebra of
`StacksFrontier.AlgebraicGeometry.GradedAlgebraTwist.Basic` actually uses. Building the generator
family directly out of `coherentMulIso` instead makes the degree-`(n, 1)` case of
multiplicativity hold by construction, which is `sliceGeneratorIso_succ` below.

## Implementation notes

The general case `sliceGeneratorIso_add (n m : ℕ)` does *not* follow from
`coherentMulIso_assoc` by induction with nothing further to reconcile, which is what this
construction was expected to achieve. Its base case `m = 0` reduces to two facts, neither of
which is proved anywhere in this library:

1. `Invertible.tensorProductLeftUnitor O hO unit = Invertible.tensorProductRightUnitor O hO unit`,
   the coincidence of the two unitors at the unit object. They are built by hand here rather than
   supplied by a `CategoryTheory.MonoidalCategory` instance, so the coherence theorem that would
   otherwise give this does not apply to them.
2. Compatibility of `overTensorSheafIso`, the slice-restriction/tensor comparison of
   `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafOverSlice`, with
   `Invertible.tensorProductRightUnitor` and `tensorProductAssociator` under
   `whiskerRestriction`.

For the *unrestricted* unitor the corresponding naturality statement does exist, at exactly the
generality used here: `Stacks.IdealTorsion.Eta.tensorProductRightUnitor_naturality` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheaf.lean`. Transporting it through the slice
is precisely what items 1 and 2 ask for, and is the whole of the remaining work. With those in
hand the induction on `m` runs on `coherentMulIso_zero_right` for the base case and
`coherentMulIso_assoc` for the step, mirroring the successor case proved below.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.sliceGeneratorIso`: the induced trivialization
  `unit ≅ (L^{⊗ n}).over U` for `n : ℕ`, built by recursion through `coherentMulIso`.

## Main results

* `Stacks.SheafOfModules.TensorPower.sliceGeneratorIso_succ`: **the generator family is
  multiplicative in degree `(n, 1)`.** The generator in degree `n + 1` is the product of the
  generator in degree `n` and the degree-one generator, compared through `coherentMulIso` read
  along the restriction functor. It holds by `rfl` — this is the case the recursion is set up to
  make true by construction.

The general statement `sliceGeneratorIso_add (n m : ℕ)` is **not** proved here; the
implementation notes below say what it still needs.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
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
  (U : C)
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
  [IsInvertible O hO L]
  (e : (whiskerRestriction O hO (Over.forget U)).obj L ≅
    _root_.SheafOfModules.unit
      (TensorSheafification.structureSheaf ((Over.forget U).op ⋙ O)
        (sliceStructureIsSheaf O hO U)))

/-- The comparison `unit ≅ (L^{⊗ n}).over U ⊗ (L^{⊗ m}).over U ≅ (L^{⊗ (n + m)}).over U`, built
from `coherentMulIso` read through the restriction functor, is what multiplicativity of the
generator family compares against. -/
noncomputable def sliceProductOver (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Over.forget U).op ⋙ O),
          Presheaf.isSheaf_of_isSheaf_comp _ (((Over.forget U).op ⋙ O))
            (forget₂ CommRingCat RingCat) ((sliceStructureIsSheaf O hO U))⟩).obj
          (((whiskerRestriction O hO (Over.forget U)).obj (tensorPower O hO L n)))).obj
        (((whiskerRestriction O hO (Over.forget U)).obj (tensorPower O hO L m)))) ≅
      (whiskerRestriction O hO (Over.forget U)).obj (tensorPower O hO L (n + m)) :=
  (overTensorSheafIso O hO U (tensorPower O hO L n) (tensorPower O hO L m)).symm ≪≫
    (whiskerRestriction O hO (Over.forget U)).mapIso (coherentMulIso O hO L n m)

/-- The induced trivialization of the degree-one tensor power, read off from `e` along the
canonical identification `tensorPower O hO L 1 ≅ L`. -/
noncomputable def sliceGeneratorOneIso :
    _root_.SheafOfModules.unit
        (TensorSheafification.structureSheaf ((Over.forget U).op ⋙ O)
          (sliceStructureIsSheaf O hO U)) ≅
      (whiskerRestriction O hO (Over.forget U)).obj (tensorPower O hO L 1) :=
  e.symm ≪≫ ((whiskerRestriction O hO (Over.forget U)).mapIso (tensorPowerOneIso O hO L)).symm

/-- **The trivialization of the `n`-th tensor power induced over the slice, for `n : ℕ`.** Built
by recursion directly through `coherentMulIso`: the base case is the trivialization of the
zeroth power (the structure sheaf itself, on both sides, by `rfl`), and the successor step
multiplies the previous generator by `sliceGeneratorOneIso` using `coherentMulIso`. -/
noncomputable def sliceGeneratorIso :
    (n : ℕ) →
      _root_.SheafOfModules.unit
          (TensorSheafification.structureSheaf ((Over.forget U).op ⋙ O)
            (sliceStructureIsSheaf O hO U)) ≅
        (whiskerRestriction O hO (Over.forget U)).obj (tensorPower O hO L (n : ℤ))
  | 0 => Iso.refl _
  | n + 1 =>
      (Invertible.tensorProductLeftUnitor ((Over.forget U).op ⋙ O)
          (sliceStructureIsSheaf O hO U)
          (_root_.SheafOfModules.unit
            (TensorSheafification.structureSheaf ((Over.forget U).op ⋙ O)
              (sliceStructureIsSheaf O hO U)))).symm ≪≫
      Invertible.tensorProductIso ((Over.forget U).op ⋙ O) (sliceStructureIsSheaf O hO U)
          (sliceGeneratorIso n) (sliceGeneratorOneIso O hO U L e) ≪≫
      sliceProductOver O hO U L (n : ℤ) 1

/-- By construction, the generator in degree `n + 1` is obtained from the generator in degree
`n` and the degree-one generator exactly through `sliceProductOver`: this is the degree-`(n, 1)`
case of multiplicativity, true "by construction" rather than by a separate argument. -/
theorem sliceGeneratorIso_succ (n : ℕ) :
    sliceGeneratorIso O hO U L e (n + 1) =
      (Invertible.tensorProductLeftUnitor ((Over.forget U).op ⋙ O)
          (sliceStructureIsSheaf O hO U)
          (_root_.SheafOfModules.unit
            (TensorSheafification.structureSheaf ((Over.forget U).op ⋙ O)
              (sliceStructureIsSheaf O hO U)))).symm ≪≫
      Invertible.tensorProductIso ((Over.forget U).op ⋙ O) (sliceStructureIsSheaf O hO U)
          (sliceGeneratorIso O hO U L e n) (sliceGeneratorOneIso O hO U L e) ≪≫
      sliceProductOver O hO U L (n : ℤ) 1 :=
  rfl

end Stacks.SheafOfModules.TensorPower

end
