module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorUnitors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictBifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit

/-!
# The right unitor of Tag 01CA is the one the derived development is stated at

On a ringed site `(C, J, 𝒪)` the category `Mod(𝒪)` carries two monoidal structures whose tensor
product is the tensor product sheaf of [Stacks, Tag 01CA] on the nose:
`Stacks.SheafOfModules.Strict.monoidalCategory`, obtained from the localized structure by
`CategoryTheory.Monoidal.induced`, and `SheafOfModules.monoidalCategorySheafTensor`, obtained
from it by `CategoryTheory.MonoidalCategory.reseat`. The unitor of the second is the one
`Stacks.SheafOfModules.sheafTensorUnitNatIso` — the isomorphism `- ⊗_𝒪 𝒪 ≅ 𝟭` that the derived
development is stated at — reads off. This file shows that the two right unitors agree.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree` proves the same
thing on a ringed **space**, where the first structure is spelled
`Stacks.PullbackGradedAlgebra.monoidalCategory`; the proof there goes through the section formula
`Stacks.PullbackTensorCoherence.rightUnitor_hom_tmul`, which is available only for a space. The
site-level section formula is `Stacks.SheafOfModules.rightUnitor_hom_val_app_tmul`, read in the
tensor-bifunctor spelling by `Stacks.TensorSheafWorld`, and that is what is used here.

## Main results

* `Stacks.TensorSheafWorld.rightUnitor_eq_tensorSheafUnitRightIso`: **the right unitor of
  Tag 01CA is the right unitor `ℱ ⊗_𝒪 𝒪 ≅ ℱ` of the tensor product sheaf**, both carrying a
  local pure tensor `x ⊗ r` to `r • x`.
* `Stacks.SheafOfModules.Strict.sheafTensorUnitNatIso_hom_app_eq`: **the component of
  `Stacks.SheafOfModules.sheafTensorUnitNatIso` at a sheaf of modules is the right unitor of
  Tag 01CA.** This is the form the derived development consumes: it is what turns a monoidal
  coherence for the structure of Tag 01CA into a statement about
  `Stacks.SheafOfModules.Tensor.sheafTensor` and `Stacks.SheafOfModules.sheafTensorUnitNatIso`.

## Implementation notes

Neither monoidal structure is left to instance synthesis where both are in scope. The first
statement is made at the `CategoryTheory.Sheaf.toRingCat` spelling of the sheaf of rings, where
`Stacks.TensorSheafWorld.monoidalCategory` is the one local instance and the section formulas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge` are stated; the second is
made at the `Stacks.SheafOfModules.Tensor.ringSheaf` spelling, where
`Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf` is the one local instance and
`Stacks.SheafOfModules.sheafTensorUnitNatIso` lives. The two sheaves of rings are equal by proof
irrelevance, so the second statement follows from the first by `:=` through
`SheafOfModules.rightUnitor_sheafTensor_eq`; the crossing happens once, inside a defeq-tolerant
`Eq.trans`.

The four sheaf arguments of `PresheafOfModules.tensorSheaf_hom_ext` are passed explicitly. Left
as metavariables they have to be solved across the boundary between `ℱ ⊗ 𝒢` and
`(tensorSheafBifunctor J).obj (ℱ, 𝒢)` — definitionally equal and not syntactically so — and
`isDefEq` then exhausts its budget; this is the hazard recorded in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules

open scoped TensorProduct

universe v u

namespace Stacks.TensorSheafWorld

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  (R : Sheaf J CommRingCat.{max u v})
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

attribute [local instance] monoidalCategory

/-- **The right unitor of the monoidal structure of Tag 01CA is the right unitor
`ℱ ⊗_𝒪 𝒪 ≅ ℱ` of the tensor product sheaf**: both carry a local pure tensor `x ⊗ r` to
`r • x`. -/
theorem rightUnitor_eq_tensorSheafUnitRightIso
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      R.obj))
    (M : SheafOfModules.{max u v} (toRingCat J R)) :
    (ρ_ M).hom = (Stacks.SheafOfModules.tensorSheafUnitRightIso R.obj hO M).hom :=
  PresheafOfModules.tensorSheaf_hom_ext
    (Osharp := R) (F := M) (G := 𝟙_ (SheafOfModules.{max u v} (toRingCat J R))) (Q := M)
    (φ := (ρ_ M).hom)
    (ψ := (Stacks.SheafOfModules.tensorSheafUnitRightIso R.obj hO M).hom)
    (fun V x y => (rightUnitor_hom_val_app_tensorSheafUnit R hO M V x y).trans
      (Stacks.SheafOfModules.tensorSheafUnitRightIso_hom_toSheafify_tmul R.obj hO M V x y).symm)

end

end Stacks.TensorSheafWorld

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  (R : Sheaf J CommRingCat.{max u v})
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

attribute [local instance] monoidalUnderlyingRingSheaf

/-- **The unit law `ℱ ⊗_𝒪 𝒪 ≅ ℱ` of `Stacks.SheafOfModules.sheafTensorUnitNatIso` is the right
unitor of the monoidal structure of Tag 01CA.** -/
theorem sheafTensorUnitNatIso_hom_app_eq
    (A : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (Stacks.SheafOfModules.sheafTensorUnitNatIso R).hom.app A = (ρ_ A).hom :=
  (_root_.SheafOfModules.rightUnitor_sheafTensor_eq R A).trans
    (Stacks.TensorSheafWorld.rightUnitor_eq_tensorSheafUnitRightIso R
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property A).symm

end Stacks.SheafOfModules.Strict

end
