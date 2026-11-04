module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor

/-!
# Two presentations of the right unitor `F ⊗ 𝒪 ≅ F` agree

For a sheaf of modules `F` on `X'`, the right unitor `F ⊗ 𝒪_{X'} ≅ F` has two presentations.

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorFactorObjUnitIso` moves the structure sheaf
  out of the argument slot of `Stacks.SheafOfModules.tensorLeftFunctor` with the symmetry
  `Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap` and then cancels it on the left with
  `Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso`.
* `Stacks.RingedSpace.tensorSheafUnitRightIso` is the presheaf right unitor carried through
  sheafification; it satisfies the section formula `x ⊗ r ↦ r • x`
  (`Stacks.RingedSpace.tensorSheafUnitRightIso_hom_tensorSheafUnit_tmul`).

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorFactorObjUnitIso_hom_eq`: the two right
  unitors are the same morphism.

## Implementation notes

Both sides are the sheafification of a morphism of presheaves of modules followed by the
sheafification counit at `F`, so the statement is `CategoryTheory.braiding_leftUnitor` on
presheaves of modules — the braiding followed by the left unitor is the right unitor — with the
sheafification functor applied to it.

The presheaf `F.val` is ascribed the type
`PresheafOfModules (structureRingPresheaf W.left.presheaf)`: at the spelling
`PresheafOfModules W.left.ringCatSheaf.obj` instance search does not find the monoidal structure on
presheaves of modules, and `λ_ F.val` fails to elaborate.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification (sheafify structureRingPresheaf)
open Stacks.SheafOfModules.Invertible (sheafifyForgetIso)
open Stacks.SheafOfModules (sheafifyValIso)

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

/-- The right unitor `F ⊗ 𝒪_{X'} ⟶ F` of the tensor factor is the right unitor
`Stacks.RingedSpace.tensorSheafUnitRightIso` of the tensor product sheaf. -/
theorem tensorFactorObjUnitIso_hom_eq (R : Type u) [CommRing R]
    (W : Over (Spec (CommRingCat.of R)))
    (F : _root_.SheafOfModules.{u} W.left.ringCatSheaf) :
    (tensorFactorObjUnitIso R W F).hom =
      (Stacks.RingedSpace.tensorSheafUnitRightIso W.left.toRingedSpace F).hom := by
  let G : PresheafOfModules.{u} (structureRingPresheaf W.left.presheaf) := F.val
  let S := sheafify W.left.presheaf (ringSheafCond W.left)
  let c := (sheafifyForgetIso W.left.presheaf (ringSheafCond W.left)).hom.app F
  show S.map (β_ G (𝟙_ (PresheafOfModules.{u} (structureRingPresheaf W.left.presheaf)))).hom ≫
      (S.map (λ_ G).hom ≫ c) =
    S.map (ρ_ G).hom ≫ (sheafifyValIso W.left.presheaf (ringSheafCond W.left) F).hom
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k ↦ k ≫ c) (S.map_comp _ _).symm) ?_
  refine Eq.trans (congrArg (fun k ↦ S.map k ≫ c) (braiding_leftUnitor G)) ?_
  exact congrArg (fun k ↦ S.map (ρ_ G).hom ≫ k) (Category.id_comp _)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
