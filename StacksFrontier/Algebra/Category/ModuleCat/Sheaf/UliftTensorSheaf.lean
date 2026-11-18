module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftTensorPresheaf

/-!
# The universe lift of a tensor product of sheaves of modules

`SheafOfModules.HasGlobalPresentation`, the global condition of Stacks 03DE(6) underlying
quasi-coherence on an arbitrary site, states a presentation of a sheaf of modules after raising
the universe of its sections by `SheafOfModules.uliftForPresentation`.  To present a tensor
product that way one needs the tensor product *at that raised universe*, and the comparison of
the raised-universe tensor product of the lifts with the lift of the tensor product.  This file
proves that comparison.

The tensor product used is `Stacks.SheafOfModules.Tensor.sheafTensor`, the Stacks 0GMW tensor
product of sheaves of modules whose two module universes are independent of the universe of the
ring sheaf.  That independence is what makes the statement possible: the ring sheaf stays at its
own universe while both module universes are raised.

## Main results

* `Stacks.SheafOfModules.UliftTensor.uliftTensorSheafIso`: raising the universe of the sections
  commutes with the tensor product of sheaves of modules.

## Implementation notes

Both sides are sheafifications of presheaves of modules, and both receive a locally bijective
map from one: the raised-universe tensor product receives its own sheafification unit (the unit
of the sealed `Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction`), and the
lift of the tensor product receives the universe lift of the sheafification unit, which is
locally bijective because `ULift.up` is injective and hits every lifted section.  The two
sources are identified by `presheafUliftTensorIso`, so `isoOfLocallyBijective` applies.

The universe arguments of `Stacks.SheafOfModules.Tensor.sheafTensor` are written out: the
unlifted bifunctor is used at the module universe of the sheaves and the lifted one at the
raised universe, and the instance arguments of the two differ, so leaving the levels to
inference picks up the wrong sheafification instances; for the same reason the module universe
of `sheafificationForgetAdjunction` is written out.

## References

* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t z

namespace Stacks.SheafOfModules.UliftTensor

section SealedUnit

open Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]

/-- The unit of the sealed sheafification, with the plain forgetful functor as right adjoint, is
locally injective. -/
lemma isLocallyInjective_sheafificationForgetAdjunction_unit_app
    (P : PresheafOfModules.{z} (ringSheaf R).obj) :
    PresheafOfModules.IsLocallyInjective J
      ((sheafificationForgetAdjunction R).unit.app P) := by
  rw [sheafificationForgetAdjunction_unit_app, PresheafOfModules.IsLocallyInjective,
    Functor.map_comp]
  infer_instance

/-- The unit of the sealed sheafification, with the plain forgetful functor as right adjoint, is
locally surjective. -/
lemma isLocallySurjective_sheafificationForgetAdjunction_unit_app
    (P : PresheafOfModules.{z} (ringSheaf R).obj) :
    PresheafOfModules.IsLocallySurjective J
      ((sheafificationForgetAdjunction R).unit.app P) := by
  rw [sheafificationForgetAdjunction_unit_app, PresheafOfModules.IsLocallySurjective,
    Functor.map_comp]
  infer_instance

end SealedUnit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{max t w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t w}]

open Stacks.SheafOfModules.Tensor in
/-- Raising the universe of the sections commutes with the tensor product of sheaves of
modules. -/
noncomputable def uliftTensorSheafIso
    (A B : SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp)) :
    SheafOfModules.uliftForPresentation.{u, v, w, w, t}
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj A).obj B) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} Osharp).obj
          (SheafOfModules.uliftForPresentation.{u, v, w, w, t} A)).obj
          (SheafOfModules.uliftForPresentation.{u, v, w, w, t} B) :=
  let u₁ := (sheafificationForgetAdjunction.{_, _, _, w} Osharp).unit.app
    (PresheafOfModules.tensorObj A.val B.val)
  let u₂ := (sheafificationForgetAdjunction.{_, _, _, max t w} Osharp).unit.app
    (PresheafOfModules.tensorObj (SheafOfModules.uliftForPresentation.{u, v, w, w, t} A).val
      (SheafOfModules.uliftForPresentation.{u, v, w, w, t} B).val)
  isoOfLocallyBijective (presheafUliftMap.{u, v, w, w, t} u₁) u₂
    (isLocallyInjective_presheafUliftMap.{u, v, w, w, t} (J := J) u₁
      (isLocallyInjective_sheafificationForgetAdjunction_unit_app Osharp
        (PresheafOfModules.tensorObj A.val B.val)))
    (isLocallySurjective_presheafUliftMap.{u, v, w, w, t} (J := J) u₁
      (isLocallySurjective_sheafificationForgetAdjunction_unit_app Osharp
        (PresheafOfModules.tensorObj A.val B.val)))
    (isLocallyInjective_sheafificationForgetAdjunction_unit_app Osharp _)
    (isLocallySurjective_sheafificationForgetAdjunction_unit_app Osharp _)
    (presheafUliftTensorIso.{u, v, w, w, w, t} A.val B.val)

end Stacks.SheafOfModules.UliftTensor

end
