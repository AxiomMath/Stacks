module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZero

/-!
# Extension by zero at a module universe independent of the object universe

Let `C` be a site, `J` a topology on it, `O` a sheaf of rings on `C` and `U : C`. This file
constructs the extension by zero `j_{U!}`, the left adjoint of restriction
`j_U^* = SheafOfModules.overFunctor O U` to the slice site over `U`, with the universe `a` of
the module sections subject only to `UnivLE.{v, a}`, where `v` is the universe of the morphisms
of `C`.

## Main definitions

* `PresheafOfModules.pushforwardIdIsoFree`: the pushforward along the identity morphism of
  presheaves of rings is `pushforward₀`.
* `SheafOfModules.extensionByZeroFree`: `j_{U!}`.
* `SheafOfModules.extensionByZeroFreeAdjunction`: the adjunction `j_{U!} ⊣ j_U^*`.

## Main results

* `PresheafOfModules.pushforwardId_isRightAdjoint_of_univLE`: restriction of presheaves of
  modules to the slice over `U`, as the pushforward along the identity morphism of presheaves of
  rings, is a right adjoint.
* `SheafOfModules.presheafOverRestriction_of_univLE`: the same for the presheaf-level pushforward
  along the identity of `O.over U`.
* `SheafOfModules.sheafOverRestriction_of_univLE`: restriction of sheaves of modules to the slice
  site over `U` is a right adjoint.
* `SheafOfModules.overFunctor_isRightAdjoint_of_univLE`: the same for
  `SheafOfModules.overFunctor O U`.
* `SheafOfModules.extensionByZeroFree_isLeftAdjoint`: `j_{U!}` is a left adjoint.

## References

* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public section

universe a w v u

open CategoryTheory CategoryTheory.Limits

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]

/-- The isomorphism between the pushforward of presheaves of modules along `Over.forget U` and
the identity morphism of presheaves of rings, and `pushforward₀ (Over.forget U) O`, at module
universe `a`. -/
noncomputable def pushforwardIdIsoFree (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :
    pushforward.{a} (F := Over.forget U)
        (R := O) (S := (Over.forget U).op ⋙ O) (𝟙 ((Over.forget U).op ⋙ O)) ≅
      pushforward₀.{a} (Over.forget U) O :=
  Iso.refl _

/-- Under `UnivLE.{v, a}`, restriction of presheaves of modules to the slice over `U`, as the
pushforward along `Over.forget U` and the identity morphism of presheaves of rings, is a right
adjoint. -/
instance pushforwardId_isRightAdjoint_of_univLE [UnivLE.{v, a}]
    (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :
    (pushforward.{a} (F := Over.forget U)
      (R := O) (S := (Over.forget U).op ⋙ O)
      (𝟙 ((Over.forget U).op ⋙ O))).IsRightAdjoint :=
  letI : (pushforward₀.{a} (Over.forget U) O).IsRightAdjoint :=
    (Stacks.Sites.OverModules.extensionFunctorAdjunction.{v, u, w, a} O U).isRightAdjoint
  Functor.isRightAdjoint_of_iso (pushforwardIdIsoFree.{a, w, v, u} O U).symm

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}]

/-- Under `UnivLE.{v, a}`, the presheaf-level pushforward along `Over.forget U` and the identity
of `O.over U` is a right adjoint. -/
instance presheafOverRestriction_of_univLE [UnivLE.{v, a}]
    (O : Sheaf J RingCat.{w}) (U : C) :
    (PresheafOfModules.pushforward.{a} (F := Over.forget U)
      (𝟙 (O.over U) : O.over U ⟶ O.over U).hom).IsRightAdjoint :=
  PresheafOfModules.pushforwardId_isRightAdjoint_of_univLE.{a, w, v, u} O.obj U

/-- Under `UnivLE.{v, a}`, restriction of sheaves of modules to the slice site over `U` is a right
adjoint. -/
instance sheafOverRestriction_of_univLE [UnivLE.{v, a}] (O : Sheaf J RingCat.{w}) (U : C) :
    (pushforward.{a} (F := Over.forget U)
      (𝟙 (O.over U) : O.over U ⟶ O.over U)).IsRightAdjoint :=
  have := presheafOverRestriction_of_univLE.{a, w, v, u} O U
  (PullbackConstruction.adjunction.{a} (F := Over.forget U)
    (𝟙 (O.over U))).isRightAdjoint

/-- Under `UnivLE.{v, a}`, `overFunctor O U` is a right adjoint. -/
instance overFunctor_isRightAdjoint_of_univLE [UnivLE.{v, a}]
    (O : Sheaf J RingCat.{w}) (U : C) :
    (overFunctor.{a} O U).IsRightAdjoint :=
  sheafOverRestriction_of_univLE.{a, w, v, u} O U

variable [UnivLE.{v, a}]

/-- The extension by zero `j_{U!}` of sheaves of modules from the slice site over `U`, at module
universe `a`: the left adjoint of restriction `j_U^* = overFunctor O U`. -/
noncomputable def extensionByZeroFree (O : Sheaf J RingCat.{w}) (U : C) :
    SheafOfModules.{a} (O.over U) ⥤ SheafOfModules.{a} O :=
  letI := sheafOverRestriction_of_univLE.{a, w, v, u} O U
  pullback.{a} (F := Over.forget U) (𝟙 (O.over U))

/-- The adjunction `j_{U!} ⊣ j_U^*` at module universe `a`. -/
noncomputable def extensionByZeroFreeAdjunction (O : Sheaf J RingCat.{w}) (U : C) :
    extensionByZeroFree.{a, w, v, u} O U ⊣ overFunctor.{a} O U :=
  letI := sheafOverRestriction_of_univLE.{a, w, v, u} O U
  pullbackPushforwardAdjunction.{a} (F := Over.forget U) (𝟙 (O.over U))

/-- `j_{U!}` is a left adjoint. -/
instance extensionByZeroFree_isLeftAdjoint (O : Sheaf J RingCat.{w}) (U : C) :
    (extensionByZeroFree.{a, w, v, u} O U).IsLeftAdjoint :=
  (extensionByZeroFreeAdjunction.{a, w, v, u} O U).isLeftAdjoint

end SheafOfModules

end
