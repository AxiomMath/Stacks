module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunction

/-!
# Sheafification of modules commutes with restriction along a cocontinuous functor

Let `w : X ⥤ Y` be continuous and cocontinuous and let `O` be a sheaf of rings on `Y`.
Sheafifying a presheaf of `O`-modules and then restricting along `w` is the same as restricting
the presheaf along `w` and then sheafifying.

Both composites are left adjoints to one functor: on the left because sheafification of presheaves
of modules is left adjoint to the forgetful functor, and restriction of sheaves of modules along a
continuous and cocontinuous functor is left adjoint to the direct image
`Stacks.SheafOfModules.pushforwardCocontinuous`
(`Stacks.SheafOfModules.RestrictRan.sheafAdjunction`); on the right because restriction of
presheaves of modules is left adjoint to `Stacks.SheafOfModules.ranPushforward`
(`Stacks.SheafOfModules.RestrictRan.adjunction`) and sheafification is again left adjoint to the
forgetful functor. The two right adjoints are the same functor on the nose: restriction of scalars
along an identity is the identity functor, and the direct image of sheaves of modules is
`ranPushforward` on underlying presheaves of modules by construction.

This is the module-coefficient counterpart of
`CategoryTheory.Functor.sheafificationCompPushforwardContinuousIso`, which is what the lan
criterion of `StacksFrontier/CategoryTheory/Sites/SheafPullbackSumFormula.lean` uses to push a
presheaf-level coproduct formula through sheafification. For modules it is what case (B) of the
direct-sum formula of Stacks 0D72 needs, the presheaf-level formula being
`Stacks.Sites.ComponentModuleSumFormula.colimitPullbackRestrictionIsoCoproduct`.

## Main results

* `Stacks.SheafOfModules.sheafificationCompRestrictIso`: the commutation.
* `Stacks.SheafOfModules.sheafificationCompRestrictIso_eq`: that commutation recorded as a
  *propositional* equality with the `CategoryTheory.Adjunction.leftAdjointUniq` it is defined to
  be. A consumer that transposes the commutation away needs the comparison to be opaque —
  writing `…leftAdjointUniq` of these two concrete composite adjunctions under a hom-set
  bijection runs into an `isDefEq` timeout — and this is the equation
  `CategoryTheory.Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_inv_app_comp` asks for.

## Implementation notes

The statement is phrased with Mathlib's `CategoryTheory.SheafOfModules.pushforward` at the
identity structure map for the restriction of sheaves of modules, and with
`CategoryTheory.PresheafOfModules.pushforward₀` for the restriction of presheaves of modules;
those are the two functors whose adjunctions are available, and they are the spellings the
consumers use.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v r v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y)
  [w.IsContinuous JX JY] [w.IsCocontinuous JX JY] (OY : Sheaf JY RingCat.{r})
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  [HasWeakSheafify JY AddCommGrpCat.{v}] [JY.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify JX AddCommGrpCat.{v}] [JX.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **Sheafification of presheaves of modules commutes with restriction along a continuous and
cocontinuous functor.** Sheafifying a presheaf of `O`-modules on `Y` and restricting the result
along `w` agrees with restricting the presheaf along `w` and sheafifying on `X`. -/
def sheafificationCompRestrictIso :
    PresheafOfModules.sheafification.{v} (𝟙 OY.obj) ⋙
        _root_.SheafOfModules.pushforward.{v} (F := w)
          (𝟙 (RestrictRan.ringSheaf w JX JY OY)) ≅
      PresheafOfModules.pushforward₀.{v} w OY.obj ⋙
        PresheafOfModules.sheafification.{v} (J := JX)
          (R₀ := (RestrictRan.ringSheaf w JX JY OY).obj)
          (R := RestrictRan.ringSheaf w JX JY OY)
          (𝟙 (RestrictRan.ringSheaf w JX JY OY).obj) :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction.{v} (𝟙 OY.obj)).comp
      (RestrictRan.sheafAdjunction.{v} w JX JY OY))
    ((RestrictRan.adjunction.{v} w OY.obj).comp
      (PresheafOfModules.sheafificationAdjunction.{v} (J := JX)
        (R₀ := (RestrictRan.ringSheaf w JX JY OY).obj)
        (R := RestrictRan.ringSheaf w JX JY OY)
        (𝟙 (RestrictRan.ringSheaf w JX JY OY).obj)))

/-- `Stacks.SheafOfModules.sheafificationCompRestrictIso` is, by definition, the comparison of the
two left adjoints of the two adjunctions it is built from.

This records the definition as a *propositional* equality, so that a consumer never has to unfold
it inside a larger type: the one `δ`-step it needs is affordable here and nowhere else. It is the
counterpart of
`CategoryTheory.CocontinuousSimplicialSite.transitionPullbackModulesIsoB_eq`. -/
theorem sheafificationCompRestrictIso_eq :
    sheafificationCompRestrictIso.{v} w JX JY OY =
      Adjunction.leftAdjointUniq
        ((PresheafOfModules.sheafificationAdjunction.{v} (𝟙 OY.obj)).comp
          (RestrictRan.sheafAdjunction.{v} w JX JY OY))
        ((RestrictRan.adjunction.{v} w OY.obj).comp
          (PresheafOfModules.sheafificationAdjunction.{v} (J := JX)
            (R₀ := (RestrictRan.ringSheaf w JX JY OY).obj)
            (R := RestrictRan.ringSheaf w JX JY OY)
            (𝟙 (RestrictRan.ringSheaf w JX JY OY).obj))) :=
  rfl

end Stacks.SheafOfModules

end
