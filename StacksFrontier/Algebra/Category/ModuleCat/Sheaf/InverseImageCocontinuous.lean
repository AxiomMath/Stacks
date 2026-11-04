module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuous
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of sheaves of modules along a cocontinuous functor of sites

Let `w : X ⥤ Y` be a cocontinuous functor of sites, giving a morphism of topoi
`f : Sh(X) ⟶ Sh(Y)` with `f_* = {}_sw`, let `O_X` and `O_Y` be sheaves of rings and let
`f^♯ : O_Y ⟶ {}_sw O_X` make `f` a morphism of ringed topoi.  The direct image of sheaves of
modules `f_* : Mod(O_X) ⥤ Mod(O_Y)` is `Stacks.SheafOfModules.pushforwardCocontinuous`.

This file shows that it is a right adjoint, and names its left adjoint
`f^* : Mod(O_Y) ⥤ Mod(O_X)`, the inverse image of sheaves of modules along a cocontinuous
functor of sites.

## Main results

* `Stacks.SheafOfModules.preservesLimitsOfSize_pushforwardCocontinuous` — **`f_*` on modules
  commutes with every limit.**
* `Stacks.SheafOfModules.isRightAdjoint_pushforwardCocontinuous` — **`f_*` on modules has a
  left adjoint** when `Mod(O_X)` is a Grothendieck abelian category and `Mod(O_Y)` is locally
  small.
* `Stacks.SheafOfModules.isRightAdjoint_pushforwardCocontinuous_of_hasWeakSheafify` — **`f_*` on
  modules has a left adjoint**, the explicit inverse image `f^* G = O_X ⊗_{f^{-1}O_Y} f^{-1}G`,
  when the source site and the sheaves of rings are small and abelian sheaves on the source site
  have a sheafification.
* `Stacks.SheafOfModules.inverseImageCocontinuous` and
  `Stacks.SheafOfModules.inverseImageCocontinuousAdjunction` — **`f^*`**, and the adjunction
  `f^* ⊣ f_*`.
* `Stacks.SheafOfModules.preservesInjectiveObjects_pushforwardCocontinuous` and
  `Stacks.SheafOfModules.preservesInjectiveObjects_iff_preservesMonomorphisms` — `f_*` carries
  injective `O_X`-modules to injective `O_Y`-modules exactly when `f^*` preserves
  monomorphisms, that is, exactly when `f^*` is exact.

## Exactness of the inverse image

On underlying abelian sheaves the inverse image of a cocontinuous functor is `G ↦ (w^p G)^#`,
which is exact ([Stacks, Tag 00XL]); on modules `f^*` is that abelian inverse image followed by
the base change `- ⊗_{f^{-1}O_Y} O_X` along the adjunct `f^{-1}O_Y ⟶ O_X` of `f^♯`, and base
change preserves monomorphisms only when it is flat
(`Stacks.ChangeOfRings.flat_of_preservesMonomorphisms_extendScalars`).  So `f^*` need not be
exact, and `preservesInjectiveObjects_pushforwardCocontinuous` takes preservation of
monomorphisms by `f^*` as a hypothesis; by `preservesInjectiveObjects_iff_preservesMonomorphisms`
that hypothesis is also necessary when `Mod(O_X)` has enough injectives.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v r v₁ u₁ v₂ u₂ v₃ u₃

namespace Stacks.SheafOfModules

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  {JX : GrothendieckTopology X} {JY : GrothendieckTopology Y} [w.IsCocontinuous JX JY]
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  {OX : Sheaf JX RingCat.{r}} {OY : Sheaf JY RingCat.{r}}
  (fSharp : OY ⟶ (w.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj OX)

/-! ### `f_*` commutes with all limits -/

section Forget

variable {Z : Type u₃} [Category.{v₃} Z] {JZ : GrothendieckTopology Z}

/-- The forgetful functor from sheaves of `O`-modules to presheaves of abelian groups: the
composite of the fully faithful inclusion of sheaves of modules into presheaves of modules with
the forgetful functor to presheaves of abelian groups. -/
abbrev toAbelianPresheaf (O : Sheaf JZ RingCat.{r}) :
    _root_.SheafOfModules.{v} O ⥤ Zᵒᵖ ⥤ AddCommGrpCat.{v} :=
  _root_.SheafOfModules.forget.{v} O ⋙ PresheafOfModules.toPresheaf.{v} O.obj

end Forget

/-- The direct image of sheaves of modules along a cocontinuous functor of sites, followed by
the forgetful functor to presheaves of abelian groups, is the forgetful functor followed by the
right Kan extension along `w.op`. -/
@[sga "4 I 5.8.3" "Clause 2, special case"]
lemma pushforwardCocontinuous_comp_toAbelianPresheaf :
    pushforwardCocontinuous.{v} w fSharp ⋙ toAbelianPresheaf.{v} OY
      = toAbelianPresheaf.{v} OX ⋙ w.op.ran :=
  rfl

/-- **The direct image of sheaves of modules along a cocontinuous functor of sites commutes with
every limit.** -/
@[sga "4 I 5.8.3" "Clause 2, special case"]
instance preservesLimitsOfSize_pushforwardCocontinuous :
    PreservesLimitsOfSize.{v, v} (pushforwardCocontinuous.{v} w fSharp) := by
  have hran : PreservesLimitsOfSize.{v, v} (w.op.ran (H := AddCommGrpCat.{v})) :=
    (w.op.ranAdjunction AddCommGrpCat.{v}).rightAdjoint_preservesLimits
  have hreflect : ReflectsLimitsOfSize.{v, v} (toAbelianPresheaf.{v} OY) :=
    reflectsLimits_of_reflectsIsomorphisms
  have hcomp : PreservesLimitsOfSize.{v, v}
      (pushforwardCocontinuous.{v} w fSharp ⋙ toAbelianPresheaf.{v} OY) := by
    rw [pushforwardCocontinuous_comp_toAbelianPresheaf]
    infer_instance
  exact preservesLimits_of_reflects_of_preserves _ (toAbelianPresheaf.{v} OY)

/-! ### `f_*` is a right adjoint -/

section Adjoint

variable [HasSheafify JX AddCommGrpCat.{v}] [JX.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [IsGrothendieckAbelian.{v} (_root_.SheafOfModules.{v} OX)]
  [LocallySmall.{v} (_root_.SheafOfModules.{v} OY)]

/-- **The direct image of sheaves of modules along a cocontinuous functor of sites has a left
adjoint.** -/
instance isRightAdjoint_pushforwardCocontinuous :
    (pushforwardCocontinuous.{v} w fSharp).IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating.{v}
    (isCoseparator_coseparator (_root_.SheafOfModules.{v} OX))
    (pushforwardCocontinuous.{v} w fSharp)

/-- **The inverse image of sheaves of modules along a cocontinuous functor of sites**,
`f^* : Mod(O_Y) ⥤ Mod(O_X)`: the left adjoint of the direct image
`Stacks.SheafOfModules.pushforwardCocontinuous`. -/
def inverseImageCocontinuous :
    _root_.SheafOfModules.{v} OY ⥤ _root_.SheafOfModules.{v} OX :=
  (pushforwardCocontinuous.{v} w fSharp).leftAdjoint

/-- **`f^* ⊣ f_*`**: the inverse image of sheaves of modules along a cocontinuous functor of
sites is left adjoint to the direct image. -/
def inverseImageCocontinuousAdjunction :
    inverseImageCocontinuous.{v} w fSharp ⊣ pushforwardCocontinuous.{v} w fSharp :=
  Adjunction.ofIsRightAdjoint (pushforwardCocontinuous.{v} w fSharp)

/-- The inverse image of sheaves of modules along a cocontinuous functor of sites commutes with
every colimit. -/
instance preservesColimitsOfSize_inverseImageCocontinuous :
    PreservesColimitsOfSize.{v, v} (inverseImageCocontinuous.{v} w fSharp) :=
  (inverseImageCocontinuousAdjunction.{v} w fSharp).leftAdjoint_preservesColimits

/-! ### Injective objects -/

/-- **The direct image of sheaves of modules along a cocontinuous functor of sites carries
injective modules to injective modules, as soon as its left adjoint preserves
monomorphisms.** -/
theorem preservesInjectiveObjects_pushforwardCocontinuous
    [(inverseImageCocontinuous.{v} w fSharp).PreservesMonomorphisms] :
    (pushforwardCocontinuous.{v} w fSharp).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (inverseImageCocontinuousAdjunction.{v} w fSharp)

/-- **The direct image preserves injective modules exactly when the inverse image preserves
monomorphisms**, when `Mod(O_X)` has enough injectives. -/
theorem preservesInjectiveObjects_iff_preservesMonomorphisms
    [EnoughInjectives (_root_.SheafOfModules.{v} OX)] :
    (pushforwardCocontinuous.{v} w fSharp).PreservesInjectiveObjects ↔
      (inverseImageCocontinuous.{v} w fSharp).PreservesMonomorphisms := by
  constructor
  · intro _
    exact Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
      (inverseImageCocontinuousAdjunction.{v} w fSharp)
  · intro _
    exact preservesInjectiveObjects_pushforwardCocontinuous.{v} w fSharp

end Adjoint

/-! ### `f_*` is a right adjoint, by the explicit inverse image -/

section AdjointOfWeakSheafify

variable [UnivLE.{r, v}] [UnivLE.{v₁, v}] [UnivLE.{u₁, v}]
  [HasWeakSheafify JX AddCommGrpCat.{v}] [JX.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **The direct image of sheaves of modules along a cocontinuous functor of sites has a left
adjoint, with no hypothesis on the categories of modules themselves**: the inverse image
`f^* G = O_X ⊗_{f^{-1}O_Y} f^{-1}G`, realised as restriction of the underlying presheaf of
modules along `w`, base change along the ring map `w^{-1}O_Y ⟶ O_X` adjoint to `f^♯`, and
sheafification, is left adjoint to it. -/
instance isRightAdjoint_pushforwardCocontinuous_of_hasWeakSheafify :
    (pushforwardCocontinuous.{v} w fSharp).IsRightAdjoint :=
  have adj : _root_.SheafOfModules.forget.{v} OY ⋙
      (PresheafOfModules.pushforward₀.{v} w OY.obj ⋙
        PresheafOfModules.pullback.{v} (F := 𝟭 X)
          (structureMapRestrict w OY.obj (structureMapPresheaf w fSharp))) ⋙
      PresheafOfModules.sheafification.{v} (R₀ := OX.obj) (𝟙 OX.obj) ⊣
      pushforwardCocontinuous.{v} w fSharp :=
    Adjunction.restrictFullyFaithful
      ((ranPushforwardAdjunction w OY.obj (structureMapPresheaf w fSharp)).comp
        (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 OX.obj)))
      (_root_.SheafOfModules.fullyFaithfulForget.{v} OY) (Functor.FullyFaithful.id _)
      (Iso.refl _) (Iso.refl _)
  adj.isRightAdjoint

end AdjointOfWeakSheafify

end Stacks.SheafOfModules

end
