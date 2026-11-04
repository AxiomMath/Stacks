module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Adjunction.Triple
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImage
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuous

/-!
# Restriction of sheaves of modules along a continuous and cocontinuous functor

Let `w : X ⥤ Y` be a functor of sites which is both continuous and cocontinuous, and let `O` be
a sheaf of rings on `Y`.  Restriction along `w` carries a sheaf of `O`-modules to a sheaf of
modules over the restricted sheaf of rings `w⁻¹O`; this is Mathlib's
`SheafOfModules.pushforward (𝟙 _)`.  Continuity is what makes the restriction of a sheaf a
sheaf.  Cocontinuity makes restriction the *inverse image* of the morphism of topoi
`g : Sh(X) ⟶ Sh(Y)` of Stacks 00XO, whose direct image is the right Kan extension along `w.op`.

On sheaves of modules, too, restriction is left adjoint to the direct image
`Stacks.SheafOfModules.pushforwardCocontinuous`, as soon as the source site is essentially small
and the target site locally small in the universe `v` of the module sections; `v` need not
dominate the universes of the two sites. When `w` is moreover fully faithful the counit of that
adjunction is an isomorphism (Stacks 00XT on sheaves of modules), and therefore the unit of *any*
left adjoint of restriction is an isomorphism: the lower shriek `g_!` is fully faithful.

## Main definitions

* `Stacks.SheafOfModules.ranUnitRingSheaf`: the tautological structure map `O ⟶ g_* g⁻¹ O`.
* `Stacks.SheafOfModules.restrictionAdjunction`: restriction of sheaves of modules along `w` is
  left adjoint to the direct image along the cocontinuous `w`.

## Main results

* `Stacks.SheafOfModules.isLeftAdjoint_restriction`: restriction is a left adjoint.
* `Stacks.SheafOfModules.isIso_restrictionAdjunction_counit`: for a fully faithful `w` the
  counit `g⁻¹ g_* ⟶ id` is an isomorphism.
* `Stacks.SheafOfModules.isIso_unit_of_restriction`: for a fully faithful `w`, the unit
  `id ⟶ g⁻¹ L` of any left adjoint `L` of restriction is an isomorphism.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u₁ v₁ u₂ v₂

namespace Stacks.SheafOfModules

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  [EssentiallySmall.{v} X] [LocallySmall.{v} Y]

/-- Over an essentially small source and a locally small target, `w.op` has pointwise right Kan
extensions of presheaves valued in a category with limits of size `v`. -/
private theorem hasPointwiseRightKanExtension_of_hasLimits (C : Type*) [Category C]
    [HasLimitsOfSize.{v, v} C] (F : Xᵒᵖ ⥤ C) : w.op.HasPointwiseRightKanExtension F := fun V ↦ by
  have := hasLimitsOfShape_of_essentiallySmall.{v} (StructuredArrow V w.op) C
  infer_instance

/-- Over an essentially small source and a locally small target, `w.op` has pointwise right Kan
extensions of presheaves of abelian groups. -/
theorem hasPointwiseRightKanExtension_addCommGrpCat (F : Xᵒᵖ ⥤ AddCommGrpCat.{v}) :
    w.op.HasPointwiseRightKanExtension F := 
  hasPointwiseRightKanExtension_of_hasLimits w _ F

/-- Over an essentially small source and a locally small target, `w.op` has pointwise right Kan
extensions of presheaves of rings. -/
theorem hasPointwiseRightKanExtension_ringCat (F : Xᵒᵖ ⥤ RingCat.{v}) :
    w.op.HasPointwiseRightKanExtension F := 
  hasPointwiseRightKanExtension_of_hasLimits w _ F

attribute [local instance] hasPointwiseRightKanExtension_addCommGrpCat
  hasPointwiseRightKanExtension_ringCat

variable (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y)
  [w.IsContinuous JX JY] [w.IsCocontinuous JX JY] (O : Sheaf JY RingCat.{v})

/-- The tautological structure map `O ⟶ g_* g⁻¹ O` of the morphism of topoi attached to the
cocontinuous functor `w`: on underlying presheaves it is the unit of the right Kan extension
adjunction along `w.op`. -/
abbrev ranUnitRingSheaf :
    O ⟶ (w.sheafPushforwardCocontinuous RingCat.{v} JX JY).obj
      ((w.sheafPushforwardContinuous RingCat.{v} JX JY).obj O) :=
  ⟨ranUnitRing w O.obj⟩

/-- Restriction of presheaves of modules along `w`, in the form
`PresheafOfModules.pushforward (𝟙 _)` in which it underlies restriction of sheaves of modules, is
left adjoint to the direct image for the tautological structure map. -/
def presheafRestrictionAdjunction (T : Yᵒᵖ ⥤ RingCat.{v}) :
    PresheafOfModules.pushforward.{v} (F := w) (𝟙 (w.op ⋙ T)) ⊣
      ranPushforward.{v} w (ranUnitRing w T) :=
  (pushforward₀RanPushforwardAdjunction.{v} w T).ofNatIsoLeft
    (Functor.isoWhiskerLeft (PresheafOfModules.pushforward₀.{v} w T)
        (PresheafOfModules.restrictScalarsId.{v, v} (w.op ⋙ T)) ≪≫
      (PresheafOfModules.pushforward₀.{v} w T).rightUnitor).symm

/-- The direct image of sheaves of modules along the cocontinuous `w`, read on underlying
presheaves of modules, is the direct image of presheaves of modules: the two are the same
construction. -/
def pushforwardCocontinuousCompForgetIso :
    _root_.SheafOfModules.forget ((w.sheafPushforwardContinuous RingCat.{v} JX JY).obj O) ⋙
        ranPushforward.{v} w (ranUnitRing w O.obj) ≅
      pushforwardCocontinuous.{v} w (ranUnitRingSheaf w JX JY O) ⋙
        _root_.SheafOfModules.forget O :=
  NatIso.ofComponents (fun N ↦ Iso.refl ((ranPushforward.{v} w (ranUnitRing w O.obj)).obj N.val))
    (fun _ ↦ rfl)

/-- Restriction of sheaves of modules along a continuous and cocontinuous functor is left
adjoint to the direct image along it, for the tautological structure map. -/
def restrictionAdjunction :
    _root_.SheafOfModules.pushforward.{v}
        (𝟙 ((w.sheafPushforwardContinuous RingCat.{v} JX JY).obj O)) ⊣
      pushforwardCocontinuous.{v} w (ranUnitRingSheaf w JX JY O) :=
  (presheafRestrictionAdjunction.{v} w O.obj).restrictFullyFaithful
    (_root_.SheafOfModules.fullyFaithfulForget O)
    (_root_.SheafOfModules.fullyFaithfulForget
      ((w.sheafPushforwardContinuous RingCat.{v} JX JY).obj O))
    (NatIso.ofComponents (fun N ↦ Iso.refl
      ((PresheafOfModules.pushforward.{v} (F := w) (𝟙 (w.op ⋙ O.obj))).obj N.val))
      (fun _ ↦ rfl))
    (pushforwardCocontinuousCompForgetIso w JX JY O)

/-- Restriction of sheaves of modules along a continuous and cocontinuous functor is a left
adjoint. -/
instance isLeftAdjoint_restriction :
    (_root_.SheafOfModules.pushforward.{v}
      (𝟙 ((w.sheafPushforwardContinuous RingCat.{v} JX JY).obj O))).IsLeftAdjoint :=
  (restrictionAdjunction w JX JY O).isLeftAdjoint

variable [w.Full] [w.Faithful]

/-- For a fully faithful, continuous and cocontinuous `w`, the counit `g⁻¹ g_* ⟶ id` of the
restriction adjunction of sheaves of modules is an isomorphism. -/
theorem isIso_restrictionAdjunction_counit :
    IsIso (restrictionAdjunction w JX JY O).counit := by
  have hpre : IsIso (pushforward₀RanPushforwardAdjunction.{v} w O.obj).counit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun P ↦ ?_
    have : IsIso ((PresheafOfModules.toPresheaf _).map
        ((pushforward₀RanPushforwardAdjunction.{v} w O.obj).counit.app P)) :=
      (w.op.isPointwiseRightKanExtensionRanCounit P.presheaf).isIso_hom
    exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  have hff : (ranPushforward.{v} w (ranUnitRing w O.obj)).FullyFaithful :=
    (pushforward₀RanPushforwardAdjunction.{v} w O.obj).fullyFaithfulROfIsIsoCounit
  have hcomp := (_root_.SheafOfModules.fullyFaithfulForget
    ((w.sheafPushforwardContinuous RingCat.{v} JX JY).obj O)).comp hff
  have h3 : (pushforwardCocontinuous.{v} w (ranUnitRingSheaf w JX JY O)).FullyFaithful :=
    (hcomp.ofIso (pushforwardCocontinuousCompForgetIso w JX JY O)).ofCompFaithful
  have := h3.full
  have := h3.faithful
  exact (restrictionAdjunction w JX JY O).counit_isIso_of_R_fully_faithful

/-- For a fully faithful, continuous and cocontinuous `w`, the unit `id ⟶ g⁻¹ L` of any left
adjoint `L` of restriction of sheaves of modules is an isomorphism: the lower shriek is fully
faithful. -/
theorem isIso_unit_of_restriction
    {L : _root_.SheafOfModules.{v} ((w.sheafPushforwardContinuous RingCat.{v} JX JY).obj O) ⥤
      _root_.SheafOfModules.{v} O}
    (adj : L ⊣ _root_.SheafOfModules.pushforward.{v}
      (𝟙 ((w.sheafPushforwardContinuous RingCat.{v} JX JY).obj O))) :
    IsIso adj.unit :=
  have := isIso_restrictionAdjunction_counit w JX JY O
  (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨adj, restrictionAdjunction w JX JY O⟩).2
    inferInstance

end Stacks.SheafOfModules

end
