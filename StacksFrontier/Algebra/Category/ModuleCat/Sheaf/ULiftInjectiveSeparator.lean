module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseShrink
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftSeparator

/-!
# The universe lift of sheaves of modules into a larger universe preserves injectives

A fully faithful functor between abelian categories whose essential image is closed under
subobjects, with Grothendieck abelian target, carries injective objects to injective objects
as soon as it carries some object to a separator. Applied to the universe lift of sheaves of
modules from the universe `max v₁ w` of the hom-sets of the site and of the rings to any
larger universe, with the extensions by zero `j_{U!} 𝒪_U` as separating family, this shows that
the lift preserves injective objects.

## Main results

* `CategoryTheory.Functor.preservesInjectiveObjects_of_isSeparator_obj`
* `Stacks.SheafOfModules.isSeparator_moduleULift_max_obj`
* `Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift_max`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open ZeroObject

universe z t v w u₁ v₁

namespace CategoryTheory.Functor

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ] {L : 𝒜 ⥤ ℬ}
  (hL : L.FullyFaithful)
  (hsub : ∀ {A : 𝒜} {S : ℬ} (i : S ⟶ L.obj A) [Mono i],
      ∃ (S' : 𝒜) (i' : S' ⟶ A) (e : L.obj S' ≅ S), e.hom ≫ i = L.map i')

omit [Abelian 𝒜] in
include hL hsub in
/-- **A fully faithful functor whose essential image is closed under subobjects carries
injective objects to injective objects**, provided its target is Grothendieck abelian and it
carries some object to a separator. -/
theorem injective_obj_of_isSeparator_obj [IsGrothendieckAbelian.{z} ℬ] {G : 𝒜}
    (hG : IsSeparator (L.obj G)) (I : 𝒜) [Injective I] : Injective (L.obj I) := by
  have := hL.faithful
  rw [injective_iff_rlp_monomorphisms_zero,
    ← IsGrothendieckAbelian.generatingMonomorphisms_rlp hG]
  rintro A B i ⟨T⟩
  obtain ⟨T', i', e, he⟩ := hsub T.arrow
  have : Mono i' := L.mono_of_mono_map (by rw [← he]; infer_instance)
  have key : HasLiftingProperty (L.map i') (0 : L.obj I ⟶ 0) := ⟨fun {f _} _ ↦
    ⟨⟨{ l := L.map (Injective.factorThru (hL.preimage f) i')
        fac_left := by rw [← Functor.map_comp, Injective.comp_factorThru, hL.map_preimage]
        fac_right := (isZero_zero _).eq_of_tgt _ _ }⟩⟩⟩
  have e' : Arrow.mk (L.map i') ≅ Arrow.mk (Subobject.arrow T) :=
    Arrow.isoMk e (Iso.refl _) (he.trans (Category.comp_id _).symm)
  exact (HasLiftingProperty.iff_of_arrow_iso_left e' _).1 key

omit [Abelian 𝒜] in
include hL hsub in
/-- `CategoryTheory.Functor.injective_obj_of_isSeparator_obj`, as preservation of injective
objects. -/
theorem preservesInjectiveObjects_of_isSeparator_obj [IsGrothendieckAbelian.{z} ℬ] {G : 𝒜}
    (hG : IsSeparator (L.obj G)) : L.PreservesInjectiveObjects where
  injective_obj {X} _ := injective_obj_of_isSeparator_obj hL hsub hG X

end CategoryTheory.Functor

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

/-- **A subobject of a universe lift of a sheaf of modules is a universe lift**: its sections
inject into lifted sections, so they are small, and the sheaf is the lift of its shrink. -/
theorem exists_moduleULift_descent {M : _root_.SheafOfModules.{v} R}
    {S : _root_.SheafOfModules.{max v t} R} (i : S ⟶ (moduleULift.{t, v} R).obj M) [Mono i] :
    ∃ (S' : _root_.SheafOfModules.{v} R) (i' : S' ⟶ M) (e : (moduleULift.{t, v} R).obj S' ≅ S),
      e.hom ≫ i = (moduleULift.{t, v} R).map i' := by
  have (U : Cᵒᵖ) : Small.{v} (S.val.obj U) := by
    have : Small.{v} (((moduleULift.{t, v} R).obj M).val.obj U) :=
      inferInstanceAs (Small.{v} (ULift.{t} (M.val.obj U)))
    exact small_of_injective (injective_app_of_mono i U)
  let e : (moduleULift.{t, v} R).obj (_root_.SheafOfModules.shrinkSame.{v} S) ≅ S :=
    _root_.SheafOfModules.uliftShrinkIso.{v} S
  exact ⟨_, (moduleULiftFullyFaithful.{t, v} R).preimage (e.hom ≫ i), e,
    ((moduleULiftFullyFaithful.{t, v} R).map_preimage _).symm⟩

/-- **The universe lift of sheaves of modules preserves limits indexed by small categories**:
they are computed on the underlying presheaves of abelian groups, where the lift is
postcomposition with `AddCommGrpCat.uliftFunctor`. -/
instance preservesLimitsOfShape_moduleULift (I : Type) [SmallCategory I] :
    PreservesLimitsOfShape I (moduleULift.{t, v} R) := by
  let G := _root_.SheafOfModules.forget.{max v t} R ⋙ PresheafOfModules.toPresheaf R.obj
  have hG : PreservesLimitsOfShape I (moduleULift.{t, v} R ⋙ G) := by
    change PreservesLimitsOfShape I
      ((_root_.SheafOfModules.forget.{v} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{v} AddCommGrpCat.{max v t}).obj
          AddCommGrpCat.uliftFunctor.{t, v})
    infer_instance
  have : ReflectsLimitsOfShape I G := reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves (moduleULift.{t, v} R) G

attribute [local instance] siteHasSheafify siteWEqualsLocallyBijective

/-- **The extensions by zero `j_{U!} 𝒪_U` form a separating family** of the sheaves of modules
in their universe: a morphism out of `j_{U!} 𝒪_U` is a section over `U` (Stacks 0G1V). -/
theorem isSeparating_extensionByZeroUnit :
    ObjectProperty.IsSeparating (.ofObj (extensionByZeroUnit.{u₁, v₁, w, t} R) :
      ObjectProperty (_root_.SheafOfModules.{max u₁ v₁ w t} R)) := by
  intro M N f₁ f₂ h
  ext U x
  have hψ := h _ ⟨U.unop⟩ ((extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U.unop M).symm x)
  have h₁ := extensionByZeroUnitHomEquiv_naturality.{u₁, v₁, w, t} R U.unop
    ((extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U.unop M).symm x) f₁
  have h₂ := extensionByZeroUnitHomEquiv_naturality.{u₁, v₁, w, t} R U.unop
    ((extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U.unop M).symm x) f₂
  rw [Equiv.apply_symm_apply] at h₁ h₂
  rw [hψ] at h₁
  exact h₁.symm.trans h₂

variable [HasWeakSheafify J AddCommGrpCat.{max v₁ w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v₁ w}]

/-- **`j_{U!} 𝒪_U` is a universe lift**: the universe lift of the sheafification of the presheaf
`X ↦ (X ⟶ U) →₀ R(X)` in the universe `max v₁ w`. -/
def extensionByZeroUnitIsoModuleULift (U : C) :
    (moduleULift.{max u₁ v₁ w t, max v₁ w} R).obj
        ((PresheafOfModules.sheafification.{max v₁ w} (𝟙 R.obj)).obj
          (extensionByZeroUnitPresheafBase R.obj U)) ≅
      extensionByZeroUnit.{u₁, v₁, w, t} R U :=
  (asIso (PresheafOfModules.sheafifyULiftHom.{_, _, _, _, max u₁ v₁ w t} (𝟙 R.obj)
    (extensionByZeroUnitPresheafBase R.obj U))).symm ≪≫
      extensionByZeroUnitULiftIso.{u₁, v₁, w, t} R U

/-- The universe lift of a separator of the sheaves of modules in the universe `max v₁ w` is a
separator of those in the universe `max u₁ v₁ w t`. -/
theorem isSeparator_moduleULift_max_obj {G : _root_.SheafOfModules.{max v₁ w} R}
    (hG : IsSeparator G) :
    IsSeparator ((moduleULift.{max u₁ v₁ w t, max v₁ w} R).obj G) := by
  have := (moduleULiftFullyFaithful.{max u₁ v₁ w t, max v₁ w} R).full
  have := (moduleULiftFullyFaithful.{max u₁ v₁ w t, max v₁ w} R).faithful
  refine (moduleULift.{max u₁ v₁ w t, max v₁ w} R).isSeparator_obj_of_isSeparating
    (fun i _ ↦ exists_moduleULift_descent R i) (isSeparating_extensionByZeroUnit.{t} R) ?_ hG
  rintro _ ⟨U⟩
  exact ⟨_, ⟨extensionByZeroUnitIsoModuleULift.{t} R U⟩⟩

/-- **The universe lift of sheaves of modules preserves injective objects**, from the universe
`max v₁ w` of the hom-sets of the site and of the rings to any universe containing the objects of
the site, provided the modules in the smaller universe have a separator. -/
theorem preservesInjectiveObjects_moduleULift_max
    [HasSeparator (_root_.SheafOfModules.{max v₁ w} R)] :
    (moduleULift.{max u₁ v₁ w t, max v₁ w} R).PreservesInjectiveObjects :=
  have := _root_.SheafOfModules.isGrothendieckAbelian_of_univLE.{max u₁ v₁ w t} R
  Functor.preservesInjectiveObjects_of_isSeparator_obj (moduleULiftFullyFaithful R)
    (fun i _ ↦ exists_moduleULift_descent R i)
    (isSeparator_moduleULift_max_obj.{t} R (isSeparator_separator _))

end Stacks.SheafOfModules
