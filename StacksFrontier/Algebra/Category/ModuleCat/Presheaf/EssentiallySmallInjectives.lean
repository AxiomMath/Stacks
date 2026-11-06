module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LocallySmall
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Presheaves of modules on an essentially small category have enough injectives

Let `C` be a category with morphisms in `Type u` which is essentially small relative to `u`,
and let `R` be a presheaf of rings on `C` with values in `RingCat.{u}`. Then the category
`PresheafOfModules.{u} R` is a Grothendieck abelian category, and in particular it has enough
injectives.

Mathlib states this for a small category `C : Type u` (in
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules`); here the objects of `C` may
live in a larger universe, as do the algebras of a big site, whose objects are rings in `Type u`
subject to a cardinality bound.

## Main results

* `PresheafOfModules.isSeparating_freeYoneda_smallModel`: the free presheaves of modules on the
  representable presheaves of the objects of a small model of `C` form a separating family.
* `PresheafOfModules.isGrothendieckAbelian_of_essentiallySmall`: `PresheafOfModules.{u} R` is
  Grothendieck abelian.
* `PresheafOfModules.enoughInjectives_of_essentiallySmall`: it has enough injectives.

## Implementation notes

Local smallness is `PresheafOfModules.locallySmall_of_essentiallySmall`; filtered colimits and
their exactness are computed in presheaves of abelian groups, as for a small category. The
separator is a coproduct of free presheaves of modules on representables: Mathlib's separating
family `PresheafOfModules.freeYoneda R` is indexed by all objects of `C`, and every member is
isomorphic to one indexed by the small model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u u₁

namespace PresheafOfModules

variable {C : Type u₁} [Category.{u} C] [EssentiallySmall.{u} C] (R : Cᵒᵖ ⥤ RingCat.{u})

/-- The free presheaves of modules on the representable presheaves of the objects of a small
model of an essentially small category form a separating family. -/
theorem isSeparating_freeYoneda_smallModel :
    (ObjectProperty.ofObj fun X : SmallModel.{u} C =>
      (free R).obj (yoneda.obj ((equivSmallModel.{u} C).inverse.obj X))).IsSeparating := by
  intro M N f g h
  refine freeYoneda.isSeparating R f g fun G hG k => ?_
  obtain ⟨X⟩ := hG
  let i : (free R).obj (yoneda.obj X) ≅ (free R).obj (yoneda.obj
      ((equivSmallModel.{u} C).inverse.obj ((equivSmallModel.{u} C).functor.obj X))) :=
    (free R).mapIso (yoneda.mapIso ((equivSmallModel.{u} C).unitIso.app X))
  have hk := congrArg (i.hom ≫ ·)
    (h _ (ObjectProperty.ofObj.mk ((equivSmallModel.{u} C).functor.obj X)) (i.inv ≫ k))
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hk

/-- **Presheaves of modules on an essentially small category form a Grothendieck abelian
category.** -/
theorem isGrothendieckAbelian_of_essentiallySmall :
    IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R) where
  locallySmall := locallySmall_of_essentiallySmall R
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun J _ _ ↦ ⟨⟨fun _ _ _ ↦ ⟨fun {F} ↦
    have : PreservesLimit F (colim (J := J) ⋙ toPresheaf R) :=
      preservesLimit_of_natIso _ (preservesColimitNatIso (toPresheaf R)).symm
    preservesLimit_of_reflects_of_preserves _ (toPresheaf R)⟩⟩⟩⟩
  hasSeparator := ⟨_, (isSeparating_freeYoneda_smallModel R).isSeparator_coproduct⟩

/-- **Presheaves of modules on an essentially small category have enough injectives.** -/
@[sga "3 I 3.1.2" "more general"]
theorem enoughInjectives_of_essentiallySmall : EnoughInjectives (PresheafOfModules.{u} R) :=
  have := isGrothendieckAbelian_of_essentiallySmall R
  inferInstance

end PresheafOfModules

end
