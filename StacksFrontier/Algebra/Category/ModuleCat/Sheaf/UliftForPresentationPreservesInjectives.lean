module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftForPresentationSmallSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLift
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftSeparator

/-!
# The universe lift of sheaves of modules preserves injective objects

Let `R` be a sheaf of rings on a site `C`. Raising the universe of the sections of sheaves of
`R`-modules, `SheafOfModules.uliftForPresentationFunctor`, carries injective objects to injective
objects, from the universe `max v r` of the morphisms of the site and of the rings to any universe
containing the site.

The lift has no left adjoint, so this is proved through Baer's criterion in the form
`CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms_rlp`: it suffices to extend along
the subobjects of one separator of the larger category. The lift of a separator is a separator,
since the essential image of the lift is closed under subobjects
(`SheafOfModules.exists_iso_uliftForPresentationMap_of_mono`) and contains the separating family
`j_{U!} 𝒪_U` of the extensions by zero of the structure sheaf; and an extension problem along a
subobject of a lift is the lift of an extension problem in the smaller universe.

## Main results

* `SheafOfModules.injective_uliftForPresentation_of_isSeparator`: the lift of an injective sheaf
  of modules is injective, given a separator of the larger category which is a lift.
* `SheafOfModules.isSeparator_uliftForPresentation_of_isSeparator`: the lift of a separator is a
  separator.
* `SheafOfModules.uliftForPresentationFunctor_preservesInjectiveObjects`: **the universe lift of
  sheaves of modules preserves injective objects.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe z u v r m t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})

section Injective

variable [HasWeakSheafify J AddCommGrpCat.{max t m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t m}]
  [IsGrothendieckAbelian.{z} (SheafOfModules.{max t m} R)]

/-- **The universe lift of an injective sheaf of modules is injective**, as soon as the larger
category of sheaves of modules is Grothendieck abelian with a separator which is itself a
universe lift. -/
theorem injective_uliftForPresentation_of_isSeparator {G : SheafOfModules.{m} R}
    (hG : IsSeparator (uliftForPresentation.{u, v, r, m, t} G))
    (I : SheafOfModules.{m} R) [Injective I] :
    Injective (uliftForPresentation.{u, v, r, m, t} I) := by
  rw [injective_iff_rlp_monomorphisms_zero,
    ← IsGrothendieckAbelian.generatingMonomorphisms_rlp hG]
  rintro A B i ⟨T⟩
  obtain ⟨T', i', _, e, he⟩ := exists_iso_uliftForPresentationMap_of_mono T.arrow
  have key : HasLiftingProperty (uliftForPresentationMap.{u, v, r, m, t} i')
      (0 : uliftForPresentation.{u, v, r, m, t} I ⟶ 0) := by
    refine ⟨fun {f g} sq => ?_⟩
    let l := uliftForPresentationMap.{u, v, r, m, t}
      (Injective.factorThru (uliftForPresentationMapDown f) i')
    have hl : uliftForPresentationMap.{u, v, r, m, t} i' ≫ l = f := by
      rw [← uliftForPresentationMap_comp, Injective.comp_factorThru]
      exact uliftForPresentationMap_down f
    exact ⟨⟨⟨l, hl, (isZero_zero _).eq_of_tgt _ _⟩⟩⟩
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (Arrow.isoMk e (Iso.refl _) (he.trans (Category.comp_id _).symm)) _).1 key

end Injective

section Separator

open Stacks.SheafOfModules

attribute [local instance] siteHasSheafify siteWEqualsLocallyBijective

/-- The extension by zero `j_{U!} 𝒪_U` of the structure sheaf, with sections in a universe
containing the site, is the universe lift of the one with sections in the universe `max v r`. -/
theorem extensionByZeroUnit_mem_essImage_uliftForPresentationFunctor
    [HasWeakSheafify J AddCommGrpCat.{max v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max v r}] (U : C) :
    (uliftForPresentationFunctor.{u, v, r, max v r, max u v r t} (R := R)).essImage
      (extensionByZeroUnit.{u, v, r, t} R U) := by
  have := isLocallyInjective_id_structure.{u, v, r} (R := R)
  have := isLocallySurjective_id_structure.{u, v, r} (R := R)
  let e : (presheafULift.{max u v r t} R.obj).obj (extensionByZeroUnitPresheafBase R.obj U) ≅
      (extensionByZeroUnitPresheafBase R.obj U).uliftSections.{max u v r t} :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ rfl)
  exact ⟨(PresheafOfModules.sheafification.{max v r} (𝟙 R.obj)).obj
      (extensionByZeroUnitPresheafBase R.obj U),
    ⟨(PresheafOfModules.sheafificationUliftObjIso.{u, v, r, max v r, max u v r t}
        (𝟙 R.obj) (extensionByZeroUnitPresheafBase R.obj U)).symm ≪≫
      (PresheafOfModules.sheafification.{max u v r t} (𝟙 R.obj)).mapIso e.symm ≪≫
      extensionByZeroUnitULiftIso.{u, v, r, t} R U⟩⟩

/-- The extensions by zero `j_{U!} 𝒪_U` of the structure sheaf separate sheaves of modules:
morphisms out of `j_{U!} 𝒪_U` are the sections over `U` (Stacks 0G1V). -/
theorem isSeparating_ofObj_extensionByZeroUnit :
    (ObjectProperty.ofObj (extensionByZeroUnit.{u, v, r, t} R)).IsSeparating := by
  intro M N f g h
  ext X x
  have hx := congrArg (extensionByZeroUnitHomEquiv.{u, v, r, t} R X.unop N)
    (h _ ⟨X.unop⟩ ((extensionByZeroUnitHomEquiv.{u, v, r, t} R X.unop M).symm x))
  rwa [extensionByZeroUnitHomEquiv_naturality, extensionByZeroUnitHomEquiv_naturality,
    Equiv.apply_symm_apply] at hx

variable [HasSheafify J AddCommGrpCat.{max v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v r}]

/-- **The universe lift of a separator of sheaves of modules is a separator.** -/
theorem isSeparator_uliftForPresentation_of_isSeparator {G : SheafOfModules.{max v r} R}
    (hG : IsSeparator G) :
    IsSeparator (uliftForPresentation.{u, v, r, max v r, max u v r t} G) := by
  refine (uliftForPresentationFunctor.{u, v, r, max v r, max u v r t}
    (R := R)).isSeparator_obj_of_isSeparating (fun {A S} i hi ↦ ?_)
    (isSeparating_ofObj_extensionByZeroUnit.{u, v, r, t} R) ?_ hG
  · let i₀ : S ⟶ uliftForPresentation.{u, v, r, max v r, max u v r t} A := i
    have : Mono i₀ := hi
    obtain ⟨S', i', _, e, he⟩ := exists_iso_uliftForPresentationMap_of_mono i₀
    exact ⟨S', i', e, he⟩
  · rintro _ ⟨U⟩
    exact extensionByZeroUnit_mem_essImage_uliftForPresentationFunctor.{u, v, r, t} R U

/-- **The universe lift of sheaves of modules preserves injective objects**, from the universe
`max v r` of the morphisms of the site and of the rings to any universe containing the site, as
soon as sheaves of modules in the smaller universe have a separator. -/
theorem uliftForPresentationFunctor_preservesInjectiveObjects
    [HasSeparator (SheafOfModules.{max v r} R)] :
    (uliftForPresentationFunctor.{u, v, r, max v r, max u v r t} (R := R)).PreservesInjectiveObjects
    where
  injective_obj {I} _ := by
    have : IsGrothendieckAbelian.{max u v r t} (SheafOfModules.{max u v r t} R) :=
      isGrothendieckAbelian_of_univLE.{max u v r t, v, u, r} R
    exact injective_uliftForPresentation_of_isSeparator.{max u v r t, u, v, r, max v r,
      max u v r t} R (isSeparator_uliftForPresentation_of_isSeparator.{u, v, r, t} R
        (isSeparator_separator _)) I

end Separator

end SheafOfModules

end
