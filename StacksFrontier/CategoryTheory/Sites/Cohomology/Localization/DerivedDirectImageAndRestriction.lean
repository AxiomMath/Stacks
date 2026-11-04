module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteMorphismLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.MorphismLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image and restriction to a localized site

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites, given by a continuous functor
`u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`. Let
`g : (C/U, O_U) ⟶ (D/V, O_V)` be the localized morphism of ringed sites of Stacks 04J0. Then
restricting the unbounded derived direct image `Rf_*` to `D/V` agrees with the derived direct
image `Rg_*` of the restriction to `C/U`.

The proof is the one of the source. Both sides are right derived functors of the same functor on
the unbounded homotopy category of `O_C`-modules, because:

* the underived identity `(f_*F)|_{D/V} = g_*(F|_{C/U})` holds, by the definition of the
  structure map of the localized morphism (Stacks 04J0) and because the functor identity
  `u' ∘ j_V = j_U ∘ u` of Stacks 03CF is strict;
* restriction is exact, so the comparison from degreewise restriction to the derived
  restriction is invertible and the left-hand composite computes `Rf_*` followed by naive
  restriction; and
* restriction carries K-injective complexes to K-injective complexes (Stacks 08FI), so on a
  K-injective complex the comparison for `Rg_*` on the right-hand composite is invertible
  as well.

## Main definitions

All in the namespace `Stacks.Cohomology.Localization`.

* `localizedPushforward`: the direct image of sheaves of modules along `g`.
* `derivedLocalizedPushforward`: the unbounded derived direct image along `g`.

## Main results

All in the namespace `Stacks.Cohomology.Localization`.

* `isIso_of_isRightDerivedFunctor_of_exact`: an exact functor needs no derivation — the
  comparison from its degreewise extension to any right derived functor of it is invertible.
* `isRightDerivedFunctor_comp_of_kInjectives`: the composite of two right derived functors is a
  right derived functor of the composite of the two degreewise functors, under the two
  invertibility conditions the argument above supplies.
* `fSharpRing_localized`: the structure map of the localized morphism of ringed sites, on
  sheaves of not necessarily commutative rings, is the restriction of the structure map.
* `pushforwardTopos_comp_overFunctor`: the underived identity
  `(f_*F)|_{D/V} = g_*(F|_{C/U})`.
* `derivedPushforwardOverFunctorIso`: **Stacks 0D6G**, the derived statement.

## Implementation notes

The derived direct image is the one of
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward`, which exists for
every morphism of ringed topoi with no further hypothesis; a morphism of ringed sites is read as
such a morphism by `AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom`. So neither the
statement nor the proof assumes that any functor computes its derived functor. The derived
restriction is `Stacks.Cohomology.Localization.derivedRestriction`.

The structure sheaf of the localized ringed site `C/U` and the restriction to `C/U` of the
structure sheaf of `C` are the same sheaf of rings by definition, but not after the reductions
instance search performs, so a statement written with one of the two spellings does not accept
the instances available for the other. `localizedPushforward` and `derivedLocalizedPushforward`
pin the spelling to the restriction, which is the one in which `derivedRestriction` takes its
values.

The three universes of the ringed sites are collapsed, as they are in
`AlgebraicGeometry.RingedSite.Hom` and in the derived development: the localized site `C/U` has
objects in the universe of the objects and the morphisms of `C`, and the sheaves of modules on
`C` and on `C/U` must take their sections in one universe for the direct image between them to
be defined.

## References

* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.Localization

universe u v w u₁ u₂ u₃ v₁ v₂ v₃ wA wB wC

section Exact

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]

/-- An exact functor needs no derivation: the canonical comparison from its degreewise extension
to the homotopy category into any right derived functor of it is an isomorphism, because the
exact functor already descends to the unbounded derived categories. -/
theorem isIso_of_isRightDerivedFunctor_of_exact (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    IsIso α := by
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let _ : F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv W :=
    Functor.isRightDerivedFunctor_of_inverts W F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  have he : F.mapDerivedCategoryFactorsh.inv ≫
      (Functor.isoWhiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedUnique F.mapDerivedCategory RF
          F.mapDerivedCategoryFactorsh.inv α W)).hom = α := by
    simp
  rw [← he]
  infer_instance

end Exact

section Composite

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory.{wA} A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{wB} B] {C : Type u₃} [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{wC} C]

/-- The composite of two right derived functors is a right derived functor of the composite of
the two degreewise functors, as soon as the comparison for the first is invertible on K-injective
complexes and the comparison for the second is invertible on their images. -/
theorem isRightDerivedFunctor_comp_of_kInjectives
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B) (RG : DerivedCategory B ⥤ DerivedCategory C)
    (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (hF : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      IsIso (αF.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (hG : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      IsIso (αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) :
    (RF ⋙ RG).IsRightDerivedFunctor
      (Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) αG ≫
        Functor.whiskerRight αF RG)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  have _ := hF I
  have _ := hG I
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

end Composite

section RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- Continuity of `Over.post u`, the functor underlying the localized morphism of ringed sites.
This is Stacks 03CF clause (a); it is restated here in the shape instance search keys on. -/
local instance isContinuous_overPost :
    (Over.post (X := V) f.u).IsContinuous (Y.J.over V) (X.J.over (f.u.obj V)) :=
  (f.localized V).isContinuous

/-- The direct image of sheaves of modules along the localized morphism of ringed sites of
Stacks 04J0, with its source and target written as the restrictions to the localized sites of
the sheaves of rings of `X` and of `Y`. That is the spelling in which the restriction functor
`CategoryTheory.SheafOfModules.overFunctor` takes its values; the structure sheaf of a localized
ringed site is the same thing by definition, but not by the reductions instance search
performs. -/
noncomputable abbrev localizedPushforward :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj V)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V) :=
  (f.localized V).toRingedToposSiteHom.pushforwardTopos

/-- The unbounded derived direct image along the localized morphism of ringed sites, with its
source and target written as in `Stacks.Cohomology.Localization.localizedPushforward`. -/
noncomputable abbrev derivedLocalizedPushforward :
    DerivedCategory
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj V))) ⥤
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V)) :=
  derivedPushforward.{u} (f.localized V).toRingedToposSiteHom

attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

/-- The localized pushforward `Stacks.Cohomology.Localization.localizedPushforward` is additive. -/
local instance additive_localizedPushforward : (localizedPushforward f V).Additive :=
  RingedToposSiteHom.pushforwardTopos_additive.{u} _

/-- Restriction to the localized site followed by the localized pushforward is additive. -/
local instance additive_overFunctor_comp_localizedPushforward :
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj V) ⋙
      localizedPushforward f V).Additive where
  map_add := by intros; rfl

/-- **Stacks 04J0** on sheaves of not necessarily commutative rings: the structure map of the
localized morphism of ringed sites is the restriction of the structure map of the given
morphism. -/
theorem fSharpRing_localized :
    (f.localized V).toRingedToposSiteHom.fSharpRing =
      (Y.J.overPullback RingCat.{u} V).map f.toRingedToposSiteHom.fSharpRing := by
  apply Sheaf.hom_ext
  ext W x
  rfl

/-- **The underived identity behind Stacks 0D6G:** the direct image of a sheaf of modules along
a morphism of ringed sites, restricted to the site localized at an object `V` of the target, is
the direct image along the localized morphism of the restriction to the localization at `u(V)`.
As in the source this is an equality of functors, not merely an isomorphism: the functor identity
`u' ∘ j_V = j_U ∘ u` of Stacks 03CF is strict. -/
theorem pushforwardTopos_comp_overFunctor :
    f.toRingedToposSiteHom.pushforwardTopos ⋙
        SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V =
      SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj V) ⋙
        localizedPushforward f V := by
  have e : RingedSite.MorphismLocalization.localizedStructureMap f.u X.J Y.J V
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) f.toRingedToposSiteHom.fSharpRing
      = (f.localized V).toRingedToposSiteHom.fSharpRing :=
    (RingedSite.MorphismLocalization.localizedStructureMap_eq f.u X.J Y.J V
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      f.toRingedToposSiteHom.fSharpRing).trans (fSharpRing_localized f V).symm
  have h := RingedSite.MorphismLocalization.pushforward_overPullback_comm_modules
    f.u X.J Y.J V (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) f.toRingedToposSiteHom.fSharpRing
  rw [e] at h
  exact h.symm

/-- The comparison from degreewise direct image followed by degreewise restriction into the
derived direct image followed by the derived restriction. -/
noncomputable def pushforwardRestrictionUnit :
    f.toRingedToposSiteHom.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        homotopyRestriction Y V ⟶
      DerivedCategory.Qh ⋙
        (derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedRestriction Y V) :=
  Functor.whiskerLeft
      (f.toRingedToposSiteHom.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ))
      ((homotopyRestriction Y V).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))) ≫
    Functor.whiskerRight (derivedPushforwardUnit.{u} f.toRingedToposSiteHom)
      (derivedRestriction Y V)

/-- The comparison from degreewise restriction followed by degreewise direct image along the
localized morphism into the derived restriction followed by its derived direct image. -/
noncomputable def restrictionPushforwardUnit :
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (f.u.obj V)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (localizedPushforward f V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        (derivedRestriction X (f.u.obj V) ⋙ derivedLocalizedPushforward f V) :=
  Functor.whiskerLeft
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (f.u.obj V)).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedPushforwardUnit.{u} (f.localized V).toRingedToposSiteHom) ≫
    Functor.whiskerRight
      ((homotopyRestriction X (f.u.obj V)).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)))
      (derivedLocalizedPushforward f V)

/-- The derived direct image followed by the derived restriction is a right derived functor of
degreewise direct image followed by degreewise restriction. On a K-injective complex the
comparison for the direct image is invertible, and the one for the restriction is invertible
everywhere because restriction is exact. -/
instance isRightDerivedFunctor_pushforwardRestrictionUnit :
    letI : (DerivedCategory.Qh
          (C := SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O))).IsLocalization
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) :=
      DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso
        (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O))
    (derivedPushforward.{u} f.toRingedToposSiteHom ⋙
        derivedRestriction Y V).IsRightDerivedFunctor (pushforwardRestrictionUnit f V)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) :=
  letI : (DerivedCategory.Qh
        (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O))).IsLocalization
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) :=
    DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O))
  letI : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V).Additive :=
    additive_overFunctor.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V
  @isRightDerivedFunctor_comp_of_kInjectives _ _ _ _ _ _ _ _ _ _ _ _ _
    f.toRingedToposSiteHom.pushforwardTopos
    (RingedToposSiteHom.pushforwardTopos_additive.{u} f.toRingedToposSiteHom)
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V)
    (additive_overFunctor.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V)
    (derivedPushforward.{u} f.toRingedToposSiteHom) (derivedRestriction Y V)
    (derivedPushforwardUnit.{u} f.toRingedToposSiteHom)
    ((homotopyRestriction Y V).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)))
    (fun I hI => isIso_derivedPushforwardUnit_app_of_isKInjective.{u}
      f.toRingedToposSiteHom I hI)
    (fun I _ =>
      (NatTrans.isIso_iff_isIso_app _).1
        (isIso_of_isRightDerivedFunctor_of_exact
          (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V)
          (derivedRestriction Y V)
          ((homotopyRestriction Y V).totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              (ComplexShape.up ℤ))))
        ((f.toRingedToposSiteHom.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))

/-- The derived restriction followed by the derived direct image along the localized morphism is
a right derived functor of degreewise restriction followed by degreewise direct image. The
restriction of a K-injective complex is K-injective (Stacks 08FI), so the comparison for the
direct image is invertible on it; the one for the restriction is invertible everywhere because
restriction is exact. -/
instance isRightDerivedFunctor_restrictionPushforwardUnit :
    letI := DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (derivedRestriction X (f.u.obj V) ⋙
        derivedLocalizedPushforward f V).IsRightDerivedFunctor
      (restrictionPushforwardUnit f V)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) :=
  letI := DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  letI : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (f.u.obj V)).Additive :=
    additive_overFunctor.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj V)
  isRightDerivedFunctor_comp_of_kInjectives _ _ _ _ _ _
    (fun _ _ => by
      have _ := isIso_of_isRightDerivedFunctor_of_exact
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj V))
        (derivedRestriction X (f.u.obj V))
        ((homotopyRestriction X (f.u.obj V)).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)))
      infer_instance)
    (fun I _ =>
      isIso_derivedPushforwardUnit_app_of_isKInjective.{u}
        (f.localized V).toRingedToposSiteHom _
        (isKInjective_over X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj V) I))

/-- The underived identity, read on the homotopy categories of cochain complexes. -/
noncomputable def homotopyPushforwardRestrictionIso :
    f.toRingedToposSiteHom.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (f.u.obj V)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (localizedPushforward f V).mapHomotopyCategory (ComplexShape.up ℤ) :=
  letI : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V).Additive :=
    additive_overFunctor.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V
  letI : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (f.u.obj V)).Additive :=
    additive_overFunctor.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj V)
  @Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
      (eqToIso (pushforwardTopos_comp_overFunctor f V)) inferInstance
      (additive_overFunctor.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V)
      (additive_overFunctor_comp_localizedPushforward f V)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj V) ⋙
          localizedPushforward f V)) (ComplexShape.up ℤ)).symm

/-- **Stacks 0D6G.** For a morphism of ringed sites `f : (C, O_C) ⟶ (D, O_D)` given by the
continuous functor `u : D ⥤ C`, an object `V` of `D` and `U = u(V)`, restricting the unbounded
derived direct image `Rf_*` to the localized site `D/V` is the derived direct image `Rg_*` along
the localized morphism `g : (C/U, O_U) ⟶ (D/V, O_V)` of Stacks 04J0 of the restriction to
`C/U`. -/
@[stacks 0D6G]
noncomputable def derivedPushforwardOverFunctorIso :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedRestriction Y V ≅
      derivedRestriction X (f.u.obj V) ⋙ derivedLocalizedPushforward f V :=
  @Functor.rightDerivedNatIso _ _ _ _ _ _ _ _ _ _ _
    (pushforwardRestrictionUnit f V) (restrictionPushforwardUnit f V)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso
    (isRightDerivedFunctor_pushforwardRestrictionUnit f V)
    (isRightDerivedFunctor_restrictionPushforwardUnit f V)
    (Functor.isoWhiskerRight (homotopyPushforwardRestrictionIso f V) DerivedCategory.Qh)

/-- **The isomorphism of Stacks 0D6G is compatible with the two comparison transformations it
is derived from.** On a cochain complex `K`, the comparison from degreewise direct image
followed by degreewise restriction, followed by the isomorphism, is the underived identity
followed by the comparison from degreewise restriction followed by degreewise direct image.

This is the defining property of the isomorphism, and the form in which it enters a uniqueness
argument: `Stacks.Cohomology.Localization.derivedPushforwardOverFunctorIso` is built by
`CategoryTheory.Functor.rightDerivedNatIso`, so it is the *unique* natural transformation with
this property, by
`Stacks.Cohomology.Localization.eq_derivedPushforwardOverFunctorIso_hom_of_unit_comp`. Without
it the isomorphism cannot be compared with any other map between the same two functors. -/
@[reassoc]
theorem pushforwardRestrictionUnit_comp_derivedPushforwardOverFunctorIso_hom_app
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    (pushforwardRestrictionUnit f V).app K ≫
        (derivedPushforwardOverFunctorIso f V).hom.app (DerivedCategory.Qh.obj K) =
      (Functor.isoWhiskerRight (homotopyPushforwardRestrictionIso f V)
            DerivedCategory.Qh).hom.app K ≫
        (restrictionPushforwardUnit f V).app K := by
  dsimp only [derivedPushforwardOverFunctorIso]
  rw [Functor.rightDerivedNatIso_hom]
  exact Functor.rightDerivedNatTrans_app _ _ _ _ _ _ K

/-- The same compatibility for the inverse of the isomorphism of Stacks 0D6G. -/
@[reassoc]
theorem restrictionPushforwardUnit_comp_derivedPushforwardOverFunctorIso_inv_app
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    (restrictionPushforwardUnit f V).app K ≫
        (derivedPushforwardOverFunctorIso f V).inv.app (DerivedCategory.Qh.obj K) =
      (Functor.isoWhiskerRight (homotopyPushforwardRestrictionIso f V)
            DerivedCategory.Qh).inv.app K ≫
        (pushforwardRestrictionUnit f V).app K := by
  dsimp only [derivedPushforwardOverFunctorIso]
  rw [Functor.rightDerivedNatIso_inv]
  exact Functor.rightDerivedNatTrans_app _ _ _ _ _ _ K

/-- **Uniqueness of the isomorphism of Stacks 0D6G.** Any natural transformation between the two
functors satisfying the compatibility of
`pushforwardRestrictionUnit_comp_derivedPushforwardOverFunctorIso_hom_app` is the forward map of
`Stacks.Cohomology.Localization.derivedPushforwardOverFunctorIso`. -/
theorem eq_derivedPushforwardOverFunctorIso_hom_of_unit_comp
    (θ : derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedRestriction Y V ⟶
      derivedRestriction X (f.u.obj V) ⋙ derivedLocalizedPushforward f V)
    (hθ : pushforwardRestrictionUnit f V ≫ Functor.whiskerLeft DerivedCategory.Qh θ =
      (Functor.isoWhiskerRight (homotopyPushforwardRestrictionIso f V)
          DerivedCategory.Qh).hom ≫ restrictionPushforwardUnit f V) :
    θ = (derivedPushforwardOverFunctorIso f V).hom := by
  refine Functor.rightDerived_ext _ (pushforwardRestrictionUnit f V)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    _ _ _ ?_
  rw [hθ]
  ext K
  exact (pushforwardRestrictionUnit_comp_derivedPushforwardOverFunctorIso_hom_app f V K).symm

end RingedSite

end Stacks.Cohomology.Localization

end
