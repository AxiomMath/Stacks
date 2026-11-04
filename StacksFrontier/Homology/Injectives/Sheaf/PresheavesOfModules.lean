module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Category.ULift
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Equivalence
public import StacksFrontier.Homology.Injectives.Sheaf.ModulesOnRingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Injectives in the category of presheaves of modules

Let `R` be a presheaf of rings on a category `C`. The category of presheaves of
`R`-modules has functorial injective embeddings, hence in particular enough injectives.

The proof reduces to the sheaf case, Stacks 01DU, through three equivalences of abelian
categories, each of which transports functorial injective embeddings by
`hasFunctorialInjectiveEmbeddings_of_equivalence`, the equivalence form of Stacks 0161:

* a presheaf is the same thing as a sheaf for the trivial (bottom) Grothendieck topology, so
  presheaves of `R`-modules on a small site are sheaves of modules over `R` viewed as a sheaf
  of rings for `⊥`, which is where 01DU applies;
* replacing `C` by its small model `AsSmall C` does not change the category of presheaves of
  modules, the comparison being pushforward along the two functors of `AsSmall.equiv`;
* restricting scalars along `ULift.ringEquiv` identifies presheaves of modules over `R` with
  presheaves of modules over the universe-lifted presheaf of rings, which brings the ring
  universe up to the ambient one.

The last two equivalences say nothing about injectives and are stated here for reuse, with
every universe independent: they are the two moves by which a statement about presheaves of
modules on an arbitrary site, over a presheaf of rings in an arbitrary universe, is reduced to
the small-site case in which Mathlib states its results.

## Main definitions

* `Stacks.Injectives.ringCatUlift`: universe lifting of rings, as a functor of `RingCat`.
* `Stacks.Injectives.presheafOfModulesUliftEquiv`: presheaves of modules over `R` are the same
  as presheaves of modules over the universe-lifted `R`.
* `Stacks.Injectives.presheafOfModulesAsSmallEquiv`: presheaves of modules over a site are the
  same as presheaves of modules over its small model.

## Main results

* `Stacks.Injectives.presheafOfModules_hasFunctorialInjectiveEmbeddings`: the category of
  presheaves of modules over a presheaf of rings has functorial injective embeddings.

## Implementation notes

Presheaves of modules are Mathlib's `PresheafOfModules R`, and functorial injective
embeddings are the Stacks 0139 predicate `HasFunctorialInjectiveEmbeddings`.

In the main theorem the three universes `u` (objects of `C`), `v` (morphisms of `C`) and `w`
(the presheaf of rings) are independent, and the modules live in `max u v w`: making the site
small raises the object universe to `max u v`, and viewing a presheaf of rings as a sheaf of
rings for the trivial topology on a small site forces the ring and the modules into the
universe of that site. The two auxiliary equivalences are stated with the module universe
independent of all of these, since that is what a consumer other than this file will need.

## References

* [Stacks Project, Tag 01DV](https://stacks.math.columbia.edu/tag/01DV)
-/

@[expose] public section

open CategoryTheory

universe u v w t s

namespace Stacks.Injectives

/-- Sheaves of modules for the trivial topology on a small site are presheaves of modules. -/
private def sheafOfModulesBotEquiv {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    SheafOfModules.{u} (⟨R, Presheaf.isSheaf_bot R⟩ : Sheaf (⊥ : GrothendieckTopology C) _) ≌
      PresheafOfModules.{u} R where
  functor := SheafOfModules.forget _
  inverse :=
    { obj := fun M => ⟨M, Presheaf.isSheaf_bot M.presheaf⟩
      map := fun f => ⟨f⟩ }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

/-- Stacks 01DV on a small site whose presheaf of rings lives in the universe of that site:
here a presheaf of modules is a sheaf of modules for the trivial topology, so 01DU applies. -/
private theorem presheafOfModules_hasFunctorialInjectiveEmbeddings_of_small
    {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    HasFunctorialInjectiveEmbeddings (PresheafOfModules.{u} R) := by
  let e := sheafOfModulesBotEquiv R
  have : e.functor.Additive := ⟨by intro X Y f g; ext; rfl⟩
  exact hasFunctorialInjectiveEmbeddings_of_equivalence e
    (sheafOfModules_hasFunctorialInjectiveEmbeddings ⊥ _)

/-- Universe lifting of rings, as a functor `RingCat.{w} ⥤ RingCat.{max t w}`. -/
def ringCatUlift.{w', t'} : RingCat.{w'} ⥤ RingCat.{max t' w'} where
  obj R := RingCat.of (ULift.{max t' w', w'} R)
  map f := RingCat.ofHom <|
    (ULift.ringEquiv (R := _)).symm.toRingHom.comp
      (f.hom.comp (ULift.ringEquiv (R := _)).toRingHom)
  map_id R := by ext r; rfl
  map_comp f g := by ext r; rfl

section Ulift

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{w})

/-- Restriction of scalars along `ULift.ringEquiv.symm`, sectionwise: a presheaf of modules
over the universe-lifted presheaf of rings is one over `R` itself. -/
noncomputable def presheafOfModulesUliftFunctor :
    PresheafOfModules.{max t w} (R ⋙ ringCatUlift.{w, t}) ⥤
      PresheafOfModules.{max t w} R where
  obj M := {
    obj X := (ModuleCat.restrictScalars
      (ULift.ringEquiv.symm : R.obj X ≃+* ULift.{max t w, w} (R.obj X)).toRingHom).obj (M.obj X)
    map {X Y} f := by
      let eX := (ULift.ringEquiv.symm : R.obj X ≃+* ULift.{max t w, w} (R.obj X))
      exact (ModuleCat.restrictScalars eX.toRingHom).map (M.map f)
    map_id X := by ext x; change M.map (𝟙 X) x = x; rw [M.map_id]; rfl
    map_comp {X Y Z} f g := by
      ext x; change M.map (f ≫ g) x = M.map g (M.map f x)
      exact M.map_comp_apply f g x
  }
  map {M N} f := {
    app X := (ModuleCat.restrictScalars
      (ULift.ringEquiv.symm : R.obj X ≃+* ULift.{max t w, w} (R.obj X)).toRingHom).map (f.app X)
    naturality := by intro X Y g; ext x; exact PresheafOfModules.naturality_apply f g x
  }

/-- Restriction of scalars along `ULift.ringEquiv`, inverse to
`presheafOfModulesUliftFunctor`. -/
noncomputable def presheafOfModulesDeuliftFunctor :
    PresheafOfModules.{max t w} R ⥤
      PresheafOfModules.{max t w} (R ⋙ ringCatUlift.{w, t}) where
  obj M := {
    obj X := (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max t w, w} (R.obj X) ≃+* R.obj X).toRingHom).obj (M.obj X)
    map {X Y} f := by
      let eX := (ULift.ringEquiv : ULift.{max t w, w} (R.obj X) ≃+* R.obj X)
      exact (ModuleCat.restrictScalars eX.toRingHom).map (M.map f)
    map_id X := by ext x; change M.map (𝟙 X) x = x; rw [M.map_id]; rfl
    map_comp {X Y Z} f g := by
      ext x; change M.map (f ≫ g) x = M.map g (M.map f x)
      exact M.map_comp_apply f g x
  }
  map {M N} f := {
    app X := (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max t w, w} (R.obj X) ≃+* R.obj X).toRingHom).map (f.app X)
    naturality := by intro X Y g; ext x; exact PresheafOfModules.naturality_apply f g x
  }

/-- Restricting scalars up and then down again is the identity. -/
noncomputable def presheafOfModulesUliftDeuliftIso :
    presheafOfModulesUliftFunctor.{u, v, w, t} R ⋙
        presheafOfModulesDeuliftFunctor.{u, v, w, t} R ≅ 𝟭 _ := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · refine PresheafOfModules.isoMk (fun X => Iso.refl _) ?_
    intro X Y f; ext x; rfl
  · intro M N f; ext X x; rfl

/-- Restricting scalars down and then up again is the identity. -/
noncomputable def presheafOfModulesDeuliftUliftIso :
    presheafOfModulesDeuliftFunctor.{u, v, w, t} R ⋙
        presheafOfModulesUliftFunctor.{u, v, w, t} R ≅ 𝟭 _ := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · refine PresheafOfModules.isoMk (fun X => Iso.refl _) ?_
    intro X Y f; ext x; rfl
  · intro M N f; ext X x; rfl

/-- Presheaves of modules do not change when the presheaf of rings is lifted to a larger
universe: restriction of scalars along `ULift.ringEquiv` is an equivalence. The module
universe is independent of the site's and of the ring's. -/
noncomputable def presheafOfModulesUliftEquiv :
    PresheafOfModules.{max t w} (R ⋙ ringCatUlift.{w, t}) ≌
      PresheafOfModules.{max t w} R where
  functor := presheafOfModulesUliftFunctor R
  inverse := presheafOfModulesDeuliftFunctor R
  unitIso := (presheafOfModulesUliftDeuliftIso R).symm
  counitIso := presheafOfModulesDeuliftUliftIso R

end Ulift

/-- Presheaves of modules do not change when the site is replaced by its small model
`AsSmall C`, the comparison being pushforward along the two functors of `AsSmall.equiv`. The
module universe `t` and the universe `s` by which the site is made small are independent of
each other and of the site's and the ring's. -/
noncomputable def presheafOfModulesAsSmallEquiv {C : Type u} [Category.{v} C]
    (R : Cᵒᵖ ⥤ RingCat.{w}) :
    PresheafOfModules.{t} ((AsSmall.equiv.{v, u, s} (C := C)).inverse.op ⋙ R) ≌
      PresheafOfModules.{t} R where
  functor := PresheafOfModules.pushforward₀ (AsSmall.equiv.{v, u, s} (C := C)).functor _
  inverse := PresheafOfModules.pushforward₀ (AsSmall.equiv.{v, u, s} (C := C)).inverse R
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- **Stacks Project, Tag 01DV.** The category of presheaves of modules over a presheaf of
rings has functorial injective embeddings (and consequently enough injectives). -/
@[stacks 01DV, sga "3 I 3.1.2" "more general"]
theorem presheafOfModules_hasFunctorialInjectiveEmbeddings
    (C : Type u) [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{w}) :
    HasFunctorialInjectiveEmbeddings (PresheafOfModules.{max u v w} R) := by
  let R' := R ⋙ ringCatUlift.{w, max u v}
  let eSmall : PresheafOfModules.{max u v w}
        ((AsSmall.equiv.{v, u, max u v w} (C := C)).inverse.op ⋙ R') ≌
      PresheafOfModules.{max u v w} R' := presheafOfModulesAsSmallEquiv R'
  have : eSmall.functor.Additive := ⟨by intro X Y f g; ext U x; rfl⟩
  let eRing : PresheafOfModules.{max u v w} (R ⋙ ringCatUlift.{w, max u v}) ≌
      PresheafOfModules.{max u v w} R := presheafOfModulesUliftEquiv R
  have : eRing.functor.Additive := ⟨by intro X Y f g; ext U x; rfl⟩
  exact hasFunctorialInjectiveEmbeddings_of_equivalence
    eRing (hasFunctorialInjectiveEmbeddings_of_equivalence eSmall
      (presheafOfModules_hasFunctorialInjectiveEmbeddings_of_small
        ((AsSmall.equiv.{v, u, max u v w} (C := C)).inverse.op ⋙ R')))

end Stacks.Injectives
