module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence

/-!
# Slices and structure maps along an equivalence of ringed sites of different sizes

Let `X` and `Y` be ringed sites whose rings take values in the same universe `w` but whose
underlying categories live in independent universes, and let `e : Y.C ≌ X.C` be an equivalence
continuous in both directions, with a structure map `φ : O_Y ⟶ e_* O_X`. This file states, at
these independent universes, the slice-level constructions of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InternalHomSiteEquivalence.lean` (where both sites
live in the same universes): the localized structure maps, the equivalence of module categories
on the slices `Y/W ≌ X/e(W)`, and the inverse structure map `psiOfIso` of an invertible `φ` with
its two compatibilities. They are stated in the namespace
`Stacks.SheafOfModules.InternalHom.AnyUniverse`.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.AnyUniverse.siteEquivPhiOver`,
  `Stacks.SheafOfModules.InternalHom.AnyUniverse.siteEquivPsiOver`: the structure maps localized
  at an object `W`.
* `Stacks.SheafOfModules.InternalHom.AnyUniverse.siteEquivModulesOver`: the equivalence of
  sheaves of modules on the slices.
* `Stacks.SheafOfModules.InternalHom.AnyUniverse.psiOfIso`: the inverse structure map, with
  `psiOfIso_counit` and `psiOfIso_unit`.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.PresheafOfModules.InternalHom

universe u v w m u' v'

namespace Stacks.SheafOfModules.InternalHom.AnyUniverse

section SliceEquivalence

variable {X : RingedSite.{u, v, w}} {Y : RingedSite.{u', v', w}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- The structure map `O_C ⟶ e_* O_D` of the equivalence, localized at an object `W` of `C`: it
is `φ` whiskered along the slice projection, which is possible because restricting along the
slice functor `C/W ⥤ D/e(W)` and then along `Over.forget` is restricting along
`Over.forget` and then along `e`. -/
def siteEquivPhiOver {X : RingedSite.{u, v, w}} {Y : RingedSite.{u', v', w}} (eqv : Y.C ≌ X.C)
    [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
    (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (W : Y.C) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) ⟶
      (((Over.postEquiv (X := W) eqv).functor).sheafPushforwardContinuous RingCat.{w}
        (Y.J.over W) (X.J.over (eqv.functor.obj W))).obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) :=
  ⟨Functor.whiskerLeft (Over.forget W).op φ.hom⟩

/-- The structure map `O_D ⟶ (e^{-1})_* O_C` of the equivalence, localized at `W`. -/
def siteEquivPsiOver {X : RingedSite.{u, v, w}} {Y : RingedSite.{u', v', w}} (eqv : Y.C ≌ X.C)
    [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
    (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (W : Y.C) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) ⟶
      (((Over.postEquiv (X := W) eqv).inverse).sheafPushforwardContinuous RingCat.{w}
        (X.J.over (eqv.functor.obj W)) (Y.J.over W)).obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  ⟨Functor.whiskerLeft (Over.forget (eqv.functor.obj W)).op ψ.hom⟩

variable
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

/-- Sheaves of modules on the localization `D/e(W)` and on the localization `C/W` agree, along
the equivalence of slices `C/W ≌ D/e(W)` induced by `e`. The two structure maps are `φ` and `ψ`
whiskered along the slice projections, and the two compatibilities they must satisfy are those
of `φ` and `ψ`, read at the underlying object of a slice object. -/
def siteEquivModulesOver (W : Y.C) :
    _root_.SheafOfModules.{m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) ≌
      _root_.SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  _root_.SheafOfModules.pushforwardPushforwardEquivalence (Over.postEquiv (X := W) eqv)
    (siteEquivPhiOver eqv φ W) (siteEquivPsiOver eqv ψ W)
    (by
      ext T : 2
      exact congrArg (fun t => NatTrans.app t (op T.unop.left)) H₁)
    (by
      ext T : 2
      exact congrArg (fun t => NatTrans.app t (op T.unop.left)) H₂)

end SliceEquivalence

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous


section PsiOfIso

variable {X : RingedSite.{u, v, w}} {Y : RingedSite.{u', v', w}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [hφ : IsIso φ]

/-- An invertible structure map of sheaves of rings is invertible on underlying presheaves:
sheaves of rings are a full subcategory of presheaves of rings. -/
instance isIso_hom_of_isIso : IsIso φ.hom :=
  inferInstanceAs (IsIso ((sheafToPresheaf Y.J RingCat.{w}).map φ))

/-- The inverse structure map determined by an invertible `φ`: transport along the counit of the
equivalence of sites, then invert `φ`. -/
def psiOfIso {X : RingedSite.{u, v, w}} {Y : RingedSite.{u', v', w}} (eqv : Y.C ≌ X.C)
    [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
    (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [hφ : IsIso φ] : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  ⟨Functor.whiskerRight (NatTrans.op eqv.counit) (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ≫
    Functor.whiskerLeft eqv.inverse.op (inv φ.hom)⟩

/-- The first compatibility, for the inverse structure map built from an invertible `φ`: it
holds because `psiOfIso` was defined by cancelling `φ` off it. -/
theorem psiOfIso_counit {X : RingedSite.{u, v, w}} {Y : RingedSite.{u', v', w}} (eqv : Y.C ≌ X.C)
    [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
    (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [hφ : IsIso φ] :
    Functor.whiskerRight (NatTrans.op eqv.counit) (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
      (psiOfIso eqv φ).hom ≫ eqv.inverse.op.whiskerLeft φ.hom := by
  ext W x
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (IsIso.inv_hom_id φ.hom) (eqv.inverse.op.obj W))
    ((RingCat.Hom.hom ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map
      (eqv.counit.app W.unop).op)) x)).symm

/-- The second compatibility, for the inverse structure map built from an invertible `φ`. Since
`φ` is invertible it suffices to check the identity after composing with `φ` again, and then
naturality of `φ` turns the statement into the triangle identity
`e(η_W) ≫ ε_{e(W)} = 𝟙` of the equivalence of sites. -/
theorem psiOfIso_unit {X : RingedSite.{u, v, w}} {Y : RingedSite.{u', v', w}} (eqv : Y.C ≌ X.C)
    [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
    (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [hφ : IsIso φ] :
    φ.hom ≫ eqv.functor.op.whiskerLeft (psiOfIso eqv φ).hom ≫
      Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
        𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj := by
  ext W : 2
  obtain ⟨W⟩ := W
  have hn := φ.hom.naturality (eqv.unit.app W).op
  dsimp only [Functor.id_obj, Functor.op_obj, unop_op, Functor.comp_obj, Functor.op_map] at hn
  have hi : (inv φ.hom).app (op (eqv.inverse.obj (eqv.functor.obj W))) ≫
      φ.hom.app (op (eqv.inverse.obj (eqv.functor.obj W))) = 𝟙 _ :=
    (asIso φ.hom).inv_hom_id_app _
  simp only [psiOfIso, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.op_app, NatTrans.id_app, Category.assoc]
  rw [← cancel_mono (φ.hom.app (op W))]
  dsimp only [Functor.id_obj, Functor.op_obj, unop_op, Functor.comp_obj]
  simp only [Category.assoc, Category.id_comp]
  rw [hn, ← Category.assoc ((inv φ.hom).app _) (φ.hom.app _), hi, Category.id_comp]
  change φ.hom.app (op W) ≫
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (eqv.counit.app (eqv.functor.obj W)).op ≫
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (eqv.functor.map (eqv.unit.app W)).op =
    φ.hom.app (op W)
  have ht : eqv.functor.map (eqv.unit.app W) ≫ eqv.counit.app (eqv.functor.obj W) = 𝟙 _ :=
    eqv.functor_unit_comp W
  rw [← Functor.map_comp, ← op_comp, ht]
  simp only [Functor.id_obj, Functor.op_obj, op_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id (φ.hom.app (op W))

end PsiOfIso

end Stacks.SheafOfModules.InternalHom.AnyUniverse

end
