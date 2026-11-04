module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence

/-!
# Sheaves of modules on slices along an equivalence of sites with invertible structure map

Let `e : C ≌ D` be an equivalence of sites, continuous in both directions, let `S` be a sheaf of
rings on `C` and `R` a sheaf of rings on `D`, and let `φ : S ⟶ e_* R` be an isomorphism of sheaves
of rings. Then for every object `W` of `C` the categories of sheaves of modules on the slices
`D/e(W)` and `C/W` are equivalent, along the equivalence of slices `C/W ≌ D/e(W)` induced by `e`.

The inverse structure map `R ⟶ (e⁻¹)_* S` is determined by `φ`: transport along the counit of the
equivalence, then invert `φ`. It satisfies the two compatibilities that
`SheafOfModules.pushforwardPushforwardEquivalence` asks for, so only `φ` and its invertibility
are needed.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.inverseStructureMapOfIso`: the inverse structure map
  `R ⟶ (e⁻¹)_* S` determined by an invertible `φ : S ⟶ e_* R`.
* `Stacks.SheafOfModules.InternalHom.siteEquivModulesOverOfIso`: the equivalence of categories of
  sheaves of modules on the slices `D/e(W)` and `C/W`.

## Main results

* `Stacks.SheafOfModules.InternalHom.whiskerRight_counit_eq_inverseStructureMapOfIso` and
  `Stacks.SheafOfModules.InternalHom.comp_inverseStructureMapOfIso_unit`: the two
  compatibilities of `φ` and `inverseStructureMapOfIso`.

## Implementation notes

The two sites have independent object and morphism universes, and the sheaves of rings are bare
sheaves rather than the structure sheaves of two ringed sites: nothing here compares an object of
one site with an object of the other, and the only universe the two sides must share is that of
the sections, which `φ` relates. This is the generality in which the small Zariski site of a
scheme, whose objects live one universe up, is compared with the site of opens of the scheme.
`Stacks.SheafOfModules.InternalHom.psiOfIso` and
`Stacks.SheafOfModules.InternalHom.siteEquivModulesOver` are the same constructions for two
ringed sites sharing their universes.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v u' v' w m

namespace Stacks.SheafOfModules.InternalHom

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (eqv : C ≌ D) [eqv.functor.IsContinuous J K] [eqv.inverse.IsContinuous K J]
  {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
  (φ : S ⟶ (eqv.functor.sheafPushforwardContinuous RingCat.{w} J K).obj R)
  [hφ : IsIso φ]

/-- **The inverse structure map determined by an invertible `φ : S ⟶ e_* R`**: transport along
the counit of the equivalence of sites, then invert `φ`. -/
def inverseStructureMapOfIso :
    R ⟶ (eqv.inverse.sheafPushforwardContinuous RingCat.{w} K J).obj S :=
  ⟨Functor.whiskerRight (NatTrans.op eqv.counit) R.obj ≫
    Functor.whiskerLeft eqv.inverse.op (inv φ.hom)⟩

/-- The first compatibility of `φ` and `inverseStructureMapOfIso`; it holds because
`inverseStructureMapOfIso` was defined by cancelling `φ` off it. -/
theorem whiskerRight_counit_eq_inverseStructureMapOfIso :
    Functor.whiskerRight (NatTrans.op eqv.counit) R.obj =
      (inverseStructureMapOfIso eqv φ).hom ≫ eqv.inverse.op.whiskerLeft φ.hom := by
  ext W x
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (IsIso.inv_hom_id φ.hom) (eqv.inverse.op.obj W))
    ((RingCat.Hom.hom (R.obj.map (eqv.counit.app W.unop).op)) x)).symm

/-- The second compatibility of `φ` and `inverseStructureMapOfIso`. Since `φ` is invertible it
suffices to check it after composing with `φ`, and naturality of `φ` turns it into the triangle
identity `e(η_W) ≫ ε_{e(W)} = 𝟙` of the equivalence of sites. -/
theorem comp_inverseStructureMapOfIso_unit :
    φ.hom ≫ eqv.functor.op.whiskerLeft (inverseStructureMapOfIso eqv φ).hom ≫
      Functor.whiskerRight (NatTrans.op eqv.unit) S.obj = 𝟙 S.obj := by
  ext W : 2
  obtain ⟨W⟩ := W
  have hn := φ.hom.naturality (eqv.unit.app W).op
  dsimp only [Functor.id_obj, Functor.op_obj, unop_op, Functor.comp_obj, Functor.op_map] at hn
  have hi : (inv φ.hom).app (op (eqv.inverse.obj (eqv.functor.obj W))) ≫
      φ.hom.app (op (eqv.inverse.obj (eqv.functor.obj W))) = 𝟙 _ :=
    (asIso φ.hom).inv_hom_id_app _
  simp only [inverseStructureMapOfIso, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.op_app, NatTrans.id_app, Category.assoc]
  rw [← cancel_mono (φ.hom.app (op W))]
  dsimp only [Functor.id_obj, Functor.op_obj, unop_op, Functor.comp_obj]
  simp only [Category.assoc, Category.id_comp]
  rw [hn, ← Category.assoc ((inv φ.hom).app _) (φ.hom.app _), hi, Category.id_comp]
  show φ.hom.app (op W) ≫ R.obj.map (eqv.counit.app (eqv.functor.obj W)).op ≫
      R.obj.map (eqv.functor.map (eqv.unit.app W)).op = φ.hom.app (op W)
  have ht : eqv.functor.map (eqv.unit.app W) ≫ eqv.counit.app (eqv.functor.obj W) = 𝟙 _ :=
    eqv.functor_unit_comp W
  rw [← Functor.map_comp, ← op_comp, ht]
  simp only [Functor.id_obj, Functor.op_obj, op_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id (φ.hom.app (op W))

/-- **Sheaves of modules on the slices agree along an equivalence of sites with an invertible
structure map.** For `W` in `C`, the categories of sheaves of modules on `D/e(W)` and on `C/W`
are equivalent along the equivalence of slices `C/W ≌ D/e(W)` induced by `e`; the two structure
maps are `φ` and `inverseStructureMapOfIso` whiskered along the slice projections. -/
def siteEquivModulesOverOfIso (W : C) :
    _root_.SheafOfModules.{m} (R.over (eqv.functor.obj W)) ≌
      _root_.SheafOfModules.{m} (S.over W) :=
  _root_.SheafOfModules.pushforwardPushforwardEquivalence (Over.postEquiv (X := W) eqv)
    (⟨Functor.whiskerLeft (Over.forget W).op φ.hom⟩ :
      (S.over W) ⟶ (((Over.postEquiv (X := W) eqv).functor).sheafPushforwardContinuous
        RingCat.{w} (J.over W) (K.over (eqv.functor.obj W))).obj (R.over (eqv.functor.obj W)))
    (⟨Functor.whiskerLeft (Over.forget (eqv.functor.obj W)).op
        (inverseStructureMapOfIso eqv φ).hom⟩ :
      (R.over (eqv.functor.obj W)) ⟶
        (((Over.postEquiv (X := W) eqv).inverse).sheafPushforwardContinuous RingCat.{w}
          (K.over (eqv.functor.obj W)) (J.over W)).obj (S.over W))
    (by
      ext T : 2
      exact congrArg (fun t => NatTrans.app t (op T.unop.left))
        (whiskerRight_counit_eq_inverseStructureMapOfIso eqv φ))
    (by
      ext T : 2
      exact congrArg (fun t => NatTrans.app t (op T.unop.left))
        (comp_inverseStructureMapOfIso_unit eqv φ))

end Stacks.SheafOfModules.InternalHom

end
