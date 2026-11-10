module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentSectionsModule

/-!
# The pullback-sections presheaf of an arbitrary module, as a presheaf of modules

For a module `F` on a scheme `S` and a site `C` of `S`-schemes, the presheaf
`(f : T → S) ↦ Γ(T, f^*F)` of Stacks 03DS restricted to `C` is a presheaf of modules over the
structure presheaf `T ↦ Γ(T, 𝒪_T)` of `C`.  Nothing about this needs `F` to be quasi-coherent:
the presheaf, its values and its restriction maps are defined for every `𝒪_S`-module, and the
restriction maps are semilinear because pulling a section back along a morphism of schemes is.
This is the presheaf whose sheafification Stacks 070S (1) and (2) compute, for an arbitrary
sheaf of `𝒪_S`-modules.

## Main definitions

* `AlgebraicGeometry.sitePullbackSectionsPresheaf`: the presheaf of abelian groups
  `T ↦ Γ(T, T.hom^* F)` on a site of `S`-schemes.
* `AlgebraicGeometry.sitePullbackSectionsModule`: its value at an object is a module over the
  global functions of that object.
* `AlgebraicGeometry.sitePullbackSectionsPresheafOfModules`: the resulting presheaf of modules
  over the structure presheaf.
* `AlgebraicGeometry.BigFppfOver.pullbackSectionsPresheaf`: the same presheaf of modules over
  the structure sheaf of the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.sitePullbackSectionsPresheaf_map_smul`: the restriction maps are
  semilinear over the restriction maps of global functions.
* `AlgebraicGeometry.quasiCoherentSectionsPresheafOfModules_eq` and
  `AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules_eq_pullbackSectionsPresheaf`: for a
  quasi-coherent `F` these are the presheaves of modules
  `AlgebraicGeometry.quasiCoherentSectionsPresheafOfModules` and
  `AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules`, by definition.

## Implementation notes

The construction is that of `AlgebraicGeometry.quasiCoherentSectionsPresheafOfModules`, made on
`AlgebraicGeometry.quasiCoherentPresheafConstruction`, the presheaf of Stacks 03DS for an
arbitrary module, instead of on its quasi-coherent name `AlgebraicGeometry.quasiCoherentPresheaf`.
The two agree definitionally, which is what makes the quasi-coherent statements special cases of
the ones built on this presheaf.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The presheaf of abelian groups of Stacks 03DS, restricted along a functor from a site of
`S`-schemes. -/
noncomputable abbrev sitePullbackSectionsPresheaf (S : Scheme.{u}) (F : S.Modules)
    {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  toOver.op ⋙ (quasiCoherentPresheafConstruction S F).functor

/-- The sections of the presheaf of Stacks 03DS over an object of a site of `S`-schemes are a
module over the global functions of that object, by transport along the prescribed isomorphism
with the global sections of a pullback. -/
@[instance_reducible]
noncomputable def sitePullbackSectionsModule (S : Scheme.{u}) (F : S.Modules)
    {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) (X : Cᵒᵖ) :
    Module ((Stacks.Sites.structurePresheaf S toOver).obj X)
      ((sitePullbackSectionsPresheaf S F toOver).obj X) := by
  change Module Γ((toOver.op.obj X).unop.left, ⊤)
    ((quasiCoherentPresheafConstruction S F).functor.obj (toOver.op.obj X))
  exact ((quasiCoherentPresheafConstruction S F).objIso
    (toOver.op.obj X)).addCommGroupIsoToAddEquiv.module _

/-- **The restriction maps of the presheaf of Stacks 03DS are semilinear.**  A restriction map of
the presheaf of pullback sections carries the action of a global function to the action of its
restriction. -/
theorem sitePullbackSectionsPresheaf_map_smul (S : Scheme.{u}) (F : S.Modules)
    {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (r : (Stacks.Sites.structurePresheaf S toOver).obj X)
    (m : (sitePullbackSectionsPresheaf S F toOver).obj X) :
    letI := sitePullbackSectionsModule S F toOver X
    letI := sitePullbackSectionsModule S F toOver Y
    (sitePullbackSectionsPresheaf S F toOver).map f (r • m) =
      (Stacks.Sites.structurePresheaf S toOver).map f r •
        (sitePullbackSectionsPresheaf S F toOver).map f m := by
  let := sitePullbackSectionsModule S F toOver X
  let := sitePullbackSectionsModule S F toOver Y
  change (sitePullbackSectionsPresheaf S F toOver).map f (r • m) = _
  let Q := quasiCoherentPresheafConstruction S F
  let TX := toOver.op.obj X
  let TY := toOver.op.obj Y
  let g := toOver.op.map f
  have hscalar (T : (Over S)ᵒᵖ) (r : Γ(T.unop.left, ⊤)) (m : Q.functor.obj T) :
      letI := (Q.objIso T).addCommGroupIsoToAddEquiv.module Γ(T.unop.left, ⊤)
      (Q.objIso T).hom (r • m) = r • (Q.objIso T).hom m :=
    ((Q.objIso T).addCommGroupIsoToAddEquiv.linearEquiv _).map_smul r m
  let rX : Γ((toOver.obj X.unop).left, ⊤) := r
  let : Module ((Stacks.Sites.structurePresheaf S toOver).obj Y) (Q.functor.obj TY) := by
    change Module ((Stacks.Sites.structurePresheaf S toOver).obj Y)
      ((sitePullbackSectionsPresheaf S F toOver).obj Y)
    exact sitePullbackSectionsModule S F toOver Y
  let : Module ((Stacks.Sites.structurePresheaf S toOver).obj Y)
      (Γ((Scheme.Modules.pullback TY.unop.hom).obj F, ⊤)) := by
    change Module Γ(TY.unop.left, ⊤) _
    infer_instance
  have hmap (z : Q.functor.obj TX) :
      (Q.objIso TY).hom (Q.functor.map g z) =
        pullbackSectionsMap F g.unop ((Q.objIso TX).hom z) := by
    have hcomp : Q.functor.map g ≫ (Q.objIso TY).hom =
        (Q.objIso TX).hom ≫ pullbackSectionsMap F g.unop := by
      rw [← Q.map_objIso g, Iso.hom_inv_id_assoc]
    simpa only [AddCommGrpCat.comp_apply] using congrArg (fun k => k z) hcomp
  apply (Q.objIso TY).addCommGroupIsoToAddEquiv.injective
  calc
    (Q.objIso TY).hom (Q.functor.map g (r • m)) =
        pullbackSectionsMap F g.unop ((Q.objIso TX).hom (r • m)) := hmap _
    _ = pullbackSectionsMap F g.unop (rX • (Q.objIso TX).hom m) :=
      congrArg _ (hscalar TX rX m)
    _ = g.unop.left.appTop r • pullbackSectionsMap F g.unop ((Q.objIso TX).hom m) :=
      pullbackSectionsMap_smul F g.unop rX _
    _ = (Stacks.Sites.structurePresheaf S toOver).map f r •
        (Q.objIso TY).hom (Q.functor.map g m) := by
      rw [← hmap m]
      rfl
    _ = (Q.objIso TY).hom
        ((Stacks.Sites.structurePresheaf S toOver).map f r • Q.functor.map g m) :=
      (hscalar TY (g.unop.left.appTop r) _).symm

/-- **The pullback-sections presheaf as a presheaf of modules.**  For a module
`F` on `S` and a site of `S`-schemes, the presheaf `T ↦ Γ(T, T.hom⁺ F)` is a presheaf of modules
over the presheaf of rings `T ↦ Γ(T, 𝒪_T)`. -/
noncomputable def sitePullbackSectionsPresheafOfModules (S : Scheme.{u}) (F : S.Modules)
    {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) :
    PresheafOfModules.{u} (Stacks.Sites.structurePresheaf S toOver) :=
  letI : ∀ X, Module ((Stacks.Sites.structurePresheaf S toOver).obj X)
      ((sitePullbackSectionsPresheaf S F toOver).obj X) :=
    fun X => sitePullbackSectionsModule S F toOver X
  PresheafOfModules.ofPresheaf (sitePullbackSectionsPresheaf S F toOver)
    (fun _ _ f r m => sitePullbackSectionsPresheaf_map_smul S F toOver f r m)

/-- The presheaf of abelian groups underlying
`AlgebraicGeometry.sitePullbackSectionsPresheafOfModules` is the presheaf of Stacks 03DS. -/
@[simp]
theorem sitePullbackSectionsPresheafOfModules_presheaf (S : Scheme.{u}) (F : S.Modules)
    {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) :
    (sitePullbackSectionsPresheafOfModules S F toOver).presheaf =
      sitePullbackSectionsPresheaf S F toOver :=
  rfl

/-- For a quasi-coherent `F`, `AlgebraicGeometry.sitePullbackSectionsPresheafOfModules` is the
presheaf of modules `AlgebraicGeometry.quasiCoherentSectionsPresheafOfModules`. -/
theorem quasiCoherentSectionsPresheafOfModules_eq (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) :
    quasiCoherentSectionsPresheafOfModules S F toOver =
      sitePullbackSectionsPresheafOfModules S F toOver :=
  rfl

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The pullback-sections presheaf of modules on the big fppf site, for an arbitrary
module.**  For a module `F` on `S`, the presheaf on the big fppf category of `S`-schemes sending
`T ⟶ S` to `Γ(T, T.hom^* F)` is a presheaf of modules over the structure sheaf of that site. -/
noncomputable def pullbackSectionsPresheaf (F : S.Modules) :
    PresheafOfModules.{u} (structureSheaf B S hS).obj :=
  sitePullbackSectionsPresheafOfModules S F (Over.post (X := B.obj hS) B.inclusion)

/-- For a quasi-coherent `F`, `AlgebraicGeometry.BigFppfOver.pullbackSectionsPresheaf` is
`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules`. -/
theorem sectionsPresheafOfModules_eq_pullbackSectionsPresheaf (F : S.Modules)
    [F.IsQuasicoherent] :
    sectionsPresheafOfModules B S hS F = pullbackSectionsPresheaf B S hS F :=
  rfl

end BigFppfOver

end AlgebraicGeometry

end
