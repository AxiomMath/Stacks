module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import StacksFrontier.AlgebraicGeometry.Descent.BigSiteEquivalence.AssociatedPresheaf
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfStructureSheaf

/-!
# The pullback-sections presheaf as a presheaf of modules

The presheaf of Stacks 03DS sends a scheme `T ⟶ S` to the global sections of the pullback of a
quasi-coherent module `F`, and it is a presheaf of abelian groups.  Those sections are a module
over the global functions `Γ(T, 𝒪_T)`, and the restriction maps are semilinear over the
restriction maps of global functions, so the presheaf of Stacks 03DS is a presheaf of modules
over the presheaf of rings of global functions — the structure presheaf of any site of
`S`-schemes.

This is the module structure that Stacks Definition 03DU (3) presupposes when it calls
`T ↦ Γ(T, f⁺ F)` a sheaf of `𝒪`-modules.

## Main definitions

* `AlgebraicGeometry.quasiCoherentSectionsPresheaf`: the presheaf of abelian groups of Stacks
  03DS, restricted along a functor from a site of `S`-schemes.
* `AlgebraicGeometry.quasiCoherentSectionsModule`: its value at an object is a module over the
  global functions of that object.
* `AlgebraicGeometry.quasiCoherentSectionsPresheafOfModules`: the resulting presheaf of modules
  over the structure presheaf.
* `AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules`: the same presheaf of modules over
  the structure sheaf of the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.quasiCoherentSectionsPresheaf_map_smul`: the restriction maps of the
  restricted presheaf are semilinear over the restriction maps of global functions.

## Implementation notes

The scalar action is transported along the prescribed isomorphisms
`AlgebraicGeometry.PullbackSectionsPresheaf.objIso`, because the presheaf of Stacks 03DS records
its values only up to those isomorphisms; the module structure is therefore not available by
unfolding the functor and has to be moved across an `AddEquiv`.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The presheaf of abelian groups of Stacks 03DS, restricted along a functor from a site of
`S`-schemes. -/
noncomputable abbrev quasiCoherentSectionsPresheaf (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  toOver.op ⋙ quasiCoherentPresheafFunctor S F

/-- The sections of the presheaf of Stacks 03DS over an object of a site of `S`-schemes are a
module over the global functions of that object, by transport along the prescribed isomorphism
with the global sections of a pullback. -/
@[instance_reducible]
noncomputable def quasiCoherentSectionsModule (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) (X : Cᵒᵖ) :
    Module ((Stacks.Sites.structurePresheaf S toOver).obj X)
      ((quasiCoherentSectionsPresheaf S F toOver).obj X) := by
  change Module Γ((toOver.op.obj X).unop.left, ⊤)
    ((quasiCoherentPresheaf S F).functor.obj (toOver.op.obj X))
  exact ((quasiCoherentPresheaf S F).objIso
    (toOver.op.obj X)).addCommGroupIsoToAddEquiv.module _

/-- **The restriction maps of the presheaf of Stacks 03DS are semilinear.**  A restriction map of
the presheaf of pullback sections carries the action of a global function to the action of its
restriction. -/
theorem quasiCoherentSectionsPresheaf_map_smul (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (r : (Stacks.Sites.structurePresheaf S toOver).obj X)
    (m : (quasiCoherentSectionsPresheaf S F toOver).obj X) :
    letI := quasiCoherentSectionsModule S F toOver X
    letI := quasiCoherentSectionsModule S F toOver Y
    (quasiCoherentSectionsPresheaf S F toOver).map f (r • m) =
      (Stacks.Sites.structurePresheaf S toOver).map f r •
        (quasiCoherentSectionsPresheaf S F toOver).map f m := by
  let := quasiCoherentSectionsModule S F toOver X
  let := quasiCoherentSectionsModule S F toOver Y
  change (quasiCoherentSectionsPresheaf S F toOver).map f (r • m) = _
  let Q := quasiCoherentPresheaf S F
  let TX := toOver.op.obj X
  let TY := toOver.op.obj Y
  let g := toOver.op.map f
  let rX : Γ((toOver.obj X.unop).left, ⊤) := r
  let eX := (Q.objIso TX).addCommGroupIsoToAddEquiv
  let RX := Γ((toOver.obj X.unop).left, ⊤)
  let : Module RX ((quasiCoherentSectionsPresheaf S F toOver).obj X) := eX.module RX
  let eY := (Q.objIso TY).addCommGroupIsoToAddEquiv
  let RY := Γ(TY.unop.left, ⊤)
  let : Module RY (Q.functor.obj TY) := eY.module RY
  let : Module ((Stacks.Sites.structurePresheaf S toOver).obj Y) (Q.functor.obj TY) := by
    change Module ((Stacks.Sites.structurePresheaf S toOver).obj Y)
      ((quasiCoherentSectionsPresheaf S F toOver).obj Y)
    exact quasiCoherentSectionsModule S F toOver Y
  let : Module ((Stacks.Sites.structurePresheaf S toOver).obj Y)
      (Γ((Scheme.Modules.pullback TY.unop.hom).obj F, ⊤)) := by
    change Module RY _
    infer_instance
  have hmap (z : Q.functor.obj TX) :
      (Q.objIso TY).hom (Q.functor.map g z) =
        pullbackSectionsMap F g.unop ((Q.objIso TX).hom z) := by
    have hcomp : Q.functor.map g ≫ (Q.objIso TY).hom =
        (Q.objIso TX).hom ≫ pullbackSectionsMap F g.unop := by
      calc
        Q.functor.map g ≫ (Q.objIso TY).hom =
            (𝟙 _) ≫ Q.functor.map g ≫ (Q.objIso TY).hom := by simp
        _ = ((Q.objIso TX).hom ≫ (Q.objIso TX).inv) ≫
            Q.functor.map g ≫ (Q.objIso TY).hom := by simp
        _ = (Q.objIso TX).hom ≫
            ((Q.objIso TX).inv ≫ Q.functor.map g ≫ (Q.objIso TY).hom) := by
          simp
        _ = (Q.objIso TX).hom ≫ pullbackSectionsMap F g.unop :=
          congrArg (fun k => (Q.objIso TX).hom ≫ k) (Q.map_objIso g)
    simpa only [AddCommGrpCat.comp_apply] using congrArg (fun k => k z) hcomp
  have hscalarX : (Q.objIso TX).hom (r • m) = rX • (Q.objIso TX).hom m := by
    change eX (rX • m) = rX • eX m
    exact (eX.linearEquiv RX).map_smul rX m
  apply (Q.objIso TY).addCommGroupIsoToAddEquiv.injective
  calc
    (Q.objIso TY).hom (Q.functor.map g (r • m)) =
        pullbackSectionsMap F g.unop ((Q.objIso TX).hom (r • m)) := hmap _
    _ = pullbackSectionsMap F g.unop (rX • (Q.objIso TX).hom m) := by
      rw [hscalarX]
    _ = g.unop.left.appTop r • pullbackSectionsMap F g.unop ((Q.objIso TX).hom m) :=
      pullbackSectionsMap_smul F g.unop rX _
    _ = (Stacks.Sites.structurePresheaf S toOver).map f r •
        (Q.objIso TY).hom (Q.functor.map g m) := by
      rw [← hmap m]
      rfl
    _ = (Q.objIso TY).hom
        ((Stacks.Sites.structurePresheaf S toOver).map f r • Q.functor.map g m) := by
      symm
      let rY : RY := g.unop.left.appTop r
      change (Q.objIso TY).hom (rY • Q.functor.map g m) = _
      exact (eY.linearEquiv RY).map_smul rY (Q.functor.map g m)

/-- **The pullback-sections presheaf as a presheaf of modules.**  For a quasi-coherent module
`F` on `S` and a site of `S`-schemes, the presheaf `T ↦ Γ(T, T.hom⁺ F)` is a presheaf of modules
over the presheaf of rings `T ↦ Γ(T, 𝒪_T)`. -/
noncomputable def quasiCoherentSectionsPresheafOfModules (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) :
    PresheafOfModules.{u} (Stacks.Sites.structurePresheaf S toOver) :=
  letI : ∀ X, Module ((Stacks.Sites.structurePresheaf S toOver).obj X)
      ((quasiCoherentSectionsPresheaf S F toOver).obj X) :=
    fun X => quasiCoherentSectionsModule S F toOver X
  PresheafOfModules.ofPresheaf (quasiCoherentSectionsPresheaf S F toOver)
    (by intro _ _ f r m; exact quasiCoherentSectionsPresheaf_map_smul S F toOver f r m)

/-- The presheaf of abelian groups underlying
`AlgebraicGeometry.quasiCoherentSectionsPresheafOfModules` is the presheaf of Stacks 03DS. -/
@[simp]
theorem quasiCoherentSectionsPresheafOfModules_presheaf (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) :
    (quasiCoherentSectionsPresheafOfModules S F toOver).presheaf =
      quasiCoherentSectionsPresheaf S F toOver :=
  rfl

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The pullback-sections presheaf of modules on the big fppf site.**  For a quasi-coherent
module `F` on `S`, the presheaf on the big fppf category of `S`-schemes sending `T ⟶ S` to
`Γ(T, T.hom⁺ F)` is a presheaf of modules over the structure sheaf of that site. -/
noncomputable def sectionsPresheafOfModules (F : S.Modules) [F.IsQuasicoherent] :
    PresheafOfModules.{u} (structureSheaf B S hS).obj :=
  quasiCoherentSectionsPresheafOfModules S F (Over.post (X := B.obj hS) B.inclusion)

/-- The presheaf of abelian groups underlying
`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules` is the presheaf of Stacks 03DS,
restricted to the big fppf site. -/
@[simp]
theorem sectionsPresheafOfModules_presheaf (F : S.Modules) [F.IsQuasicoherent] :
    (sectionsPresheafOfModules B S hS F).presheaf =
      (Over.post (X := B.obj hS) B.inclusion).op ⋙ quasiCoherentPresheafFunctor S F :=
  rfl

end BigFppfOver

end AlgebraicGeometry

end
