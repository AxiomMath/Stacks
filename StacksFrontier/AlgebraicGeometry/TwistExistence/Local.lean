module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.Glue

/-!
# Local maps on the whole space, and the pullback of a local map along an open immersion

`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/Glue.lean` glues local maps and local
isomorphisms of presheaves of `𝒪`-modules over an open contained in the supremum of a family.
What a consumer gets back is a `TopCat.Sheaf.LocalModuleHom` or
`TopCat.Sheaf.LocalModuleEquiv` **on the whole space**, and this file turns such a thing into an
honest morphism, respectively isomorphism, of presheaves of modules — the last step of any
glueing argument whose output has to be a morphism rather than a family of maps on sections.

It also supplies the move in the other direction, which a *locality* argument needs: a local
isomorphism defined on an open of a scheme can be read, along an open immersion whose image lies
in that open, as a local isomorphism on the whole of the source — because the sections of a
restriction over an open of the source *are* the sections over its image.

Everything here is about a presheaf of rings on a topological space, or about an arbitrary open
immersion of schemes. No `Proj` and no graded ring appears; that is deliberate, for the reason
recorded in `StacksFrontier/AlgebraicGeometry/ChartTransNonNested/Glue.lean`.

## Main definitions

* `TopCat.Sheaf.LocalModuleHom.toHom`: **a local map on the whole space is a morphism.**
* `TopCat.Sheaf.LocalModuleEquiv.toPresheafIso`: **a local isomorphism on the whole space is an
  isomorphism** of presheaves of modules.
* `Stacks.AlgebraicGeometry.TwistExistence.isoOfLocalEquiv`: the same for sheaves of modules on a
  scheme, through the fully faithful forgetful functor.
* `Stacks.AlgebraicGeometry.TwistExistence.restrictLocalEquiv`: **the pullback of a local
  isomorphism along an open immersion.**

## Implementation notes

The naturality field of a morphism of presheaves of modules is an equation between composites in
`ModuleCat` indexed by an arbitrary morphism `h` of the opposite category of opens. Opens form a
partial order, so `h` is the unique morphism between its endpoints; it is substituted away by
`Subsingleton.elim` *before* the equation is tested on a section, since it occurs in the
restriction of scalars appearing in the type of that equation and so cannot be rewritten
underneath it.

For `restrictLocalEquiv` the scalar bookkeeping is definitional and no lemma is cited for it:
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl` and
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom` is `rfl`, so the action of `Γ(Y, V)` on
the sections of a restriction over `V` *is* the action of `Γ(X, f ''ᵁ V)` through
`(f.appIso V).inv`, and a map linear for the latter is linear for the former with no transport.
The same holds of the restriction maps, by
`AlgebraicGeometry.Scheme.Modules.restrictAppIso_inv_map`.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 04TN](https://stacks.math.columbia.edu/tag/04TN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} 𝒪}

namespace LocalModuleHom

/-- **A local map of presheaves of `𝒪`-modules on the whole space is a morphism.** The components
are the local map's own, and the naturality condition is its compatibility with the restriction
maps. -/
public def toHom (g : LocalModuleHom M N ⊤) : M ⟶ N where
  app Y := g.app Y.unop le_top
  naturality {Y Z} h := by
    have hZY : Z.unop ≤ Y.unop := leOfHom h.unop
    obtain rfl : h = (homOfLE hZY).op := Subsingleton.elim _ _
    exact ModuleCat.hom_ext (LinearMap.ext fun s => g.naturality le_top hZY s)

/-- The morphism of a local map acts on sections as the local map. -/
public theorem toHom_app (g : LocalModuleHom M N ⊤) (V : Opens X) (s : M.obj (op V)) :
    (toHom g).app (op V) s = g.app V le_top s :=
  rfl

end LocalModuleHom

namespace LocalModuleEquiv

/-- **A local isomorphism of presheaves of `𝒪`-modules on the whole space is an isomorphism.**
The two directions are the morphisms of the local map and of its inverse, and the two composites
are the identity because each component is a linear equivalence. -/
public def toPresheafIso (e : LocalModuleEquiv M N ⊤) : M ≅ N where
  hom := LocalModuleHom.toHom e.toLocalModuleHom
  inv := LocalModuleHom.toHom e.symmLocalModuleHom
  hom_inv_id :=
    PresheafOfModules.hom_ext fun Y =>
      ModuleCat.hom_ext (LinearMap.ext fun s => (e.app Y.unop le_top).symm_apply_apply s)
  inv_hom_id :=
    PresheafOfModules.hom_ext fun Y =>
      ModuleCat.hom_ext (LinearMap.ext fun t => (e.app Y.unop le_top).apply_symm_apply t)

/-- The forward direction of the isomorphism acts on sections as the local isomorphism. -/
public theorem toPresheafIso_hom_app (e : LocalModuleEquiv M N ⊤) (V : Opens X)
    (s : M.obj (op V)) : e.toPresheafIso.hom.app (op V) s = e.app V le_top s :=
  rfl

/-- Its inverse acts on sections as the inverse of the local isomorphism. -/
public theorem toPresheafIso_inv_app (e : LocalModuleEquiv M N ⊤) (V : Opens X)
    (t : N.obj (op V)) : e.toPresheafIso.inv.app (op V) t = (e.app V le_top).symm t :=
  rfl

end LocalModuleEquiv

end TopCat.Sheaf

namespace Stacks.AlgebraicGeometry.TwistExistence

variable {X Y : Scheme.{u}}

/-- **A local isomorphism on the whole space is an isomorphism of sheaves of modules on a
scheme.** The forgetful functor to presheaves of modules is fully faithful, so the isomorphism of
`TopCat.Sheaf.LocalModuleEquiv.toPresheafIso` is the image of one of sheaves. -/
public def isoOfLocalEquiv {M N : X.Modules}
    (e : TopCat.Sheaf.LocalModuleEquiv M.val N.val ⊤) : M ≅ N :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso e.toPresheafIso

/-- The isomorphism built from a local isomorphism acts on sections as the local isomorphism. -/
public theorem isoOfLocalEquiv_hom_app {M N : X.Modules}
    (e : TopCat.Sheaf.LocalModuleEquiv M.val N.val ⊤) (V : X.Opens) (s : M.val.obj (op V)) :
    (isoOfLocalEquiv e).hom.val.app (op V) s = e.app V le_top s :=
  rfl

/-- Its inverse acts on sections as the inverse of the local isomorphism. -/
public theorem isoOfLocalEquiv_inv_app {M N : X.Modules}
    (e : TopCat.Sheaf.LocalModuleEquiv M.val N.val ⊤) (V : X.Opens) (t : N.val.obj (op V)) :
    (isoOfLocalEquiv e).inv.val.app (op V) t = (e.app V le_top).symm t :=
  rfl

/-- **The pullback of a local isomorphism along an open immersion.** A local isomorphism of
sheaves of modules on `X`, defined over an open containing the image of an open immersion
`f : Y ⟶ X`, is a local isomorphism of their restrictions along `f` on the whole of `Y`: the
sections of a restriction over an open of `Y` are the sections over its image, and the scalars
match through `(f.appIso V).inv`. -/
public def restrictLocalEquiv (f : Y ⟶ X) [IsOpenImmersion f] {M N : X.Modules} {W₀ : X.Opens}
    (e : TopCat.Sheaf.LocalModuleEquiv M.val N.val W₀) (hf : f ''ᵁ (⊤ : Y.Opens) ≤ W₀) :
    TopCat.Sheaf.LocalModuleEquiv (Scheme.Modules.restrict M f).val
      (Scheme.Modules.restrict N f).val ⊤ where
  app V _ :=
    { toFun := e.app (f ''ᵁ V) ((f.image_mono le_top).trans hf)
      map_add' := map_add _
      map_smul' := fun r x =>
        (e.app (f ''ᵁ V) ((f.image_mono le_top).trans hf)).map_smul ((f.appIso V).inv r) x
      invFun := (e.app (f ''ᵁ V) ((f.image_mono le_top).trans hf)).symm
      left_inv := (e.app (f ''ᵁ V) ((f.image_mono le_top).trans hf)).left_inv
      right_inv := (e.app (f ''ᵁ V) ((f.image_mono le_top).trans hf)).right_inv }
  naturality _ hWV s := e.naturality ((f.image_mono le_top).trans hf) (f.image_mono hWV) s

/-- The pullback of a local isomorphism acts on the sections over an open of the source as the
original acts on the sections over its image. -/
public theorem restrictLocalEquiv_app (f : Y ⟶ X) [IsOpenImmersion f] {M N : X.Modules}
    {W₀ : X.Opens} (e : TopCat.Sheaf.LocalModuleEquiv M.val N.val W₀)
    (hf : f ''ᵁ (⊤ : Y.Opens) ≤ W₀) (V : Y.Opens)
    (x : (Scheme.Modules.restrict M f).val.obj (op V)) :
    (restrictLocalEquiv f e hf).app V le_top x =
      e.app (f ''ᵁ V) ((f.image_mono le_top).trans hf) x :=
  rfl

end Stacks.AlgebraicGeometry.TwistExistence

end
