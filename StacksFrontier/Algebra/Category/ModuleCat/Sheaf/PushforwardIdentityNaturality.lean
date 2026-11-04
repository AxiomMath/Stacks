module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules

/-!
# Morphisms of the restriction of sheaves of modules to a dense subsite

Let `v : C ⥤ C'` exhibit `(C, J)` as a dense subsite of `(C', K)` and let `R` be a sheaf of rings
on `(C', K)`.  Restriction of sections along `v` carries a sheaf of `R`-modules to a sheaf of
modules over the restricted sheaf of rings, `Stacks.DenseSubsiteModules.moduleRestriction`, with
no change of scalars.  A family of linear maps on the sections of two sheaves of `R`-modules over
the objects in the image of `v` whose naturality squares for the restriction maps of those two
sheaves commute is therefore a morphism of their restrictions.

## Main results

* `PresheafOfModules.naturality_of_apply`: a naturality square of two linear maps between the
  sections of two presheaves of modules over two objects commutes as soon as it commutes on
  sections.
* `Stacks.DenseSubsiteModules.moduleRestriction_naturality`: a naturality square of such a family
  for the restriction maps of the two sheaves is the naturality square of the induced family on
  the restrictions.
* `Stacks.DenseSubsiteModules.moduleRestrictionHom`: the morphism of the restrictions such a
  family defines, with `Stacks.DenseSubsiteModules.moduleRestrictionHom_val_app` reading it on
  sections.
* `Stacks.DenseSubsiteModules.full_moduleRestriction`: restriction of sheaves of modules to a
  dense subsite is full.

## Implementation notes

The sections of the restriction of a sheaf of modules over an object `X` of `C` are the sections
of the sheaf over `v.obj X`, as a module over one and the same ring, and the restriction maps of
the two agree; both identifications hold definitionally but not syntactically.  The functor, the
two sheaves, the two objects and the morphism between them are variables in both statements
below, so that each identification is performed once here rather than at the objects a consumer
has.  Both are asked for in the position of a morphism of modules, never between two sections:
the data and the hypothesis of these results are the family itself and its naturality squares,
not the values of the family on sections.

`Stacks.DenseSubsiteModules.full_moduleRestriction` names the fullness of the restriction, which
is already available as an instance.  At a concrete functor `v` typeclass resolution does not
reach that instance, because `Stacks.DenseSubsiteModules.moduleRestriction` is a reducible
abbreviation and what resolution sees is the shape of `CategoryTheory.SheafOfModules.pushforward`
at a reduced structure morphism; naming it keeps a consumer from having to reconstruct it.

## References

* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace PresheafOfModules

universe w w' uu vv

variable {C : Type uu} [Category.{vv} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- Commutation of the naturality square of two linear maps between the sections of two
presheaves of modules over two objects, from its elementwise form on sections.

This is the converse of `PresheafOfModules.naturality_apply`, and it is what builds a morphism of
presheaves of modules out of a family of linear maps natural on sections.  The two presheaves,
the two objects and the morphism between them are variables, so that the identification of a
section of a presheaf of modules with a section of its restriction of scalars is performed here
rather than at every use. -/
theorem naturality_of_apply (M₁ M₂ : PresheafOfModules.{w'} R) {Z Z' : Cᵒᵖ} (g : Z ⟶ Z')
    (app : M₁.obj Z ⟶ M₂.obj Z) (app' : M₁.obj Z' ⟶ M₂.obj Z')
    (h : ∀ m : M₁.obj Z, app' (M₁.map g m) = M₂.map g (app m)) :
    M₁.map g ≫ (ModuleCat.restrictScalars (R.map g).hom).map app' = app ≫ M₂.map g :=
  ModuleCat.hom_ext (LinearMap.ext h)

end PresheafOfModules

universe w u₁ v₁ u₂ v₂

namespace Stacks.DenseSubsiteModules

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K] (R : Sheaf K RingCat.{w})
  (M N : SheafOfModules.{w} R)

/-- A naturality square of a family of linear maps on the sections of two sheaves of `R`-modules
over the objects in the image of `v`, read as a naturality square of the induced family on the
sections of the restrictions of those sheaves to the dense subsite. -/
theorem moduleRestriction_naturality
    (app : ∀ Z : Cᵒᵖ, M.val.obj (v.op.obj Z) ⟶ N.val.obj (v.op.obj Z))
    {Z Z' : Cᵒᵖ} (g : Z ⟶ Z')
    (h : M.val.map (v.op.map g) ≫
        (ModuleCat.restrictScalars (R.obj.map (v.op.map g)).hom).map (app Z') =
      app Z ≫ N.val.map (v.op.map g)) :
    ((moduleRestriction J K v R).obj M).val.map g ≫
        (ModuleCat.restrictScalars ((ringRestriction J K v R).obj.map g).hom).map (app Z') =
      app Z ≫ ((moduleRestriction J K v R).obj N).val.map g :=
  h

/-- A family of linear maps on the sections of two sheaves of `R`-modules over the objects in the
image of `v`, natural for the restriction maps of those sheaves, as a morphism of their
restrictions to the dense subsite. -/
def moduleRestrictionHom
    (app : ∀ Z : Cᵒᵖ, M.val.obj (v.op.obj Z) ⟶ N.val.obj (v.op.obj Z))
    (h : ∀ (Z Z' : Cᵒᵖ) (g : Z ⟶ Z'), M.val.map (v.op.map g) ≫
        (ModuleCat.restrictScalars (R.obj.map (v.op.map g)).hom).map (app Z') =
      app Z ≫ N.val.map (v.op.map g)) :
    (moduleRestriction J K v R).obj M ⟶ (moduleRestriction J K v R).obj N :=
  ⟨{ app := app
     naturality := fun {Z Z'} g =>
       moduleRestriction_naturality J K v R M N app g (h Z Z' g) }⟩

/-- The morphism of the restrictions defined by a natural family of linear maps is, on sections
over an object of the subsite, the member of the family at that object. -/
theorem moduleRestrictionHom_val_app
    (app : ∀ Z : Cᵒᵖ, M.val.obj (v.op.obj Z) ⟶ N.val.obj (v.op.obj Z))
    (h : ∀ (Z Z' : Cᵒᵖ) (g : Z ⟶ Z'), M.val.map (v.op.map g) ≫
        (ModuleCat.restrictScalars (R.obj.map (v.op.map g)).hom).map (app Z') =
      app Z ≫ N.val.map (v.op.map g))
    (Z : Cᵒᵖ) :
    (moduleRestrictionHom J K v R M N app h).val.app Z = app Z :=
  rfl

/-- Restriction of sheaves of modules to a dense subsite is full, by the Comparison Lemma for
sheaves of modules. -/
theorem full_moduleRestriction : (moduleRestriction J K v R).Full :=
  inferInstance

end Stacks.DenseSubsiteModules

end
