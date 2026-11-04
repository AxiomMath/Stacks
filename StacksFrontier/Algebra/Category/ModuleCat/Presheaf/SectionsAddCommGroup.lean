module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# The abelian group of global sections of a presheaf of modules

`PresheafOfModules.sections`, the global sections of a presheaf of modules, is defined in
Mathlib as the sections of the underlying presheaf of *sets*, so it carries no algebraic
structure at all: `s + t` is not a term, even though every `M.obj X` is an abelian group and
every restriction map `M.map f` is additive.  This file supplies the missing structure — the
global sections of a presheaf of modules are an abelian group under pointwise addition —
together with the three computation rules (the value over an object of a sum, of zero and of a
negative) and the additivity of the map on sections induced by a morphism of presheaves of
modules.

Nothing here is specific to a sheaf: `SheafOfModules.sections` is by definition the sections of
the underlying presheaf of modules, so the instance applies to it as well.

## Main definitions

* `PresheafOfModules.sectionsAddSubgroup`: the global sections as an additive subgroup of the
  product of the modules of sections over the objects of the site.
* `PresheafOfModules.sectionsAddCommGroup`: the resulting abelian group structure on the global
  sections of a presheaf of modules.

## Main results

* `PresheafOfModules.sections_eval_add`, `PresheafOfModules.sections_eval_zero` and
  `PresheafOfModules.sections_eval_neg`: the value over an object of a sum, of zero and of a
  negative.  All three hold by definition.
* `PresheafOfModules.sections_eval_add_of_map` and
  `PresheafOfModules.sections_restrictₛₗ_eval_add`: an additivity relation between the values of
  three sections over an object passes to the objects above it, and is witnessed by the
  restriction maps into it.  Together they are what makes additivity of a map of global sections
  a local condition on the site.
* `PresheafOfModules.sectionsMap_add`: the map on sections induced by a morphism of presheaves
  of modules is additive, and `PresheafOfModules.sectionsAddMonoidHom` is that map bundled.

## Implementation notes

The group structure is the one `PresheafOfModules.sectionsAddSubgroup` carries as a subgroup of
a product, rather than a structure written out field by field on the subtype: the carrier of
that subgroup is the type of sections on the nose, so the two types are the same and the three
computation rules are `rfl` — which they are not for a hand-written structure, whose `nsmul` and
`zsmul` fields the kernel then cannot see through.

Additivity of the restriction maps is taken from `PresheafOfModules.restrictₛₗ`, the bundled
semilinear form of `PresheafOfModules.map`: the restriction map itself is a morphism of
`ModuleCat` into a restriction of scalars, so `map_add` applied to it lands at the abelian group
structure of that restriction of scalars and not at the one of `M.obj Y`.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- **The global sections of a presheaf of modules, as an additive subgroup** of the product of
its modules of sections: a family of sections compatible with the restriction maps.  The carrier
is `PresheafOfModules.sections` itself, so this *is* that type with its pointwise group
structure. -/
def sectionsAddSubgroup (M : PresheafOfModules.{v} R) :
    AddSubgroup (∀ X : Cᵒᵖ, M.obj X) where
  carrier := {u | ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), M.map f (u X) = u Y}
  zero_mem' := by
    intro X Y f
    exact map_zero (M.restrictₛₗ f)
  add_mem' {a b} ha hb := by
    intro X Y f
    refine (map_add (M.restrictₛₗ f) (a X) (b X)).trans ?_
    simp only [restrictₛₗ_apply, Pi.add_apply]
    rw [ha f, hb f]
  neg_mem' {a} ha := by
    intro X Y f
    refine (map_neg (M.restrictₛₗ f) (a X)).trans ?_
    simp only [restrictₛₗ_apply, Pi.neg_apply]
    rw [ha f]

/-- **The global sections of a presheaf of modules form an abelian group**, under pointwise
addition: this is `PresheafOfModules.sectionsAddSubgroup`, whose carrier is the type of sections
on the nose. -/
noncomputable instance sectionsAddCommGroup (M : PresheafOfModules.{v} R) :
    AddCommGroup M.sections :=
  inferInstanceAs (AddCommGroup M.sectionsAddSubgroup)

/-- The value of a sum of sections of a presheaf of modules over an object is the sum of the
values. -/
@[simp]
theorem sections_eval_add {M : PresheafOfModules.{v} R} (s t : M.sections) (X : Cᵒᵖ) :
    (s + t).eval X = s.eval X + t.eval X := rfl

/-- The value of the zero section of a presheaf of modules over an object is zero. -/
@[simp]
theorem sections_eval_zero (M : PresheafOfModules.{v} R) (X : Cᵒᵖ) :
    (0 : M.sections).eval X = 0 := rfl

/-- The value of the negative of a section of a presheaf of modules over an object is the
negative of the value. -/
@[simp]
theorem sections_eval_neg {M : PresheafOfModules.{v} R} (s : M.sections) (X : Cᵒᵖ) :
    (-s).eval X = -s.eval X := rfl

/-- The restriction map along `g` sends the value of a global section over `X` to its value
over `Y`. -/
private theorem restrictₛₗ_eval {M : PresheafOfModules.{v} R} (s : M.sections) {X Y : Cᵒᵖ}
    (g : X ⟶ Y) : M.restrictₛₗ g (s.eval X) = s.eval Y := sections_property s g

/-- **An additivity relation between the values of three global sections over an object passes
to the objects above it.**  This is the step that makes additivity of a map of global sections a
*local* condition on the site: the relation `t = t₁ + t₂` read over one object restricts along
every morphism out of it. -/
theorem sections_eval_add_of_map {M : PresheafOfModules.{v} R} {t t₁ t₂ : M.sections}
    {X Y : Cᵒᵖ} (g : X ⟶ Y) (h : t.eval X = t₁.eval X + t₂.eval X) :
    t.eval Y = t₁.eval Y + t₂.eval Y := by
  rw [← restrictₛₗ_eval t g, h, map_add, restrictₛₗ_eval, restrictₛₗ_eval]

/-- **An additivity relation between the values of three global sections over an object is
witnessed by the restriction maps into it.**  This is the form in which separatedness of a sheaf
of modules consumes the relation: to compare two sections over an object it compares their
restrictions along the arrows of a covering sieve, and over the source of such an arrow the
relation is already known. -/
theorem sections_restrictₛₗ_eval_add {M : PresheafOfModules.{v} R} {t t₁ t₂ : M.sections}
    {X Y : Cᵒᵖ} (g : X ⟶ Y) (h : t.eval Y = t₁.eval Y + t₂.eval Y) :
    M.restrictₛₗ g (t.eval X) = M.restrictₛₗ g (t₁.eval X + t₂.eval X) := by
  rw [map_add, restrictₛₗ_eval, restrictₛₗ_eval, restrictₛₗ_eval, h]

/-- **The map on global sections induced by a morphism of presheaves of modules is additive.** -/
theorem sectionsMap_add {M N : PresheafOfModules.{v} R} (φ : M ⟶ N) (s t : M.sections) :
    sectionsMap φ (s + t) = sectionsMap φ s + sectionsMap φ t :=
  sections_ext _ _ fun X ↦ map_add (φ.app X).hom (s.eval X) (t.eval X)

/-- The map on global sections induced by a morphism of presheaves of modules, bundled as a
morphism of abelian groups. -/
@[simps]
noncomputable def sectionsAddMonoidHom {M N : PresheafOfModules.{v} R} (φ : M ⟶ N) :
    M.sections →+ N.sections where
  toFun := sectionsMap φ
  map_zero' := sections_ext _ _ fun X ↦ map_zero (φ.app X).hom
  map_add' := sectionsMap_add φ

end PresheafOfModules

end
