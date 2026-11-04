module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# Factoring a morphism through a submodule

Let `M` be a (pre)sheaf of modules and `N` a submodule of it. A morphism `f : P ⟶ M` whose
components all take values in `N` factors uniquely through the inclusion `N.ι`. This file
supplies that factorization.

## Main definitions

* `PresheafOfModules.Submodule.factorThru` and `SheafOfModules.Submodule.factorThru`: the
  factorization of a morphism whose values lie in the submodule.

## Main results

* `PresheafOfModules.Submodule.factorThru_ι` and `SheafOfModules.Submodule.factorThru_ι`: the
  factorization composed with the inclusion is the original morphism.
* `SheafOfModules.Submodule.eq_factorThru` and
  `SheafOfModules.Submodule.existsUnique_factorThru`: the factorization is the unique morphism
  with that property.

## Implementation notes

The presheaf-level factorization is `LinearMap.codRestrict` applied objectwise, and its
naturality is the naturality of `f` read on elements. The sheaf-level one is the presheaf-level
one, since a morphism of sheaves of modules is a morphism of the underlying presheaves of
modules and the underlying presheaf of `N.toSheafOfModules` is `N.toSubmodule.toPresheafOfModules`
on the nose. Uniqueness needs no computation: `N.ι` is a monomorphism.

## References

* [Stacks Project, Tag 01AP](https://stacks.math.columbia.edu/tag/01AP)
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace PresheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M : PresheafOfModules.{v} R} (N : M.Submodule)

/-- A morphism `f : P ⟶ M` of presheaves of modules all of whose values lie in a submodule `N`
of `M` factors through `N`, objectwise by restricting the codomain. -/
noncomputable def factorThru {P : PresheafOfModules.{v} R} (f : P ⟶ M)
    (hf : ∀ (X : Cᵒᵖ) (x : P.obj X), f.app X x ∈ N.obj X) :
    P ⟶ N.toPresheafOfModules where
  app X := ModuleCat.ofHom (LinearMap.codRestrict (N.obj X) (f.app X).hom (hf X))
  naturality {X Y} g := by
    ext x
    apply Subtype.ext
    exact naturality_apply f g x

/-- The factorization of `f` through `N` has the same values as `f`. -/
@[simp]
lemma factorThru_app_val {P : PresheafOfModules.{v} R} (f : P ⟶ M)
    (hf : ∀ (X : Cᵒᵖ) (x : P.obj X), f.app X x ∈ N.obj X) (X : Cᵒᵖ) (x : P.obj X) :
    dsimp% ((N.factorThru f hf).app X x).val = f.app X x := rfl

/-- The factorization of `f` through `N`, composed with the inclusion of `N`, is `f`. -/
@[reassoc (attr := simp)]
lemma factorThru_ι {P : PresheafOfModules.{v} R} (f : P ⟶ M)
    (hf : ∀ (X : Cᵒᵖ) (x : P.obj X), f.app X x ∈ N.obj X) :
    N.factorThru f hf ≫ N.ι = f := by
  ext X x
  rfl

end PresheafOfModules.Submodule

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{v} R} (N : M.Submodule)

/-- A morphism `f : P ⟶ M` of sheaves of modules all of whose values lie in a submodule `N` of
`M` factors through `N`. -/
noncomputable def factorThru {P : SheafOfModules.{v} R} (f : P ⟶ M)
    (hf : ∀ (X : Cᵒᵖ) (x : P.val.obj X), f.val.app X x ∈ N.obj X) :
    P ⟶ N.toSheafOfModules :=
  ⟨N.toSubmodule.factorThru f.val hf⟩

/-- The factorization of `f` through `N`, composed with the inclusion of `N`, is `f`. -/
@[reassoc (attr := simp)]
lemma factorThru_ι {P : SheafOfModules.{v} R} (f : P ⟶ M)
    (hf : ∀ (X : Cᵒᵖ) (x : P.val.obj X), f.val.app X x ∈ N.obj X) :
    N.factorThru f hf ≫ N.ι = f :=
  SheafOfModules.hom_ext (N.toSubmodule.factorThru_ι f.val hf)

/-- Any morphism into `N` whose composite with the inclusion is `f` is the factorization of `f`,
because the inclusion is a monomorphism. -/
lemma eq_factorThru {P : SheafOfModules.{v} R} (f : P ⟶ M)
    (hf : ∀ (X : Cᵒᵖ) (x : P.val.obj X), f.val.app X x ∈ N.obj X)
    (g : P ⟶ N.toSheafOfModules) (hg : g ≫ N.ι = f) : g = N.factorThru f hf := by
  rw [← cancel_mono N.ι, hg, factorThru_ι]

/-- A morphism whose values lie in `N` factors through `N` in exactly one way. -/
lemma existsUnique_factorThru {P : SheafOfModules.{v} R} (f : P ⟶ M)
    (hf : ∀ (X : Cᵒᵖ) (x : P.val.obj X), f.val.app X x ∈ N.obj X) :
    ∃! g : P ⟶ N.toSheafOfModules, g ≫ N.ι = f :=
  ⟨N.factorThru f hf, N.factorThru_ι f hf, N.eq_factorThru f hf⟩

end SheafOfModules.Submodule

end
