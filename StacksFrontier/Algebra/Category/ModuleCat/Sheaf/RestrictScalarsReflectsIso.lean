module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of scalars reflects isomorphisms

Let `α : R ⟶ R'` be a morphism of (pre)sheaves of rings on a site.  Restriction of scalars
along `α` changes neither the underlying presheaf of abelian groups nor the underlying maps, so
a morphism of `R'`-modules whose restriction is an isomorphism is already an isomorphism: the
inverse furnished by the restriction is automatically `R'`-linear, because it is linear once
composed with a bijection that is.

Mathlib has the statement for modules over a ring, `ModuleCat.restrictScalars` being an instance
of `CategoryTheory.Functor.ReflectsIsomorphisms`, and the faithfulness of restriction of scalars
of (pre)sheaves of modules; this file supplies the reflection of isomorphisms for presheaves and
for sheaves of modules.

Note that this is *not* fullness: nothing here produces a morphism of `R'`-modules from one of
`R`-modules, and so nothing here identifies two `R'`-modules whose restrictions happen to be
isomorphic.  What it does is promote an isomorphism of restrictions **of a given morphism** to an
isomorphism upstairs.

## Main results

* `Stacks.PresheafOfModules.ChangeOfRings.isIso_of_isIso_restrictScalars` and
  `Stacks.PresheafOfModules.ChangeOfRings.reflectsIsomorphisms_restrictScalars`: restriction of
  scalars of presheaves of modules reflects isomorphisms.
* `Stacks.SheafOfModules.ChangeOfRings.isIso_of_isIso_restrictScalars` and
  `Stacks.SheafOfModules.ChangeOfRings.reflectsIsomorphisms_restrictScalars`: restriction of
  scalars of sheaves of modules reflects isomorphisms.

## Implementation notes

The module universe has to be ascribed wherever `SheafOfModules.restrictScalars` is applied.
Elaborating `(SheafOfModules.restrictScalars α).obj M` with the module universe left to
unification fails: the `CategoryTheory.Category` instance on the source category is sought while
that universe is still a metavariable, and the search reports
`failed to synthesize Category.{u + 1, u + 2} (SheafOfModules …)` even though the instance is
found at once when the universe is written.  Every occurrence below therefore carries `.{v}`.

The proof is pointwise and goes through the three functors that forget structure, each of which
leaves the underlying map alone, so that each step is a transport along `Eq.refl`:
`PresheafOfModules.evaluation` turns the hypothesis into invertibility of
`(ModuleCat.restrictScalars (α.app X).hom).map (f.app X)`, Mathlib's reflection of isomorphisms
for `ModuleCat.restrictScalars` makes `f.app X` invertible, `PresheafOfModules.isoMk` assembles
the componentwise inverses (the naturality square is literally the one of `f`), and
`SheafOfModules.forget` reflects isomorphisms because it is fully faithful.
-/

@[expose] public section

open CategoryTheory

universe v v' u u'

namespace Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')
variable {M₁ M₂ : PresheafOfModules.{v} R'}

/-- If the restriction of scalars of a morphism of presheaves of modules is an isomorphism, then
each of its components is an isomorphism: restriction of scalars of modules over a ring reflects
isomorphisms, and evaluating the restriction of scalars of `f` at an object of the site is the
restriction of scalars of the component of `f` there. -/
theorem isIso_app_of_isIso_restrictScalars (f : M₁ ⟶ M₂)
    [IsIso ((PresheafOfModules.restrictScalars.{v} α).map f)] (X : Cᵒᵖ) :
    IsIso (PresheafOfModules.Hom.app f X) := by
  have h₀ : IsIso ((PresheafOfModules.evaluation.{v} R X).map
      ((PresheafOfModules.restrictScalars.{v} α).map f)) := inferInstance
  have h₁ : IsIso ((ModuleCat.restrictScalars (α.app X).hom).map
      (PresheafOfModules.Hom.app f X)) := h₀
  exact isIso_of_reflects_iso (PresheafOfModules.Hom.app f X)
    (ModuleCat.restrictScalars (α.app X).hom)

/-- **Restriction of scalars of presheaves of modules reflects isomorphisms.**  Each component of
the morphism is an isomorphism of modules, and the componentwise inverses form a morphism of
presheaves of modules because the naturality square is the one of the morphism itself. -/
theorem isIso_of_isIso_restrictScalars (f : M₁ ⟶ M₂)
    [IsIso ((PresheafOfModules.restrictScalars.{v} α).map f)] : IsIso f := by
  have happ : ∀ X : Cᵒᵖ, IsIso (PresheafOfModules.Hom.app f X) := fun X =>
    isIso_app_of_isIso_restrictScalars α f X
  let e : M₁ ≅ M₂ := PresheafOfModules.isoMk
    (fun X => asIso (PresheafOfModules.Hom.app f X))
    (fun {_X _Y} g => PresheafOfModules.Hom.naturality f g)
  have hfe : f = e.hom := PresheafOfModules.hom_ext fun _X => rfl
  rw [hfe]
  infer_instance

/-- Restriction of scalars of presheaves of modules reflects isomorphisms. -/
instance reflectsIsomorphisms_restrictScalars :
    (PresheafOfModules.restrictScalars.{v} α).ReflectsIsomorphisms where
  reflects f _ := isIso_of_isIso_restrictScalars α f

end Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable {O O' : Sheaf J RingCat.{u}} (f : O ⟶ O')
variable {G₁ G₂ : SheafOfModules.{v} O'}

/-- **Restriction of scalars of sheaves of modules reflects isomorphisms.**  A morphism of
sheaves of modules is an isomorphism as soon as the underlying morphism of presheaves of modules
is, and restriction of scalars of sheaves of modules is restriction of scalars of the underlying
presheaves of modules. -/
theorem isIso_of_isIso_restrictScalars (φ : G₁ ⟶ G₂)
    [IsIso ((SheafOfModules.restrictScalars.{v} f).map φ)] : IsIso φ := by
  have h₀ : IsIso ((SheafOfModules.forget.{v} O).map
      ((SheafOfModules.restrictScalars.{v} f).map φ)) := inferInstance
  have h₁ : IsIso ((PresheafOfModules.restrictScalars.{v} f.hom).map
      (SheafOfModules.Hom.val φ)) := h₀
  have h₂ : IsIso (SheafOfModules.Hom.val φ) :=
    Stacks.PresheafOfModules.ChangeOfRings.isIso_of_isIso_restrictScalars f.hom
      (SheafOfModules.Hom.val φ)
  have h₃ : IsIso ((SheafOfModules.forget.{v} O').map φ) := h₂
  exact isIso_of_reflects_iso φ (SheafOfModules.forget.{v} O')

/-- Restriction of scalars of sheaves of modules reflects isomorphisms. -/
instance reflectsIsomorphisms_restrictScalars :
    (SheafOfModules.restrictScalars.{v} f).ReflectsIsomorphisms where
  reflects φ _ := isIso_of_isIso_restrictScalars f φ

end Stacks.SheafOfModules.ChangeOfRings

end
