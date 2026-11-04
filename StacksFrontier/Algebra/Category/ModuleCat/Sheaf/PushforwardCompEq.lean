module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Composition and transport of direct images of sheaves of modules, as equalities

Mathlib's `SheafOfModules.pushforwardComp` identifies the composite of two direct images of
sheaves of modules with the direct image for the composite functor of sites, and it is
`Iso.refl`: the two functors are *definitionally* equal.  This file records that equality as an
`Eq`, together with the transport of a direct image along an equality of functors of sites.

## Main results

* `Stacks.SheafOfModules.pushforwardComp_eq`: `g_* ∘ f_* = (f ⋙ g)_*` on sheaves of modules.
* `Stacks.SheafOfModules.pushforwardComp_id_eq`: the same when the inner structure map is an
  identity, so that the composite structure map is the outer one unchanged.
* `Stacks.SheafOfModules.pushforward_eq_of_heq`: direct images along equal functors of sites
  agree, given heterogeneously equal structure maps.

## Implementation notes

The two composition laws hold by `rfl`, and the point of stating them is that the `rfl` is
checked *here*, at generic functors of sites and generic structure maps, where it is cheap.
Applying them at a concrete pair of direct images only instantiates a closed proof term, so no
definitional unfolding of the concrete functors of sites takes place; checking the same `rfl`
directly at the direct images of a geometric situation is a `whnf` timeout.

This is why the equalities are worth having next to `SheafOfModules.pushforwardComp`: an
isomorphism between the two composites cannot be fed to `CategoryTheory.Functor.congr_hom` or
`CategoryTheory.Functor.hcongr_hom`, and `Iso.refl` yields no `Eq`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v r v₁ u₁ v₂ u₂ v₃ u₃

namespace Stacks.SheafOfModules

section Comp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {K' : GrothendieckTopology D'} {F : C ⥤ D} {G : D ⥤ D'} [F.IsContinuous J K]
  [G.IsContinuous K K'] {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
  {R' : Sheaf K' RingCat.{r}}

/-- **The composite of two direct images of sheaves of modules is the direct image for the
composite functor of sites**, as an equality of functors: for `φ : S ⟶ f_* R` and
`ψ : R ⟶ g_* R'`, restricting along `g` and then along `f` is restricting along `f ⋙ g`, with the
structure map `φ` followed by the restriction along `f` of `ψ`.

This is the `Eq` behind `SheafOfModules.pushforwardComp`, which is `Iso.refl`. -/
theorem pushforwardComp_eq (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{r} K K').obj R') :
    haveI : (F ⋙ G).IsContinuous J K' := Functor.isContinuous_comp F G J K K'
    _root_.SheafOfModules.pushforward.{v} ψ ⋙ _root_.SheafOfModules.pushforward.{v} φ =
      _root_.SheafOfModules.pushforward.{v} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map ψ) :=
  rfl

/-- **The composite of two direct images of sheaves of modules when the inner structure map is an
identity**: restricting along `g` with the identity structure map and then along `f` with
structure map `φ` is restricting along `f ⋙ g` with structure map `φ`.

This is `Stacks.SheafOfModules.pushforwardComp_eq` with `ψ` an identity; the composite structure
map `φ ≫ f_*(𝟙)` is `φ` itself. -/
theorem pushforwardComp_id_eq
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj
      ((G.sheafPushforwardContinuous RingCat.{r} K K').obj R')) :
    haveI : (F ⋙ G).IsContinuous J K' := Functor.isContinuous_comp F G J K K'
    _root_.SheafOfModules.pushforward.{v}
          (𝟙 ((G.sheafPushforwardContinuous RingCat.{r} K K').obj R')) ⋙
        _root_.SheafOfModules.pushforward.{v} φ =
      _root_.SheafOfModules.pushforward.{v} (F := F ⋙ G) φ :=
  rfl

end Comp

section Transport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- **Direct images of sheaves of modules along equal functors of sites agree**, when the two
structure maps are heterogeneously equal.

The two structure maps cannot be compared by an `Eq`: they are morphisms into the direct images
of one sheaf of rings along the two functors of sites, and those are two different objects of
`CategoryTheory.Sheaf`.  `HEq` is what makes the comparison statable, and once the functors of
sites are substituted the two types coincide and the heterogeneous equation becomes an equation.

This is the form to use when the two structure maps are literally the same term — an identity,
say — so that the hypothesis is `HEq.rfl`.  Carrying the structure map across the equality with
`CategoryTheory.eqToHom` instead, as in `Stacks.SheafOfModules.pushforward_eqToHom_eq`, leaves an
`eqToHom` whose two endpoints are not syntactically equal, which `CategoryTheory.eqToHom_refl`
cannot remove even when they are definitionally equal. -/
theorem pushforward_eq_of_heq {F F' : C ⥤ D} [F.IsContinuous J K] [F'.IsContinuous J K]
    (h : F = F') {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R)
    (φ' : S ⟶ (F'.sheafPushforwardContinuous RingCat.{r} J K).obj R) (hφ : φ ≍ φ') :
    _root_.SheafOfModules.pushforward.{v} φ = _root_.SheafOfModules.pushforward.{v} φ' := by
  subst h
  exact congrArg _ (eq_of_heq hφ)

end Transport

end Stacks.SheafOfModules

end
