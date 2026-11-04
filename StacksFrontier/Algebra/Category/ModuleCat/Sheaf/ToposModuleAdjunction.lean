module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of sheaves of modules is left adjoint to pushforward

Let `F : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)`, and let
`φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R` be a morphism of sheaves of
rings. Mathlib defines the pushforward functor `SheafOfModules.pushforward φ`, and defines
pullback as a left adjoint of it *when one exists*, the existence being carried by the
typeclass `(SheafOfModules.pushforward φ).IsRightAdjoint`.

This file discharges that typeclass, so that the adjunction holds outright rather than
under a hypothesis, and then specializes it to a change of rings on a fixed site, where it
becomes the adjunction between extension and restriction of scalars.

## Main definitions

* `extendScalars` is extension of scalars along a morphism `R₁ ⟶ R₂` of sheaves of rings
  on a fixed site, defined as the left adjoint of `SheafOfModules.restrictScalars`.

## Main results

* `pushforward_isRightAdjoint` discharges `(SheafOfModules.pushforward φ).IsRightAdjoint`
  for an arbitrary continuous functor of small sites and an arbitrary morphism of sheaves
  of rings.
* `pullbackPushforwardAdjunction` is the resulting adjunction between pullback and
  pushforward of sheaves of modules, with no adjointness hypothesis.
* `extendRestrictScalarsAdjunction` is the change-of-rings adjunction
  `extendScalars α ⊣ SheafOfModules.restrictScalars α` on a fixed site.
* `extendScalarsIso` identifies extension of scalars with the sheafification of the
  sectionwise tensor product.

## Implementation notes

Mathlib's `SheafOfModules.pullbackPushforwardAdjunction` is `Adjunction.ofIsRightAdjoint`
applied to the pushforward, so all of its content sits in the `IsRightAdjoint` instance.
Mathlib supplies that instance only after assuming the corresponding presheaf-level
instance `(PresheafOfModules.pushforward φ.hom).IsRightAdjoint`. That presheaf-level
instance is itself available unconditionally from
`PresheafOfModules.pullbackObjIsDefined_eq_top`, but at a shape instance resolution does
not match against the sheaf-level goal. The one step taken here is to bridge those two by
hand; everything after it is Mathlib's.

Both sites are small categories whose type of objects, type of morphisms and sheaves of
rings all lie in a single universe `u`. This is forced, not chosen:
`PresheafOfModules.pullbackObjIsDefined_eq_top` is stated for `{C D : Type u}` with
`[SmallCategory C]`, `[SmallCategory D]` and sheaves of rings in `RingCat.{u}`, because its
proof resolves a presheaf of modules into free modules on representables, and a
representable presheaf on a `Category.{v} C` with `C : Type u` is not `u`-small unless
`v = u`. The module universe coincides with the ring universe for the same reason. Nothing
here is asserted at a wider universe than that argument supports.

For the change-of-rings specialization the continuous functor is the identity. Pushforward
of sheaves of modules along the identity functor of a site is *literally* restriction of
scalars, recorded by `pushforward_id_eq_restrictScalars`, so `extendScalars` is adjoint to
Mathlib's `restrictScalars` on the nose, with no transport along a comparison isomorphism.
Extension of scalars is defined by its universal property rather than as a tensor product;
`extendScalarsIso` supplies the concrete description, Mathlib's `pullbackIso` being the
sheafification of the sectionwise `R₂ ⊗[R₁] -`.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Sheaves.ModuleAdjunction

section Sites

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- Pushforward of presheaves of modules along a morphism of presheaves of rings over a
functor of small categories always has a left adjoint: its partial left adjoint is defined
on every object. -/
instance presheafPushforward_isRightAdjoint :
    (PresheafOfModules.pushforward.{u} φ.hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top φ.hom)

variable [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Pushforward of sheaves of modules along a continuous functor of small sites and a
morphism of sheaves of rings always has a left adjoint. -/
instance pushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{u} φ).IsRightAdjoint :=
  inferInstance

/-- **Stacks 03D7**, the ringed-site case: for a continuous functor of sites and a morphism
of sheaves of rings, pullback of sheaves of modules is left adjoint to pushforward. The
adjunction supplies the natural bijection between morphisms out of a pullback and morphisms
into a pushforward. -/
@[stacks 03D7 "ringed sites"]
noncomputable def pullbackPushforwardAdjunction :
    SheafOfModules.pullback.{u} φ ⊣ SheafOfModules.pushforward.{u} φ :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} φ

end Sites

section ChangeOfRings

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R₁ R₂ : Sheaf J RingCat.{u}}

/-- A morphism of sheaves of rings on a fixed site, read as a structure map over the
identity functor of that site. -/
def changeOfRingsStructureMap (α : R₁ ⟶ R₂) :
    R₁ ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{u} J J).obj R₂ :=
  α

/-- Pushforward of sheaves of modules along the identity functor of a site is restriction
of scalars. -/
lemma pushforward_id_eq_restrictScalars (α : R₁ ⟶ R₂) :
    SheafOfModules.pushforward.{u} (changeOfRingsStructureMap α) =
      SheafOfModules.restrictScalars.{u} α :=
  rfl

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Extension of scalars along a morphism `α : R₁ ⟶ R₂` of sheaves of rings on a fixed
site, defined as the left adjoint of restriction of scalars along `α`. -/
noncomputable def extendScalars (α : R₁ ⟶ R₂) :
    SheafOfModules.{u} R₁ ⥤ SheafOfModules.{u} R₂ :=
  SheafOfModules.pullback.{u} (changeOfRingsStructureMap α)

/-- Change of rings for sheaves of modules on a fixed site: extension of scalars along a
morphism of sheaves of rings is left adjoint to restriction of scalars along it. -/
noncomputable def extendRestrictScalarsAdjunction (α : R₁ ⟶ R₂) :
    extendScalars α ⊣ SheafOfModules.restrictScalars.{u} α :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (changeOfRingsStructureMap α)

/-- Extension of scalars is the sheafification of the sectionwise tensor product: on
sections over `U` the underlying presheaf of modules is `R₂(U) ⊗[R₁(U)] -`. -/
noncomputable def extendScalarsIso (α : R₁ ⟶ R₂) :
    extendScalars α ≅ SheafOfModules.forget R₁ ⋙
      PresheafOfModules.pullback.{u} (changeOfRingsStructureMap α).hom ⋙
        PresheafOfModules.sheafification (R₀ := R₂.obj) (𝟙 R₂.obj) :=
  SheafOfModules.pullbackIso.{u} (changeOfRingsStructureMap α)

end ChangeOfRings

end Stacks.Sheaves.ModuleAdjunction
