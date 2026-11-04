module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# The underlying abelian sheaf of a pushforward of sheaves of modules

Let `F : C ⥤ D` be a continuous functor of sites and let
`φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R` be a morphism of sheaves of rings.
Forgetting the module structure commutes with the induced pushforward of sheaves of modules:
the underlying abelian sheaf of `φ_* ℳ` is the restriction along `F` of the underlying abelian
sheaf of `ℳ`.

Mathlib has this comparison for presheaves of modules, as
`PresheafOfModules.pushforwardCompToPresheaf`, but not for sheaves.  The two sides of the
sheaf-level statement have *definitionally equal* underlying presheaves — the forgetful functor
of `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
is `rfl` on the structure maps — but comparing the two `CategoryTheory.Sheaf` structures
directly, with their `ModuleCat.restrictScalars` wrappers, is expensive enough to be worth
avoiding.  So the comparison is *built*, by lifting the presheaf-level isomorphism through the
fully faithful `CategoryTheory.sheafToPresheaf`, rather than asserted.

## Main definitions

* `Stacks.SheafOfModules.toSheafPushforwardIso`: the underlying abelian sheaf of a pushforward
  of sheaves of modules is the restriction of the underlying abelian sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u u₁ u₂

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D] {F : C ⥤ D}
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} [F.IsContinuous J K]
    {R : Sheaf K RingCat.{v}} {S : Sheaf J RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{v} J K).obj R)

/-- **Forgetting the module structure commutes with the pushforward of sheaves of modules.**
The underlying abelian sheaf of `φ_* ℳ` is the restriction along `F` of the underlying abelian
sheaf of `ℳ`.

This is `PresheafOfModules.pushforwardCompToPresheaf` lifted through the fully faithful
inclusion of sheaves into presheaves. -/
def toSheafPushforwardIso (M : _root_.SheafOfModules.{v} R) :
    (_root_.SheafOfModules.toSheaf.{v} S).obj
        ((_root_.SheafOfModules.pushforward.{v} φ).obj M) ≅
      (F.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj
        ((_root_.SheafOfModules.toSheaf.{v} R).obj M) :=
  (sheafToPresheaf J AddCommGrpCat.{v}).preimageIso
    ((PresheafOfModules.pushforwardCompToPresheaf φ.hom).app M.val)

end Stacks.SheafOfModules

end
