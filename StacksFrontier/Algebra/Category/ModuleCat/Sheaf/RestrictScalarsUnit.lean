module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Restriction of scalars along an isomorphism carries the free module of rank one to itself

A ring `A` read as a module over an isomorphic ring `B` is the free `B`-module of rank one, the
identification being the isomorphism itself.  This file records that fact for a module over a
ring, and the two statements of presheaves of modules it gives: restriction of scalars along an
isomorphism of presheaves of rings, and the pushforward along a functor with an isomorphic
change of scalars, both carry the free presheaf of modules of rank one to the free presheaf of
modules of rank one.

## Main definitions

* `ModuleCat.restrictScalarsSelfEquiv`: a ring, read as a module over an isomorphic ring, is the
  free module of rank one.
* `PresheafOfModules.restrictScalarsUnitIso`: restriction of scalars along an isomorphism of
  presheaves of rings carries the free presheaf of modules of rank one to the free presheaf of
  modules of rank one.
* `PresheafOfModules.pushforwardUnitIso`: the same for `PresheafOfModules.pushforward`.

## Implementation notes

`PresheafOfModules.pushforwardUnitIso` is literally `PresheafOfModules.restrictScalarsUnitIso`:
`PresheafOfModules.pushforward` is by definition `PresheafOfModules.pushforward₀` followed by a
restriction of scalars, and `pushforward₀` carries the free presheaf of rank one over `R` to the
free presheaf of rank one over `G.op ⋙ R` on the nose, both being the presheaf of rings itself
with its multiplication as the action.  Only the type ascription differs.

The change of scalars is taken as a morphism carrying an `IsIso` instance rather than as a
`CategoryTheory.Iso`.  That is what a consumer can use: the functor it applies is
`PresheafOfModules.pushforward` of a *morphism*, and an isomorphism whose `hom` field is only
definitionally that morphism leaves the two functors to be unified under a metavariable, which
fails.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace ModuleCat

/-- **A ring is the free module of rank one over any isomorphic ring.**  For an isomorphism
`i : A ≅ B` of rings, the `B`-module `B` read as an `A`-module along `i` is the `A`-module `A`,
the identification being `i` itself. -/
def restrictScalarsSelfEquiv {A B : RingCat.{w}} (i : A ≅ B) :
    ((ModuleCat.restrictScalars i.hom.hom).obj (ModuleCat.of B B)) ≃ₗ[A] ModuleCat.of A A where
  toFun x := i.ringCatIsoToRingEquiv.symm x
  invFun x := i.ringCatIsoToRingEquiv x
  map_add' x y := map_add i.ringCatIsoToRingEquiv.symm x y
  map_smul' a x := by
    change i.ringCatIsoToRingEquiv.symm
      (i.ringCatIsoToRingEquiv a * (show (B : Type w) from x)) = _
    rw [map_mul, RingEquiv.symm_apply_apply]
    rfl
  left_inv x := i.ringCatIsoToRingEquiv.apply_symm_apply x
  right_inv x := i.ringCatIsoToRingEquiv.symm_apply_apply x

end ModuleCat

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **Restriction of scalars along an isomorphism carries the free presheaf of modules of rank
one to the free presheaf of modules of rank one.**  Objectwise this is
`ModuleCat.restrictScalarsSelfEquiv`, and the naturality is that of the inverse of the
isomorphism of presheaves of rings. -/
def restrictScalarsUnitIso {R S : Cᵒᵖ ⥤ RingCat.{w}} (φ : S ⟶ R) [IsIso φ] :
    (restrictScalars.{w} φ).obj (unit R) ≅ unit S :=
  isoMk (fun X ↦ (ModuleCat.restrictScalarsSelfEquiv ((asIso φ).app X)).toModuleIso)
    (fun {_ _} f ↦ by ext x; exact congr($((asIso φ).inv.naturality f) x))

/-- **The pushforward of the free presheaf of modules of rank one along an isomorphic change of
scalars is the free presheaf of modules of rank one.** -/
def pushforwardUnitIso {G : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{w}} {S : Cᵒᵖ ⥤ RingCat.{w}}
    (φ : S ⟶ G.op ⋙ R) [IsIso φ] :
    (pushforward.{w} φ).obj (unit R) ≅ unit S :=
  restrictScalarsUnitIso φ

end PresheafOfModules

end
