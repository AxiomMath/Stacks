module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Change of coefficient rings for sheaves of modules on the small étale site

Let `φ : Λ₁ ⟶ Λ₂` be a homomorphism of commutative rings and let `X` be a scheme. A sheaf of
`Λ₂`-modules on `X_étale` is a sheaf of `Λ₁`-modules through `φ`; this is the "restriction"
functor `res` of [Stacks, Tag 0GL6] and [Stacks, Tag 0GLF]. It has a left adjoint, the
sheafified extension of scalars `- ⊗_{Λ₁} Λ₂`, and a right adjoint, the coextension of scalars
`Hom_{Λ₁}(Λ₂, -)`, both computed on sections before sheafifying.

## Main definitions

All in the namespace `Stacks.EtaleCohomology.ChangeOfRings`.

* `restrictScalars φ X`: `res : Mod(X_étale, Λ₂) ⥤ Mod(X_étale, Λ₁)`.
* `coextendScalars φ X`: `Hom_{Λ₁}(Λ₂, -) : Mod(X_étale, Λ₁) ⥤ Mod(X_étale, Λ₂)`.
* `extendScalars φ X`: `- ⊗_{Λ₁} Λ₂ : Mod(X_étale, Λ₁) ⥤ Mod(X_étale, Λ₂)`.
* `restrictCoextendScalarsAdj φ X` and `extendRestrictScalarsAdj φ X`: the two adjunctions.

## Implementation notes

The two rings are taken in the same universe `r`, so that their categories of sheaves of modules
`Stacks.EtaleCohomology.EtaleModules` have coefficients in the same universe `max (u + 1) r`
and restriction of scalars of `ModuleCat` applies sectionwise. Restriction and coextension of
scalars preserve limits, so they preserve the sheaf condition and act by composition; extension of
scalars does not, and is followed by sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology.ChangeOfRings

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- **Restriction of scalars `res : Mod(X_étale, Λ₂) ⥤ Mod(X_étale, Λ₁)`** along `φ`: a sheaf of
`Λ₂`-modules read as a sheaf of `Λ₁`-modules through `φ`, section by section. -/
abbrev restrictScalars (X : Scheme.{u}) :
    EtaleModules.{u, r} Λ₂ X ⥤ EtaleModules.{u, r} Λ₁ X :=
  sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars φ)

/-- **Coextension of scalars `Hom_{Λ₁}(Λ₂, -) : Mod(X_étale, Λ₁) ⥤ Mod(X_étale, Λ₂)`** along
`φ`, section by section. -/
abbrev coextendScalars (X : Scheme.{u}) :
    EtaleModules.{u, r} Λ₁ X ⥤ EtaleModules.{u, r} Λ₂ X :=
  sheafCompose X.smallEtaleTopology (ModuleCat.coextendScalars φ)

/-- Restriction of scalars of sheaves of modules is additive. -/
instance (X : Scheme.{u}) : (restrictScalars φ X).Additive where
  map_add := by intros; rfl

/-- **Restriction of scalars is left adjoint to coextension of scalars**, on sheaves of modules
on `X_étale`: the sectionwise adjunction restricted to sheaves. -/
def restrictCoextendScalarsAdj (X : Scheme.{u}) : restrictScalars φ X ⊣ coextendScalars φ X :=
  ((ModuleCat.restrictCoextendScalarsAdj φ).whiskerRight (C := X.Etaleᵒᵖ)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _) (Iso.refl _) (Iso.refl _)

/-- **Extension of scalars `- ⊗_{Λ₁} Λ₂ : Mod(X_étale, Λ₁) ⥤ Mod(X_étale, Λ₂)`** along `φ`:
sectionwise extension of scalars followed by sheafification. -/
abbrev extendScalars (X : Scheme.{u}) :
    EtaleModules.{u, r} Λ₁ X ⥤ EtaleModules.{u, r} Λ₂ X :=
  Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.extendScalars φ)

/-- **Extension of scalars is left adjoint to restriction of scalars**, on sheaves of modules on
`X_étale`. -/
def extendRestrictScalarsAdj (X : Scheme.{u}) : extendScalars φ X ⊣ restrictScalars φ X :=
  Sheaf.adjunction X.smallEtaleTopology (ModuleCat.extendRestrictScalarsAdj φ)

end Stacks.EtaleCohomology.ChangeOfRings

end
