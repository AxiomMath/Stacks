module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization

/-!
# Sections of a module on an affine open, through `IsAffineOpen.fromSpec`

An affine open `U` of a scheme `X` comes with the open immersion
`hU.fromSpec : Spec Γ(X, U) ⟶ X`. Pulling a module `F` back along it and taking global
sections gives the same `Γ(X, U)`-module as taking the sections of `F` over `U`. This file
gives that identification both as an isomorphism in the category of modules and as a
`Γ(X, U)`-linear equivalence.

## Main definitions

* `AlgebraicGeometry.affineSectionsIso`: the isomorphism
  `Γ(F.restrict hU.fromSpec, ⊤) ≅ Γ(F, U)`.
* `AlgebraicGeometry.affineSectionsLinearEquiv`: the same map as a `Γ(X, U)`-linear
  equivalence.

## Main results

* `AlgebraicGeometry.affineSectionsIso_hom_smul`: `affineSectionsIso` is `Γ(X, U)`-linear.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The sections over an affine open `U` of a module on `X` agree with the global sections of
its restriction along `hU.fromSpec`. -/
noncomputable def affineSectionsIso {X : Scheme.{u}}
    (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(F.restrict hU.fromSpec, ⊤) ≅ Γ(F, U) :=
  F.restrictAppIso hU.fromSpec ⊤ ≪≫
    F.presheaf.mapIso (eqToIso (by
      rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec])).symm.op

/-- `AlgebraicGeometry.affineSectionsIso` is linear over the ring of functions on the affine
open. -/
lemma affineSectionsIso_hom_smul {X : Scheme.{u}}
    (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (r : Γ(X, U)) (t : Γ(F.restrict hU.fromSpec, ⊤)) :
    (affineSectionsIso F hU).hom (r • t) =
      r • (affineSectionsIso F hU).hom t := by
  let f := hU.fromSpec
  have he : f ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have hr : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (f.appIso ⊤).inv =
      X.presheaf.map (eqToHom he).op := by
    rw [← fromSpec_appLE_top hU]
    exact f.appLE_appIso_inv _
  change F.presheaf.map (eqToHom he.symm).op
    ((F.restrictAppIso f ⊤).hom (r • t)) = _
  rw [Scheme.Modules.smul_Spec_def]
  simp only [Opens.leTop, homOfLE_refl, op_id]
  rw [(Spec Γ(X, U)).presheaf.map_id]
  simp only [CommRingCat.id_apply]
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, F.map_smul]
  have hr' : X.presheaf.map (eqToHom he.symm).op
      ((f.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv r)) = r := by
    simp only [← CommRingCat.comp_apply, hr, ← Functor.map_comp]
    simp
  rw [hr']
  rfl

/-- The sections over an affine open `U` of a module on `X`, as a `Γ(X, U)`-linear equivalence
with the global sections of its restriction along `hU.fromSpec`. -/
noncomputable def affineSectionsLinearEquiv {X : Scheme.{u}}
    (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(F.restrict hU.fromSpec, ⊤) ≃ₗ[Γ(X, U)] Γ(F, U) :=
  LinearEquiv.ofBijective
    { toFun := ConcreteCategory.hom (affineSectionsIso F hU).hom
      map_add' := map_add (ConcreteCategory.hom (affineSectionsIso F hU).hom)
      map_smul' := affineSectionsIso_hom_smul F hU }
    (ConcreteCategory.bijective_of_isIso (affineSectionsIso F hU).hom)

@[simp]
lemma affineSectionsLinearEquiv_apply {X : Scheme.{u}}
    (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (t : Γ(F.restrict hU.fromSpec, ⊤)) :
    affineSectionsLinearEquiv F hU t = (affineSectionsIso F hU).hom t := rfl

end AlgebraicGeometry
