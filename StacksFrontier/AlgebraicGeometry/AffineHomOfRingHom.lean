module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Morphisms of affine schemes from ring maps on global sections

A morphism between affine schemes is determined by, and can be built from, the ring map it
induces on global sections: conjugating `Spec` of a ring map `Γ(X, ⊤) →+* Γ(Y, ⊤)` by the
canonical isomorphisms `Y ≅ Spec Γ(Y, ⊤)` and `X ≅ Spec Γ(X, ⊤)` gives a morphism `Y ⟶ X`
whose action on global sections is the given ring map.

## Main definitions

* `AlgebraicGeometry.affineHomOfRingHom` is the morphism of affine schemes induced by a ring
  map on global sections.

## Main results

* `AlgebraicGeometry.affineHomOfRingHom_appTop`: `affineHomOfRingHom φ` acts on global sections
  as `φ`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The morphism of affine schemes induced by a ring map on global sections. -/
def affineHomOfRingHom {Y X : Scheme.{u}} [IsAffine Y] [IsAffine X]
    (φ : Γ(X, ⊤) →+* Γ(Y, ⊤)) : Y ⟶ X :=
  Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ X.isoSpec.inv

/-- `affineHomOfRingHom φ` acts on global sections as `φ`. -/
lemma affineHomOfRingHom_appTop {Y X : Scheme.{u}} [IsAffine Y] [IsAffine X]
    (φ : Γ(X, ⊤) →+* Γ(Y, ⊤)) :
    (affineHomOfRingHom φ).appTop.hom = φ := by
  have h : affineHomOfRingHom φ ≫ X.toSpecΓ =
      Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
    simp [affineHomOfRingHom, Scheme.isoSpec]
  rw [Scheme.toSpecΓ_naturality, cancel_epi] at h
  simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end AlgebraicGeometry

end
