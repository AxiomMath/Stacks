module

public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation

/-!
# Morphisms into the site object presented by a contained scheme over an object

`AlgebraicGeometry.BigFppfOver.siteObjectOver` is the object of the big fppf category over `S`
determined by a contained scheme `Z` with a morphism `φ : Z ⟶ U` to the underlying scheme of an
object `U`.  This file supplies the morphisms *into* it: an object `T` of the category with a
morphism `σ : T ⟶ U` whose underlying morphism of schemes factors through `φ`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.siteHomOver`: a morphism of the big fppf category over `S` into
  `AlgebraicGeometry.BigFppfOver.siteObjectOver`, out of any object lying over the same target
  and factoring through the contained scheme.

## Main results

* `AlgebraicGeometry.BigFppfOver.toScheme_map_siteHomOver`: its underlying morphism of schemes is
  the given factorization.
* `AlgebraicGeometry.BigFppfOver.siteHomOver_comp_siteMapOver`: composed with
  `AlgebraicGeometry.BigFppfOver.siteMapOver` it is the morphism it was built over.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of the big fppf category over `S` into
`AlgebraicGeometry.BigFppfOver.siteObjectOver`.**

An object `T` of the category with a morphism `σ : T ⟶ U` and a factorization `ψ` of its
underlying morphism of schemes through `φ : Z ⟶ U` maps to the object `Z` presents over `U`:
the structure morphism of `AlgebraicGeometry.BigFppfOver.siteObjectOver` to `S` is `φ` followed
by that of `U`, so the triangle over `S` is the given factorization followed by the triangle of
`σ`. -/
def siteHomOver (U : BigFppfOver B S hS) {Z : Scheme.{u}} (hZ : B.Contains Z)
    (φ : Z ⟶ (toScheme B S hS).obj U) {T : BigFppfOver B S hS} (σ : T ⟶ U)
    (ψ : (toScheme B S hS).obj T ⟶ Z) (hψ : ψ ≫ φ = (toScheme B S hS).map σ) :
    T ⟶ siteObjectOver B S hS U hZ φ :=
  Over.homMk (⟨ψ⟩ : T.left ⟶ B.obj hZ) (by
    ext
    change ψ ≫ φ ≫ U.hom.hom = T.hom.hom
    rw [← Category.assoc, hψ]
    exact congrArg (·.hom) (Over.w σ))

/-- The underlying morphism of schemes of `AlgebraicGeometry.BigFppfOver.siteHomOver` is the given
factorization `ψ`. -/
@[simp]
theorem toScheme_map_siteHomOver (U : BigFppfOver B S hS) {Z : Scheme.{u}}
    (hZ : B.Contains Z) (φ : Z ⟶ (toScheme B S hS).obj U) {T : BigFppfOver B S hS} (σ : T ⟶ U)
    (ψ : (toScheme B S hS).obj T ⟶ Z) (hψ : ψ ≫ φ = (toScheme B S hS).map σ) :
    (toScheme B S hS).map (siteHomOver B S hS U hZ φ σ ψ hψ) = ψ :=
  rfl

/-- The morphism of `AlgebraicGeometry.BigFppfOver.siteHomOver` composed with the morphism to the
given object is the morphism it was built over. -/
@[simp]
theorem siteHomOver_comp_siteMapOver (U : BigFppfOver B S hS) {Z : Scheme.{u}}
    (hZ : B.Contains Z) (φ : Z ⟶ (toScheme B S hS).obj U) {T : BigFppfOver B S hS} (σ : T ⟶ U)
    (ψ : (toScheme B S hS).obj T ⟶ Z) (hψ : ψ ≫ φ = (toScheme B S hS).map σ) :
    siteHomOver B S hS U hZ φ σ ψ hψ ≫ siteMapOver B S hS U hZ φ = σ := by
  apply Over.OverMorphism.ext
  ext
  exact hψ

end BigFppfOver

end AlgebraicGeometry
