module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria

/-!
# Morphisms between open subobjects of the big fppf site

`AlgebraicGeometry.Space.openSubobject` regards an open subscheme of the scheme of an object of
the big fppf site over `S` as an object of that site.  This file lifts a morphism of schemes
between two such open subschemes, compatible with a morphism of the ambient objects, to a
morphism of the site.

## Main definitions

* `AlgebraicGeometry.Space.openSubobjectLift`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The lift of a morphism of open subschemes to the open subobjects of the site.**  For a
morphism `k : T' ⟶ T` of the site, open immersions `j : A ⟶ T` and `j' : A' ⟶ T'` and a morphism
of schemes `φ : A' ⟶ A` with `φ ≫ j = j' ≫ k`, the morphism of the site between the two open
subobjects whose morphism of schemes is `φ`. -/
def openSubobjectLift {T T' : BigFppfOver B S hS} (k : T' ⟶ T) {A A' : Scheme.{u}}
    (j : A ⟶ (BigFppfOver.toScheme B S hS).obj T) (hj : AlgebraicGeometry.IsOpenImmersion j)
    (j' : A' ⟶ (BigFppfOver.toScheme B S hS).obj T')
    (hj' : AlgebraicGeometry.IsOpenImmersion j') (φ : A' ⟶ A)
    (hφ : φ ≫ j = j' ≫ (BigFppfOver.toScheme B S hS).map k) :
    openSubobject B S hS T' j' hj' ⟶ openSubobject B S hS T j hj :=
  Over.homMk (B.inclusion.preimage (show B.inclusion.obj
      (B.obj (@Scheme.size_lt_of_isOpenImmersion _ _ _ j' hj' T'.left.property)) ⟶
      B.inclusion.obj (B.obj (@Scheme.size_lt_of_isOpenImmersion _ _ _ j hj T.left.property))
      from φ)) (by
    apply B.inclusion.map_injective
    simp only [openSubobject, Over.mk_hom, Functor.map_comp, Functor.map_preimage]
    rw [← Category.assoc, hφ, Category.assoc]
    congr 1
    exact congrArg B.inclusion.map (Over.w k))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.openSubobjectLift` is the given
morphism. -/
theorem toScheme_map_openSubobjectLift {T T' : BigFppfOver B S hS} (k : T' ⟶ T)
    {A A' : Scheme.{u}}
    (j : A ⟶ (BigFppfOver.toScheme B S hS).obj T) (hj : AlgebraicGeometry.IsOpenImmersion j)
    (j' : A' ⟶ (BigFppfOver.toScheme B S hS).obj T')
    (hj' : AlgebraicGeometry.IsOpenImmersion j') (φ : A' ⟶ A)
    (hφ : φ ≫ j = j' ≫ (BigFppfOver.toScheme B S hS).map k) :
    (BigFppfOver.toScheme B S hS).map (openSubobjectLift B S hS k j hj j' hj' φ hφ) = φ :=
  B.inclusion.map_preimage _

/-- `AlgebraicGeometry.Space.openSubobjectLift` lies over the given morphism of the ambient
objects. -/
theorem openSubobjectLift_comp {T T' : BigFppfOver B S hS} (k : T' ⟶ T) {A A' : Scheme.{u}}
    (j : A ⟶ (BigFppfOver.toScheme B S hS).obj T) (hj : AlgebraicGeometry.IsOpenImmersion j)
    (j' : A' ⟶ (BigFppfOver.toScheme B S hS).obj T')
    (hj' : AlgebraicGeometry.IsOpenImmersion j') (φ : A' ⟶ A)
    (hφ : φ ≫ j = j' ≫ (BigFppfOver.toScheme B S hS).map k) :
    openSubobjectLift B S hS k j hj j' hj' φ hφ ≫ openSubobjectHom B S hS T j hj =
      openSubobjectHom B S hS T' j' hj' ≫ k := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rwa [Functor.map_comp, Functor.map_comp, toScheme_map_openSubobjectLift,
    toScheme_map_openSubobjectHom, toScheme_map_openSubobjectHom]

end AlgebraicGeometry.Space

end
