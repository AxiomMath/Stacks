module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModules
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulePullback

/-!
# Inverse images of modules across the relocalization of algebraic spaces

Let `g : T ⟶ S` be a morphism of a big fppf site and `φ : Y ⟶ Z` a representable morphism of
algebraic spaces over `T`. Viewing everything over `S` gives the morphism `Λ φ : Λ Y ⟶ Λ Z` of
lower-shriek extensions. Base change of étale charts along `φ` and along `Λ φ` correspond under
the equivalences of small étale sites of `AlgebraicGeometry.Space.SmallEtale.relocalize`, because
`Λ` preserves fibre products; hence the inverse images of modules along `φ` and along `Λ φ`
correspond under the equivalences `Mod(𝒪_Y) ≌ Mod(𝒪_{Λ Y})` and `Mod(𝒪_Z) ≌ Mod(𝒪_{Λ Z})`.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSpaceLowerShriek`, `AlgebraicGeometry.Space.relocalizeHom`:
  the lower-shriek extension as a functor on algebraic spaces.
* `AlgebraicGeometry.Space.relocalizeBaseChangeIso`: base change of charts commutes with the
  equivalences of small étale sites.

## Main results

* `AlgebraicGeometry.Space.relocalizePushforwardIso`: direct images along `φ` and `Λ φ`
  correspond.
* `AlgebraicGeometry.Space.relocalizeModulePullbackIso`: inverse images along `φ` and `Λ φ`
  correspond, `φ^* ⋙ E_Y ≅ E_Z ⋙ (Λ φ)^*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS)

/-- The lower-shriek extension of an algebraic space over `T` to `S`. -/
noncomputable abbrev relocalizeSpaceLowerShriek (Y : AlgebraicSpaces B T hT) :
    AlgebraicSpaces B S hS :=
  ⟨(OverShriek.relocalizePresheafFunctor g).obj Y.1, isAlgebraicSpace_relocalize' B hT hS g Y.1 Y.2⟩

variable {Y Z : AlgebraicSpaces B T hT} (φ : Y ⟶ Z) (hφ : yoneda.relativelyRepresentable φ.hom)

end AlgebraicGeometry.Space

end
