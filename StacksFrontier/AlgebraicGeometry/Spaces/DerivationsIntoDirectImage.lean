module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Derivations into a direct image and maps out of the pulled back differentials

Let `a : X ⟶ Y` and `b : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`, and let
`C` be a sheaf of `𝒪_X`-modules on the small étale site of `X`.  A `Z`-derivation
`D : 𝒪_Y ⟶ a_*C` factors through the universal `Z`-derivation `d_{Y/Z}` by a unique
`𝒪_Y`-linear map `θ : Ω_{Y/Z} ⟶ a_*C`, and by the adjunction `a^* ⊣ a_*` such a `θ` is the
same thing as an `𝒪_X`-linear map `θ : a^*Ω_{Y/Z} ⟶ C`.  Composing the two bijections gives
Equation (0619) of the Stacks project: the `Z`-derivations of `𝒪_Y` with values in `a_*C` are
exactly the maps `a^*Ω_{Y/Z} ⟶ C`, with `D = d_{Y/Z} ∘ θ`.

## Main definitions

* `AlgebraicGeometry.Space.differentialsHomEquiv` reads the universal property of the sheaf of
  differentials of Stacks 04CT as a bijection: morphisms `Ω_{X/Y} ⟶ F` are the `Y`-derivations
  with values in `F`.
* `AlgebraicGeometry.Space.derivationDirectImageEquiv` is **Equation (0619)**: the bijection
  between `𝒪_X`-linear maps `a^*Ω_{Y/Z} ⟶ C` and `Z`-derivations `𝒪_Y ⟶ a_*C`.

## Main results

* `AlgebraicGeometry.Space.differentialsHomEquiv_apply` and
  `AlgebraicGeometry.Space.derivationDirectImageEquiv_apply`: both bijections are given by
  composing with the universal derivation, so the derivation attached to `θ` really is
  `d_{Y/Z} ∘ θ`.

## Implementation notes

The universal property `AlgebraicGeometry.Space.universalDerivation_isUniversal` is stated as a
`∃!`, which is exactly the assertion that postcomposition with the universal derivation is
bijective; `differentialsHomEquiv` is `Equiv.ofBijective` applied to that, so the forward
direction of both bijections is literally postcomposition and the two `_apply` lemmas hold by
`rfl`.

The statement is general in the target module `C`: the source introduces Equation (0619) for
the conormal sheaf `C = 𝒞_{X/X'}` of a first order thickening and for a derivation produced by
Stacks 0618, but neither the thickening nor the provenance of the derivation is used, and the
consumers of the equation (Stacks 04D0, 061C) need the bijection at a general module in order
to run it in both directions.

## References

* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials and its universal derivation.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction
  `a^* ⊣ a_*` on sheaves of modules.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- Postcomposition with the universal `Y`-derivation is a bijection from the morphisms
`Ω_{X/Y} ⟶ F` of `𝒪_X`-modules onto the `Y`-derivations with values in `F`.  This is the
universal property of Stacks 04CT read as a bijection. -/
theorem bijective_universalDerivation_postcomp (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    Function.Bijective
      (fun g : sheafOfDifferentials B S hS f ⟶ F ↦
        (universalDerivation B S hS f).postcomp g.val) :=
  (Function.bijective_iff_existsUnique _).2 (universalDerivation_isUniversal B S hS f F)

/-- The universal property of the sheaf of differentials of Stacks 04CT as a bijection:
an `𝒪_X`-linear map `Ω_{X/Y} ⟶ F` is the same thing as a `Y`-derivation of `𝒪_X` with values
in `F`, the correspondence being composition with `d_{X/Y}`. -/
def differentialsHomEquiv (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) :
    (sheafOfDifferentials B S hS f ⟶ F) ≃
      F.val.Derivation' (structureSharpInverseImage B S hS f).hom :=
  Equiv.ofBijective _ (bijective_universalDerivation_postcomp B S hS f F)

/-- `AlgebraicGeometry.Space.differentialsHomEquiv` sends a morphism out of the sheaf of
differentials to its composite with the universal derivation. -/
theorem differentialsHomEquiv_apply (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (g : sheafOfDifferentials B S hS f ⟶ F) :
    differentialsHomEquiv B S hS f F g = (universalDerivation B S hS f).postcomp g.val :=
  rfl

/-- **Stacks 0619.** For `a : X ⟶ Y`, `b : Y ⟶ Z` and an `𝒪_X`-module `C`, the `𝒪_X`-linear
maps `θ : a^*Ω_{Y/Z} ⟶ C` correspond bijectively to the `Z`-derivations `D : 𝒪_Y ⟶ a_*C`, by
`D = d_{Y/Z} ∘ θ` with `θ` transposed along the adjunction `a^* ⊣ a_*`. -/
@[stacks 0619 "the bijection `θ ↔ D = d_{Y/B} ∘ θ`, stated at a general target module"]
def derivationDirectImageEquiv (a : X ⟶ Y) (b : Y ⟶ Z)
    (C : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS b) ⟶ C) ≃
      ((modulePushforward B S hS a).obj C).val.Derivation'
        (structureSharpInverseImage B S hS b).hom :=
  ((modulePullbackAdjunction B S hS a).homEquiv _ _).trans
    (differentialsHomEquiv B S hS b ((modulePushforward B S hS a).obj C))

/-- **Equation (0619) itself.**  The derivation attached to `θ : a^*Ω_{Y/Z} ⟶ C` is the
universal derivation `d_{Y/Z}` followed by the transpose of `θ` along `a^* ⊣ a_*`. -/
@[stacks 0619 "the equation `D = d_{Y/B} ∘ θ`"]
theorem derivationDirectImageEquiv_apply (a : X ⟶ Y) (b : Y ⟶ Z)
    (C : Modules.{u, u} B S hS X.1 X.2)
    (θ : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS b) ⟶ C) :
    derivationDirectImageEquiv B S hS a b C θ =
      (universalDerivation B S hS b).postcomp
        (((modulePullbackAdjunction B S hS a).homEquiv _ _) θ).val :=
  rfl

end AlgebraicGeometry.Space

end
