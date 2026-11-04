module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChangeDerivation
import StacksCore.Tactic.StacksAttribute

/-!
# Derivations into a direct image and maps out of the pulled back differentials, for schemes

Let `a : X ⟶ Y` and `b : Y ⟶ Z` be morphisms of schemes and let `C` be a sheaf of
`𝒪_X`-modules.  A `Z`-derivation `D : 𝒪_Y ⟶ a_*C` factors through the universal
`Z`-derivation `d_{Y/Z}` by a unique `𝒪_Y`-linear map `θ : Ω_{Y/Z} ⟶ a_*C`, and by the
adjunction `a^* ⊣ a_*` such a `θ` is the same thing as an `𝒪_X`-linear map
`θ : a^*Ω_{Y/Z} ⟶ C`.  Composing the two bijections gives Equation (04BV) of the Stacks
project: the `Z`-derivations of `𝒪_Y` with values in `a_*C` are exactly the maps
`a^*Ω_{Y/Z} ⟶ C`, with `D = d_{Y/Z} ∘ θ`.

This is the Zariski twin of
`StacksFrontier/AlgebraicGeometry/Spaces/DerivationsIntoDirectImage.lean`, which carries the same
equation for algebraic spaces on the small étale site as
`AlgebraicGeometry.Space.derivationDirectImageEquiv`, registered there under the
algebraic-spaces spelling of the equation, [Stacks Project, Tag 0619].

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.derivationDirectImageEquiv` is **Equation (04BV)**: the
  bijection between `𝒪_X`-linear maps `a^*Ω_{Y/Z} ⟶ C` and `Z`-derivations `𝒪_Y ⟶ a_*C`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.derivationDirectImageEquiv_apply`: the bijection is given by
  composing with the universal derivation, so the derivation attached to `θ` really is
  `d_{Y/Z} ∘ θ`.

## Implementation notes

Both halves are already available at scheme level, so the equation is their composite.  The
universal property of `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` is
`AlgebraicGeometry.Scheme.Hom.bijective_universalRelativeDerivation_postcomp`, whose forward
direction is literally postcomposition with the universal derivation; the adjunction is
Mathlib's `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`.  Since
`Equiv.ofBijective` and `Equiv.trans` both compute, the `_apply` lemma holds by `rfl`.

The statement is general in the target module `C`: the source introduces the equation for the
conormal sheaf `C = 𝒞_{X/X'}` of a first order thickening and for a derivation produced by
Lemma 37.9.1, but neither the thickening nor the provenance of the derivation is used, and
reading the equation in both directions needs the bijection at a general module.

## References

* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM), the sheaf of
  differentials and its universal derivation.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the same equation in
  the algebraic-spaces chapter.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}}

/-- **Equation (04BV).**  For `a : X ⟶ Y`, `b : Y ⟶ Z` morphisms of schemes and an
`𝒪_X`-module `C`, the `𝒪_X`-linear maps `θ : a^*Ω_{Y/Z} ⟶ C` correspond bijectively to the
`Z`-derivations `D : 𝒪_Y ⟶ a_*C`, by `D = d_{Y/Z} ∘ θ` with `θ` transposed along the
adjunction `a^* ⊣ a_*`. -/
@[stacks 04BV "the bijection `θ ↔ D = d_{Y/S} ∘ θ` at scheme level on the Zariski site, stated \
at a general target module"]
def derivationDirectImageEquiv (a : X ⟶ Y) (b : Y ⟶ Z) (C : X.Modules) :
    ((Scheme.Modules.pullback a).obj (relativeDifferentials b) ⟶ C) ≃
      SheafOfModules.SheafDerivation (inverseImageStructureMap b)
        ((Scheme.Modules.pushforward a).obj C) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv _ _).trans
    (Equiv.ofBijective _ (bijective_universalRelativeDerivation_postcomp b
      ((Scheme.Modules.pushforward a).obj C)))

/-- **Equation (04BV) itself.**  The derivation attached to `θ : a^*Ω_{Y/Z} ⟶ C` is the
universal derivation `d_{Y/Z}` followed by the transpose of `θ` along `a^* ⊣ a_*`. -/
@[stacks 04BV "the equation `D = d_{Y/S} ∘ θ` at scheme level on the Zariski site"]
theorem derivationDirectImageEquiv_apply (a : X ⟶ Y) (b : Y ⟶ Z) (C : X.Modules)
    (θ : (Scheme.Modules.pullback a).obj (relativeDifferentials b) ⟶ C) :
    derivationDirectImageEquiv a b C θ =
      (universalRelativeDerivation b).postcomp
        (((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
          (relativeDifferentials b) C) θ).val :=
  rfl

end AlgebraicGeometry.Scheme.Hom

end
