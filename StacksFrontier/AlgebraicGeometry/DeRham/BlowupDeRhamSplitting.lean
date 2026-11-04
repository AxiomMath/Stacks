module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupCentreSectionGluing
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupRetractionModels
import StacksCore.Tactic.StacksAttribute

/-!
# The splitting of the de Rham complex along a blowing up with smooth centre

Let `f : X ⟶ S` be smooth, `i : Z ⟶ X` a closed immersion with `Z` smooth over `S`, and
`b : X' ⟶ X` the blowing up of `X` along `Z`. If `Z` has positive codimension in `X` at every
point, the canonical map `Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` has a retraction in
`D(X, (X ⟶ S)⁻¹𝒪_S)` ([Stacks, Tag 0FUW]).

The hypothesis is used in the form that `Z` contains no nonempty open subset of `X`, which is
implied by positive codimension at every point (a point of `Z` with a neighbourhood in `X`
contained in `Z` is a point at which `Z` has codimension `0`).

## Main results

* `Stacks.DeRham.BlowupTriangle.exists_retraction_toBlowUp`: [Stacks, Tag 0FUW].

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage

universe u w

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham.BlowupTriangle

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- **[Stacks, Tag 0FUW]: the de Rham complex splits off along a blowing up with smooth centre.**
Let `f : X ⟶ S` be smooth, `i : Z ⟶ X` a closed immersion with `Z` smooth over `S`, and
`b : X' ⟶ X` the blowing up of `X` along `Z`. If `Z` contains no nonempty open subset of `X` (in
particular, if `Z` has positive codimension in `X` at every point), the canonical map
`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` has a retraction in `D(X, (X ⟶ S)⁻¹𝒪_S)`, for any models of the
derived categories. -/
@[stacks 0FUW "f : X -> S smooth, i : Z -> X a closed immersion with Z smooth over S, \
b : X' -> X the blowing up along Z; if Z has positive codimension in X at every point (used in \
the weaker form that Z contains no nonempty open subset of X), then \
Omega_{X/S} -> Rb_*Omega_{X'/S} has a splitting in D(X, (X -> S)^{-1}O_S), for any models"]
theorem exists_retraction_toBlowUp [Smooth f] [Smooth (i ≫ f)]
    [HasDerivedCategory.{w} (ModuleSheaves (inverseImageBase f))]
    [HasDerivedCategory.{w} (ModuleSheaves (inverseImageBase (blowupMap i ≫ f)))]
    (hint : interior (Set.range i.base) = ∅) :
    ∃ r : blowUpDeRham f i ⟶ deRham f, toBlowUp f i ≫ r = 𝟙 _ :=
  exists_retraction_toBlowUp_of_standard f i (exists_retraction_toBlowUp_standard f i hint)

end Stacks.DeRham.BlowupTriangle

end
