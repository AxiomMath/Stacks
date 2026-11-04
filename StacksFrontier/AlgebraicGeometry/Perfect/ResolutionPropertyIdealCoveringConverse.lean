module

public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyIdealCovering
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmpleFamilyIdealCovering
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyIdealCoveringSubstantial
public import StacksCore.Tactic.StacksAttribute

/-!
# The resolution property from a finite affine covering cut out by ideals

[Stacks, Tag 0F89].  Let `X` be a scheme with

1. a finite affine open covering `X = U 0 ∪ ⋯ ∪ U (m - 1)`, and
2. finite type quasi-coherent sheaves of ideals `I j ⊆ 𝒪_X` with `V(I j) = X ∖ U j`

(`AlgebraicGeometry.IsIdealAffineCovering`).  Then `X` has the resolution property if and only
if each `I j` is the quotient of a finite locally free `𝒪_X`-module.

## Main results

* `hasResolutionProperty_iff_forall_exists_epi_idealPow_of_isIdealAffineCovering`:
  **[Stacks, Tag 0F89]**, the equivalence.
* `AlgebraicGeometry.idealCoveringImpliesResolutionProperty`: the statement
  `AlgebraicGeometry.IdealCoveringImpliesResolutionProperty`, which [Stacks, Tag 0GMM] and
  [Stacks, Tag 0F8A] are carried with as a hypothesis, holds.

## Implementation notes

The two directions are in the library: the immediate one is
`AlgebraicGeometry.exists_isFiniteLocallyFree_epi_of_isIdealAffineCovering`, and the substantial
one, at the source's generality, is
`AlgebraicGeometry.hasResolutionProperty_of_isIdealAffineCovering`.  This file puts them together
into the equivalence the tag asserts.

## References

* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **[Stacks, Tag 0F89].** Let `X` be a scheme with
1. a finite affine open covering `X = U 0 ∪ ⋯ ∪ U (m - 1)`, and
2. finite type quasi-coherent sheaves of ideals `I j` with `V(I j) = X ∖ U j`.

Then `X` has the resolution property if and only if each `I j` is the quotient of a finite
locally free `𝒪_X`-module.

The forward direction is `exists_isFiniteLocallyFree_epi_of_isIdealAffineCovering`, the
converse `hasResolutionProperty_of_isIdealAffineCovering`. -/
@[stacks 0F89]
theorem hasResolutionProperty_iff_forall_exists_epi_idealPow_of_isIdealAffineCovering {m : ℕ}
    {U : Fin m → X.Opens} {I : Fin m → X.IdealSheafData} (h : IsIdealAffineCovering X U I) :
    HasResolutionProperty X ↔
      ∀ j, ∃ (E : X.Modules)
        (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
        (q : E ⟶ idealPow (I j) 1), Epi q :=
  ⟨fun _ j ↦ exists_isFiniteLocallyFree_epi_of_isIdealAffineCovering h j, fun hE ↦ by
    choose E hE q hq using hE
    exact hasResolutionProperty_of_isIdealAffineCovering h E hE q hq⟩

/-- **The substantial direction of [Stacks, Tag 0F89], for all schemes at once.** This is the
statement `IdealCoveringImpliesResolutionProperty` that
`AlgebraicGeometry.hasResolutionProperty_of_isAmpleFamily` ([Stacks, Tag 0GMM]) and
`AlgebraicGeometry.hasResolutionProperty_of_isRegular` ([Stacks, Tag 0F8A]) take as a
hypothesis. -/
theorem idealCoveringImpliesResolutionProperty : IdealCoveringImpliesResolutionProperty.{u} :=
  fun _ _ _ _ h hE ↦ (hasResolutionProperty_iff_forall_exists_epi_idealPow_of_isIdealAffineCovering
    h).2 hE

end AlgebraicGeometry
