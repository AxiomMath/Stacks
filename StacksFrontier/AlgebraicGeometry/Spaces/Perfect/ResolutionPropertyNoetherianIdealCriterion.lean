module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowPushforwardProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDescentIdealQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertySurjection

/-!
# The resolution property of a Noetherian algebraic space from the ideal of the situation

In the situation of Stacks 0GUY — a quasi-compact and quasi-separated algebraic space `X` over a
scheme `S`, an affine surjective étale chart `φ : V → X` factored as an open immersion
`j : V → Y` followed by a finite morphism `π : Y → X`, and a finite type quasi-coherent sheaf of
ideals `ℐ ⊆ 𝒪_Y` cutting out the complement of `j(V)` — Stacks 0GV0 asserts, for `X` Noetherian,
that `X` has the resolution property **if and only if** `π_*ℐ` is the quotient of a finite
locally free `𝒪_X`-module.

## Main results

* `AlgebraicGeometry.Space.hasResolutionProperty_of_exists_epi_modulePushforwardIdeal`: the
  converse direction.  A surjection `ℰ ⟶ π_*ℐ` from a finite locally free `ℰ` propagates to
  surjections onto every `π_*(ℐⁿ)`, `n ≥ 1`, and Stacks 0GUZ surjects a finite direct sum of
  those onto any coherent module.
* `AlgebraicGeometry.Space.hasResolutionProperty_iff_exists_epi_modulePushforwardIdeal`:
  **Stacks 0GV0**, the equivalence.

## Implementation notes

Stacks 0GUZ allows exponents `n_i = 0`, for which `π_*(ℐ⁰) = π_*𝒪_Y` is not known to be a
quotient of a finite locally free module; the exponents are taken at least `1` by the form of
Stacks 0GUZ with a lower bound on the exponents,
`AlgebraicGeometry.Space.exists_epi_biproduct_idealSheafPowPushforward_of_le`.

## References

* [Stacks Project, Tag 0GV0](https://stacks.math.columbia.edu/tag/0GV0), Lemma 76.56.3.
* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ), Lemma 76.56.2.
* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY), Situation 76.56.1.
* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS), the resolution
  property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

variable (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- **Stacks 0GV0, the direction towards the resolution property.**  In the situation of
Stacks 0GUY with `X` Noetherian, if `π_*ℐ` is the quotient of a finite locally free
`𝒪_X`-module, then `X` has the resolution property. -/
theorem hasResolutionProperty_of_exists_epi_modulePushforwardIdeal
    (hX : IsNoetherian B S hS hZ X.1)
    (h : ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ modulePushforwardIdeal B S hS hZ X hqc hqs D), Epi p) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 := by
  have hpow := exists_isFiniteLocallyFreeOnSite_epi_idealSheafPowPushforward_of_one B S hS
    (D.piHom B S hS hZ X hqc hqs) D.isFinite_π.isAffineHom D.I D.isFiniteTypeQuasicoherent_I.1 h
  refine (hasResolutionProperty_iff B S hS X.1 X.2).2 fun M _ => ?_
  have : Fact (HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) := ⟨hX.2.2⟩
  have hM : IsCoherent B S hS X.1 X.2 M.obj :=
    (isCoherent_iff_isCoherentOnSite B S hS X.1 X.2 M.obj).2
      (isCoherentOnSite_of_isCartesian_of_isLocallyNoetherian B S hS X.1 X.2 M.obj
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 M.obj M.property)
        (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite M.obj ‹_›))
  obtain ⟨r, n, hn, hB, σ, hσ⟩ :=
    exists_epi_biproduct_idealSheafPowPushforward_of_le B S hS hZ X hqc hqs D hX M.obj hM 1
  exact exists_isFiniteLocallyFreeOnSite_epi_of_epi_biproduct B S hS X
    (fun i => idealSheafPowPushforward B S hS (D.piHom B S hS hZ X hqc hqs) D.I (n i))
    (fun i => hpow (n i) (hn i)) σ hσ

/-- Let `X` be a quasi-compact and quasi-separated algebraic space, `φ : V ⟶ X` a surjective
étale morphism from an affine scheme factored as an open immersion `j : V ⟶ Y` followed by a
finite `π : Y ⟶ X`, and `ℐ ⊆ 𝒪_Y` a finite type quasi-coherent sheaf of ideals with
`V(ℐ) = Y ∖ j(V)`, and assume `X` is Noetherian. Then `X` has the resolution property if and only
if `π_*ℐ` is the quotient of a finite locally free `𝒪_X`-module. -/
@[stacks 0GV0 "the whole statement, both directions"]
theorem hasResolutionProperty_iff_exists_epi_modulePushforwardIdeal
    (hX : IsNoetherian B S hS hZ X.1) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 ↔
      ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
        (p : E ⟶ modulePushforwardIdeal B S hS hZ X hqc hqs D), Epi p :=
  ⟨exists_isFiniteLocallyFreeOnSite_epi_modulePushforwardIdeal B S hS hZ X hqc hqs D hX,
    hasResolutionProperty_of_exists_epi_modulePushforwardIdeal B S hS hZ X hqc hqs D hX⟩

end AlgebraicGeometry.Space

end
