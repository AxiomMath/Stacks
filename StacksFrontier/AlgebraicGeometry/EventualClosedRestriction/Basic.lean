module

public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologicalCriterion
public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic

/-!
# Restriction to a closed subscheme is surjective on sections in all large twists

Let `X` be proper over a Noetherian ring `R`, let `𝓛` be an ample invertible `𝒪_X`-module and let
`i : Z ⟶ X` be a closed immersion with ideal sheaf `𝓘`. Then

`Γ(X, 𝓛^{⊗ n}) ⟶ Γ(Z, i^*(𝓛^{⊗ n}))`

is surjective for every `n ≫ 0`.

## Main results

* `AlgebraicGeometry.isCoherent_idealSheaf_of_isClosedImmersion`: the ideal sheaf of a closed
  immersion into a locally Noetherian scheme is coherent.
* `AlgebraicGeometry.exists_forall_surjective_pullbackGlobalSection_tensorPower`: for `X` proper
  over a Noetherian ring, `𝓛` ample and `i : Z ⟶ X` a closed immersion, the restriction map
  `Γ(X, 𝓛^{⊗ n}) ⟶ Γ(Z, i^*(𝓛^{⊗ n}))` is surjective for all sufficiently large `n`.

## Implementation notes

The ideal sheaf `𝓘` is quasi-coherent
(`Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf`), and a quasi-coherent
submodule of the coherent structure sheaf is coherent on a locally Noetherian scheme
(`Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono`, **[Stacks, Tag 01Y1]**). By
`AlgebraicGeometry.Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple`
(**[Stacks, Tag 0B5U]**) there is then an `n₀` with `H¹(X, 𝓘 ⊗ 𝓛^{⊗ n}) = 0` for all `n ≥ n₀`, and
`Stacks.AmpleSurjectiveThickening.surjective_pullbackGlobalSection_of_isZero_h1` turns each such
vanishing into surjectivity of the restriction map.

## References

* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- The ideal sheaf of a closed immersion `i : Z ⟶ X` into a locally Noetherian scheme `X` is
coherent. -/
public theorem isCoherent_idealSheaf_of_isClosedImmersion {X Z : Scheme.{u}}
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] :
    (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).IsCoherent := by
  have hunit : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hqc : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf i
  set j := SheafOfModules.unitToPushforwardObjUnit
    (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom) with hj
  have hmono : Mono (Limits.kernel.ι j) := inferInstance
  exact @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono X _
    (SheafOfModules.unit X.ringCatSheaf) _ hunit hqc (Limits.kernel.ι j) hmono

/-- Let `X` be proper over a Noetherian ring `R`, `𝓛` an ample invertible `𝒪_X`-module and
`i : Z ⟶ X` a closed immersion. Then there is `n₀` such that the restriction map
`Γ(X, 𝓛^{⊗ n}) ⟶ Γ(Z, i^*(𝓛^{⊗ n}))` is surjective for every `n ≥ n₀`. -/
public theorem exists_forall_surjective_pullbackGlobalSection_tensorPower {R : Type u} [CommRing R]
    [IsNoetherianRing R] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] (i : Z ⟶ X)
    [IsClosedImmersion i] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Function.Surjective
      (Stacks.NonvanishingPullback.pullbackGlobalSection i
        (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨n₀, hn₀⟩ := Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple L f hL
    (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)
    (isCoherent_idealSheaf_of_isClosedImmersion i)
  refine ⟨n₀, fun n hn => ?_⟩
  let : Stacks.Ample.IsInvertibleModule X (tensorPower X.presheaf X.ringCatSheaf.2 L (n : ℤ)) :=
    tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 L (n : ℤ)
  exact Stacks.AmpleSurjectiveThickening.surjective_pullbackGlobalSection_of_isZero_h1 i _
    (hn₀ n 1 hn Nat.one_pos)

end AlgebraicGeometry

end
