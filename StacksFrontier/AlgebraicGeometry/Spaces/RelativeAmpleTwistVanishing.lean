module

public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleAffineTarget

/-!
# Relative ampleness over a Noetherian ring and cohomology

Let `R` be a Noetherian ring, `X` an algebraic space over `R` whose structure morphism
`f : X → Spec R` is proper, and `𝓛` an invertible `𝒪_X`-module.  Stacks 0D38 asserts that `𝓛`
is ample on `X/R` in the sense of Stacks 0D31 if and only if for every coherent `𝒪_X`-module
`𝓕` there is an `n₀ ≥ 0` with `H ᵖ(X, 𝓕 ⊗ 𝓛^{⊗ n}) = 0` for all `n ≥ n₀` and all `p > 0`.

Over the affine base `Spec R`, relative ampleness is ampleness on the scheme `X` then is
(`AlgebraicGeometry.Space.isRelativelyAmple_iff_exists_isAmple_of_isAffine`, from Stacks 0D32
and 01VK).  Given that, (1) ⟹ (2) is Serre's vanishing theorem on the scheme, Stacks 0B5T, read
through the comparison of étale and Zariski cohomology
(`AlgebraicGeometry.Space.exists_isZero_rightDerived_twistStep_of_isAmple`), and (2) ⟹ (1) is
Stacks 0D2W
(`AlgebraicGeometry.Space.exists_isAmple_of_forall_isCoherent_isZero_rightDerived_one_twistStep`),
`X` being Noetherian as it is proper over a Noetherian affine scheme.

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_iff_forall_isCoherent_exists_isZero_rightDerived`:
  **Stacks 0D38.**

## Implementation notes

The ring `R` is an affine object `V` of the site with `Γ(V, 𝒪_V) = R` Noetherian, and `X → Spec R`
is a proper morphism `f : X ⟶ h_V`, as in Stacks 0GFA
(`AlgebraicGeometry.Space.tfae_isAmple_of_isProper_toAffine`).  The twist `𝓕 ⊗ 𝓛^{⊗ n}` is
`AlgebraicGeometry.Space.twistStep`, and cohomology is that of `𝒪_X`-modules on the small étale
site.

## References

* [Stacks Project, Tag 0D38](https://stacks.math.columbia.edu/tag/0D38)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance 5000] SheafOfModules.instAbelian

/-- **Stacks 0D38.**  Let `R` be a Noetherian ring — here an affine object `V` of the site with
`Γ(V, 𝒪_V) = R` Noetherian — let `X` be an algebraic space over `R` whose structure morphism
`f : X ⟶ h_V` is proper, and let `𝓛` be an invertible `𝒪_X`-module.  Then `𝓛` is ample on `X/R`
(Stacks 0D31) if and only if for every coherent `𝒪_X`-module `𝓕` there is an `n₀ ≥ 0` with
`H ᵖ(X, 𝓕 ⊗ 𝓛^{⊗ n}) = 0` for all `n ≥ n₀` and all `p > 0`. -/
@[stacks 0D38]
theorem isRelativelyAmple_iff_forall_isCoherent_exists_isZero_rightDerived
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L] :
    have := enoughInjectives_modules B S hS X.1 X.2
    IsRelativelyAmple B S hS f L ↔
      ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
          IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived p).obj
              (twistStep B S hS X.1 X.2 L n F)) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  rw [isRelativelyAmple_iff_exists_isAmple_of_isAffine V f L hL]
  refine ⟨fun ⟨U, eX, _, hamp⟩ F hF =>
    exists_isZero_rightDerived_twistStep_of_isAmple V f hf L U eX hamp F hF, fun h => ?_⟩
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    isLocallyNoetherian_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom
  refine exists_isAmple_of_forall_isCoherent_isZero_rightDerived_one_twistStep
    B.contains_terminal X (isNoetherian_of_isProper_toAffine B S hS V inferInstance f hf) L
    fun F hF => ?_
  obtain ⟨n₀, hn₀⟩ := h F hF
  exact ⟨n₀ + 1, by omega, hn₀ (n₀ + 1) (by omega) 1 one_pos⟩

end AlgebraicGeometry.Space

end
