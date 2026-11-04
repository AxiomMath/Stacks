module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.TwistedFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.AmpleConsequences
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.CoherentFiniteness
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherent sheaves on `Proj` of a Noetherian graded ring

[Stacks, Tag 0B5Q]. Let `A` be a Noetherian graded ring and `X = Proj A`. Then `X` is a Noetherian
scheme, and for a coherent `𝒪_X`-module `ℱ`:

1. there are `r ≥ 0`, integers `d₁, …, d_r` and a surjection `⨁_j 𝒪_X(d_j) ⟶ ℱ`;
2. `Hᵖ(X, ℱ)` is a finite `A₀`-module for every `p`;
3. for `p > 0` the cohomology `Hᵖ(X, ℱ(d))` vanishes for all `d` large enough;
4. for every `k ∈ ℤ` the graded `A`-module `⨁_{d ≥ k} H⁰(X, ℱ(d))` is a finite `A`-module.

## Main results

* `Stacks.AlgebraicGeometry.ProjNoetherian.proj_isNoetherian_and_coherent`: the whole of
  [Stacks, Tag 0B5Q]. Assertion (4) is
  `Stacks.AlgebraicGeometry.ProjCoherentII.moduleFinite_truncation_of_isCoherent`.

## References

* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistFunctor
open Stacks.AlgebraicGeometry.ProjTwistedSections
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProjNoetherian

variable {A : Type u} {σ : Type u} [CommRing A] [IsNoetherianRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Stacks Project, Tag 0B5Q.** Let `A` be a Noetherian graded ring and `X = Proj A`. Then `X`
is a Noetherian scheme, and every coherent `𝒪_X`-module `ℱ` satisfies the four assertions of the
lemma: `ℱ` is a quotient of a finite direct sum of twisting sheaves, each `Hᵖ(X, ℱ)` is a finite
`A₀`-module, the higher cohomology of the high twists vanishes, and each graded tail
`⨁_{n ≥ k} H⁰(X, ℱ(n))` is a finite `A`-module. -/
@[stacks 0B5Q]
theorem proj_isNoetherian_and_coherent :
    AlgebraicGeometry.IsNoetherian (AlgebraicGeometry.Proj 𝒜) ∧
      ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜), _root_.SheafOfModules.IsCoherent F →
        (∃ (r : ℕ) (dj : Fin r → ℤ)
            (b : Bicone fun j : Fin r => twistingSheaf 𝒜 (dj j)) (_ : b.IsBilimit)
            (φ : b.pt ⟶ F), Epi φ) ∧
          (∀ p : ℕ, Module.Finite (𝒜 0)
            ((ModuleCat.restrictScalars
              (Stacks.AlgebraicGeometry.GradedProperCohomology.specAlgebraRingHom (𝒜 0)
                (AlgebraicGeometry.Proj.toSpecZero 𝒜))).obj
              (Stacks.AlgebraicGeometry.GradedProperCohomology.cohomologyOf
                (AlgebraicGeometry.Proj 𝒜) p F))) ∧
          (∀ p : ℕ, 0 < p → ∃ e₀ : ℤ, ∀ e : ℤ, e₀ ≤ e →
            IsZero (Hgroup (projRingSheaf 𝒜) ⊤ p (twistSheafOfModules 𝒜 F e))) ∧
          (∀ k : ℤ,
            letI := (ProjTwistedSections.twistedGlobalSectionsModule 𝒜 F).moduleInst
            Module.Finite A
              (TwistedGlobalSectionsModule.truncation 𝒜 F
                (ProjTwistedSections.twistedGlobalSectionsModule 𝒜 F) k)) :=
  ⟨Stacks.AlgebraicGeometry.Proj.isNoetherian_proj 𝒜, fun F hF =>
    ⟨hasTwistQuotients 𝒜 F hF,
      fun p => moduleFinite_cohomology 𝒜 F hF p,
      fun p hp => exists_isZero_hgroup_twist_of_isCoherent 𝒜 p hp F hF,
      fun k =>
        Stacks.AlgebraicGeometry.ProjCoherentII.moduleFinite_truncation_of_isCoherent 𝒜 F hF k⟩⟩

end Stacks.AlgebraicGeometry.ProjNoetherian

end
