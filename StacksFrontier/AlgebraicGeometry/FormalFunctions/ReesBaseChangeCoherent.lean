module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesComapLocallySurjective
public import StacksFrontier.AlgebraicGeometry.RelativeSpecQcohEquivalence.FiniteType
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# `F'` is coherent, and `h0897` is down to the `B`-linear comparison

[Stacks, Tag 0897]'s proof base-changes to `X' = Spec_X(⨁ₙ ℐⁿ)` and uses there a **coherent**
`𝒪_{X'}`-module `F'` with `π_* F' ≅ ⨁ₙ Mₙ`.  That module is
`Stacks.Cohomology.FormalFunctions.reesBaseChangeModule`, and
`Stacks.Cohomology.FormalFunctions.isQuasicoherent_reesBaseChangeModule` gave only its
quasi-coherence.  This file proves it is **coherent**, so that [Stacks, Tag 02O8]'s hypothesis
`h0897` loses the coherence hypothesis of
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_isCoherent` and is
left with the `B`-linear comparison `cmp` alone.

## Main results

* `Stacks.Cohomology.FormalFunctions.isFiniteType_reesBaseChangeModule`: **`F'` is of finite
  type.**
* `Stacks.Cohomology.FormalFunctions.isCoherent_reesBaseChangeModule`: **`F'` is coherent.**
* `Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_cmp`:
  **[Stacks, Tag 02O8]'s hypothesis `h0897` at one graded module, with everything of
  [Stacks, Tag 0897]'s base change discharged except the comparison `cmp`.**

## Implementation notes

The three steps between [Stacks, Tag 0897]'s finiteness hypothesis on `M` and coherence of `F'`
are now all in place:

* finite type of the total module `⨁ₙ Mₙ` over `⨁ₙ ℐⁿ` is
  `Stacks.Cohomology.FormalFunctions.isFiniteType_ungradedSheaf`;
* its transport across [Stacks, Tag 01SB] is
  `Stacks.AffineAlgebraEquivalence.isFiniteType_inverse_obj`, which rests on the `𝓐`-analogue of
  [Stacks, Tag 01PB] proved in
  `StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.AffineSections`;
* local Noetherianness of `X'` is
  `Stacks.Cohomology.FormalFunctions.isLocallyNoetherian_reesRelativeSpec`.

[Stacks, Tag 01XZ]
(`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType`)
then applies.

No `@[stacks]` attribute: [Stacks, Tag 0G7X] is still conditional, on `cmp`, and the tag gets no
site until that chain is unconditional.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.GradedProperCohomology

universe u

namespace Stacks.Cohomology.FormalFunctions

noncomputable section

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))
  (M : SheafOfModules.GradedModule.{u, u, u} (baseReesAlgebra I X))

/-- **`F'` is of finite type.**  Its direct image is the total module `⨁ₙ Mₙ`, of finite type
over `⨁ₙ ℐⁿ` by [Stacks, Tag 0897]'s own hypothesis on `M`, and finite type transports across
[Stacks, Tag 01SB]. -/
theorem isFiniteType_reesBaseChangeModule
    (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hft : M.IsFiniteType)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    (reesBaseChangeModule I X M hqc hneg).IsFiniteType :=
  isFiniteType_inverse_obj (Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom))
    (reesTotalQcoh I X M hqc hneg) (isFiniteType_ungradedSheaf I X M hft)

/-- **`F'` is coherent**: quasi-coherent and of finite type on the locally Noetherian scheme
`X'`, which is [Stacks, Tag 01XZ]. -/
theorem isCoherent_reesBaseChangeModule [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper X.hom)
    (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hft : M.IsFiniteType)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    (reesBaseChangeModule I X M hqc hneg).IsCoherent :=
  have : IsLocallyNoetherian (reesRelativeSpec I X).left :=
    isLocallyNoetherian_reesRelativeSpec I X hX
  have := isQuasicoherent_reesBaseChangeModule I X M hqc hneg
  have := isFiniteType_reesBaseChangeModule I X M hqc hft hneg
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

attribute [local instance] cohomologyGradedModule

/-- **[Stacks, Tag 02O8]'s hypothesis `h0897` at one graded module, with coherence of `F'`
discharged as well.**  The only hypothesis left beyond [Stacks, Tag 0897]'s own is `cmp`, the
`B`-linear comparison `⨁ₙ Hᵖ(X, Mₙ) ≃ₗ[B] Hᵖ(X', F')`. -/
theorem isCohomologyReesFiniteOfGradedModule_of_cmp [IsNoetherianRing A] (p : ℕ)
    (hX : AlgebraicGeometry.IsProper X.hom)
    (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hft : M.IsFiniteType)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules))
    (cmp :
      letI := gradedCohomologySumModuleRees I X M p hneg
      gradedCohomologySum M p ≃ₗ[↥(reesAlgebra I)]
        ↥((ModuleCat.restrictScalars (specAlgebraRingHom ↥(reesAlgebra I)
            (reesRelativeSpecToPullback I X (baseReesComapPullbackHom I X) ≫
              pullback.fst (reesSpecToBase I) X.hom))).obj
          (cohomologyOf (reesRelativeSpec I X).left p
            (reesBaseChangeModule I X M hqc hneg)))) :
    IsCohomologyReesFiniteOfGradedModule I X M p :=
  have := isCoherent_reesBaseChangeModule I X M hX hqc hft hneg
  isCohomologyReesFiniteOfGradedModule_of_isCoherent I X M p hX hqc hft hneg
    (reesBaseChangeModule I X M hqc hneg) cmp

end

end Stacks.Cohomology.FormalFunctions

end
