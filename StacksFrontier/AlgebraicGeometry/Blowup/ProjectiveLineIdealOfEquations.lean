module

public import StacksFrontier.AlgebraicGeometry.ProjSaturation.QuotientComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveLineReesRelation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The homogeneous ideal of equations of the blowup inside the projective line

Let `A` be a regular local ring of dimension two and let `x₀, x₁` be a minimal generating pair of
its maximal ideal `𝔪`. The blowup of `Spec A` in `𝔪` is a closed subscheme of the projective line
`𝐏¹_A = Proj A[T₀, T₁]` via `Stacks.Blowup.blowUpSpecToProjSpace`. Its homogeneous ideal of
equations, `AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme` (Tag 0BXK), is the
single relation `(x₁T₀ - x₀T₁)`.

The kernel of the graded presentation `A[T₀, T₁] ⟶ ⨁ₙ 𝔪ⁿ` is `(x₁T₀ - x₀T₁)`
(`Stacks.Blowup.ker_reesPresentation_maximalIdeal_eq_span_relation`), and this ideal is saturated
(`Stacks.Blowup.mem_span_relation_maximalIdeal_of_forall_homogeneous_mul_mem`). The ideal of
equations is therefore that kernel, by Tag 01N0 part (3) in the form
`AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme_map_eq_of_ker_eq_of_saturated`.

## Main results

* `Stacks.Blowup.idealOfClosedSubscheme_blowUpSpecToProjSpace_maximalIdeal_eq_span_relation`:
  **the ideal of equations of the blowup inside `𝐏¹_A` is `(x₁T₀ - x₀T₁)`.**

## Implementation notes

`Stacks.Blowup.blowUpSpecToProjSpace` is by definition `AlgebraicGeometry.Proj.map` of the Rees
presentation, but the closed-immersion instance available for it,
`Stacks.Blowup.isClosedImmersion_blowUpSpecToProjSpace`, is phrased at the `blowUpSpecToProjSpace`
spelling and instance search does not unfold the definition to reach it. One `haveI` supplies the
instance at the `Proj.map` spelling, which is harmless because
`AlgebraicGeometry.IsClosedImmersion` is a `Prop`.

No `@[stacks]` attribute is attached: this is a special case of the results tagged 01N0 and 0BXK.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj MvPolynomial IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Blowup

universe u

/-- **The homogeneous ideal of equations of the blowup of a regular local surface inside the
projective line is the single relation `x₁T₀ - x₀T₁`.** For `A` regular local of dimension two and
`x₀, x₁` a minimal generating pair of its maximal ideal, the closed subscheme
`Bl_𝔪 Spec A ⊆ 𝐏¹_A = Proj A[T₀, T₁]` is cut out by that one equation of degree one. -/
@[sga "6 VII 3.5" "special case"]
theorem idealOfClosedSubscheme_blowUpSpecToProjSpace_maximalIdeal_eq_span_relation
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    (x : Fin 2 → A) (hx : ∀ i, x i ∈ maximalIdeal A)
    (hspan : maximalIdeal A = Ideal.span (Set.range x)) :
    idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 2) A)
        (blowUpSpecToProjSpace (maximalIdeal A) x hx hspan) =
      Ideal.span {(C (x 1) * X 0 - C (x 0) * X 1 : MvPolynomial (Fin 2) A)} := by
  have : IsClosedImmersion (AlgebraicGeometry.Proj.map
      (reesPresentation (maximalIdeal A) x hx)
      (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
        (surjective_reesPresentation (maximalIdeal A) x hx hspan))) :=
    isClosedImmersion_blowUpSpecToProjSpace (maximalIdeal A) x hx hspan
  exact idealOfClosedSubscheme_map_eq_of_ker_eq_of_saturated _ (reesGrading (maximalIdeal A))
    (reesPresentation (maximalIdeal A) x hx)
    (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
      (surjective_reesPresentation (maximalIdeal A) x hx hspan))
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin 2) A) _
    (ker_reesPresentation_maximalIdeal_eq_span_relation A hdim x hx hspan)
    (fun _ ⟨_, h⟩ =>
      mem_span_relation_maximalIdeal_of_forall_homogeneous_mul_mem A hdim x hspan h)

end Stacks.Blowup

end
