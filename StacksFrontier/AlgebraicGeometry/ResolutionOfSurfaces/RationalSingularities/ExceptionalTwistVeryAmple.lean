module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.AffineProjective
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealTwist
public import StacksFrontier.AlgebraicGeometry.VeryAmpleProjectiveSpace.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Very ampleness of the first twist on the exceptional curve

Let `(A, 𝔪, κ)` be a Noetherian local ring, let `X` be the blowup of `Spec(A)` in `𝔪` and let
`E ⊆ X` be its exceptional divisor. This file proves clause (2) of [Stacks, Tag 0B63]: `𝒪_E(1)`
is very ample for the structure morphism `E ⟶ Spec(κ)`.

The source's proof is "very ampleness of `𝒪_X(1)` is built into the construction, so restricting
it to the special fibre keeps it very ample", and that is the shape of the argument here, with the
restriction performed before the change of base rather than after:

* over the affine base `Spec(A)` the blowup immerses into a projective space over `Spec(A)`,
  carrying the hyperplane sheaf to `𝒪_X(1)`
  (`AlgebraicGeometry.exists_isImmersion_blowUp_projectiveSpaceOver`, part (1) of
  [Stacks, Tag 02NS] over an affine base);
* composing with the closed immersion `E ⟶ X` gives an immersion of `E` into the same projective
  space, over `Spec(A)`, carrying the hyperplane sheaf to `𝒪_E(1)`; and the composite with the
  structure morphism to `Spec(A)` factors through the closed point by
  `AlgebraicGeometry.exceptionalDivisorToCentre_comp`;
* `Stacks.VeryAmpleProjectiveSpace.isRelativelyVeryAmple_of_immersion_over` then reads that as
  relative very ampleness over `Spec(κ)`: projective space is a fibre product over the terminal
  scheme, so the morphism to projective space over `Spec(κ)` with the same projection to the
  integral model exists with nothing to check, and [Stacks, Tag 01OE] over the affine base
  `Spec(κ)` identifies that projective space with a projective bundle.

## Main results

* `AlgebraicGeometry.isRelativelyVeryAmple_curveTwistSheaf_one`: **clause (2) of
  [Stacks, Tag 0B63]** — `𝒪_E(1)` is very ample relative to `E ⟶ Spec(κ)`, in the sense of
  [Stacks, Tag 01VM].

## Implementation notes

The hypotheses are those of clause (1)'s properness registration
`AlgebraicGeometry.isProper_exceptionalDivisorToCentre_residuePoint`: a Noetherian local ring,
with neither the normality nor the rational-singularity hypothesis of Situation
[Stacks, Tag 0B4W]. Neither is used: what the clause expresses is a property of the blowup
construction, exactly as the source says.

The twist is `AlgebraicGeometry.BlowUpDualizing.curveTwistSheaf A 1`, the restriction of
`𝒪_X(1)` to `E` at the spelling clauses (3), (4) and (5) are stated in; the identification of
that restriction with the pullback of `AlgebraicGeometry.blowUpTwist` is
`AlgebraicGeometry.BlowUpDualizing.pullbackTwistSheafIso` together with
`AlgebraicGeometry.BlowUpDualizing.twistSheafOneIso`.

## References

* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample

universe u

namespace AlgebraicGeometry

open Stacks.Blowup BlowUpDualizing in
/-- **[Stacks, Tag 0B63] clause (2).** For a Noetherian local ring `(A, 𝔪, κ)`, with `X` the
blowup of `Spec(A)` in `𝔪` and `E ⊆ X` the exceptional divisor, the first twist `𝒪_E(1)` is very
ample for the structure morphism `E ⟶ Spec(κ)`.

Very ampleness is [Stacks, Tag 01VM],
`Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`: there are a quasi-coherent `𝒪_{Spec κ}`-module
`F` and an immersion `E ⟶ 𝐏(F)` over `Spec(κ)` pulling `𝒪_{𝐏(F)}(1)` back to `𝒪_E(1)`. -/
@[stacks 0B63 "clause (2): the first twist on the exceptional curve is very ample over the \
residue field"]
theorem isRelativelyVeryAmple_curveTwistSheaf_one (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple
      (exceptionalDivisorToCentre (residuePoint A)) (curveTwistSheaf A 1) := by
  have hNoeth : IsNoetherianRing Γ(Spec (.of A), (⊤ : (Spec (.of A)).Opens)) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (Spec (.of A))⟩
  obtain ⟨n, r, hr, hrbase, ⟨etw⟩⟩ :=
    exists_isImmersion_blowUp_projectiveSpaceOver (centre A)
      (Ideal.fg_of_isNoetherianRing _)
  have := hr
  have : IsImmersion (exceptionalImmersion A ≫ r) := inferInstance
  refine Stacks.VeryAmpleProjectiveSpace.isRelativelyVeryAmple_of_immersion_over n
    (residuePoint A) (exceptionalDivisorToCentre (residuePoint A)) (curveTwistSheaf A 1)
    (exceptionalImmersion A ≫ r) inferInstance ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => exceptionalImmersion A ≫ m) hrbase).trans
        (exceptionalDivisorToCentre_comp (residuePoint A)).symm)
  · exact (pullbackTwistSheafIso A 1).symm ≪≫
      (Scheme.Modules.pullback (exceptionalImmersion A)).mapIso
        ((twistSheafOneIso A) ≪≫ etw) ≪≫
      (Scheme.Modules.pullbackComp (exceptionalImmersion A) r).app _

end AlgebraicGeometry

end
