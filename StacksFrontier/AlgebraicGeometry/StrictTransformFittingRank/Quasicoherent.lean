module

public import StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.StrictTransformFittingRank.Basic

/-!
# The quasi-coherence hypothesis of the Fitting-blowup strict transform is discharged

`StacksFrontier/AlgebraicGeometry/StrictTransformFittingRank/Basic.lean` carries three named
hypotheses for its port of [Stacks, Tag 0CZQ], the third of which,
`Stacks.StrictTransformFittingRank.StrictTransformQuasicoherent`, asserts that the strict
transform of a finite type quasi-coherent module along the blowup of a Fitting ideal is
quasi-coherent. Its module docstring records that the subsheaf half is proved but that the input
it needs — retrocompactness of the complement of the inverse image of the exceptional divisor —
is supplied by nothing there.

It is supplied elsewhere: the exceptional ideal of a blowup is an effective Cartier divisor
([Stacks, Tag 02OS]), so the complement of its support is affine over the blowup
([Stacks, Tag 07ZT]) and in particular its inclusion is quasi-compact, which base-changes to the
inverse image. That chain is `Stacks.StrictTransform.isQuasicoherent_sheaf` together with
`Stacks.StrictTransform.quasiCompact_ι_compl_support_exceptionalIdeal`, and it is
unconditional. This file discharges the hypothesis from it.

## Main results

* `Stacks.StrictTransformFittingRank.strictTransformQuasicoherent`:
  `Stacks.StrictTransformFittingRank.StrictTransformQuasicoherent` holds.
* `Stacks.StrictTransformFittingRank.isFiniteLocallyFreeOfRank_strictTransform_fittingBlowUp'`:
  [Stacks, Tag 0CZQ] from the other two named hypotheses alone.

## Implementation notes

The two spellings of the strict transform of a module —
`Stacks.StrictTransformFittingRank.strictTransformSheaf`, the cokernel of
`(AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule _ _).ι`, and
`Stacks.StrictTransform.sheaf`, the cokernel of
`AlgebraicGeometry.Scheme.Modules.supportedSectionsι` — agree definitionally at the blowup of a
Fitting ideal, so the discharge is the one `exact`. The module docstring of
`StacksFrontier/AlgebraicGeometry/StrictTransform/Basic.lean` warns that the two are recorded over
syntactically different category instances; that affects what can be written in a *type*, not
whether a term of one is a term of the other.

No `@[stacks 0CZQ]` attribute is claimed below: the statement still carries two hypotheses the
tag does not.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
* [Stacks Project, Tag 07ZT](https://stacks.math.columbia.edu/tag/07ZT)
* [Stacks Project, Tag 0CZQ](https://stacks.math.columbia.edu/tag/0CZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.StrictTransformFittingRank

/-- **The third named hypothesis of the [Stacks, Tag 0CZQ] port holds.** The strict transform of
a finite type quasi-coherent module along the blowup of a Fitting ideal is quasi-coherent, with no
hypothesis: this is the instance `Stacks.StrictTransform.isQuasicoherent_sheaf` at the blowup,
whose retrocompactness input comes from the exceptional divisor being an effective Cartier
divisor. -/
theorem strictTransformQuasicoherent : StrictTransformQuasicoherent.{u} := by
  intro S F _ _ k
  exact Stacks.StrictTransform.isQuasicoherent_sheaf (𝟙 S)
    (AlgebraicGeometry.blowUpToBase (AlgebraicGeometry.fittingIdeal F (k : ℤ)))
    (AlgebraicGeometry.exceptionalIdeal (AlgebraicGeometry.fittingIdeal F (k : ℤ))) F

/-- **[Stacks, Tag 0CZQ] from two named hypotheses instead of three.** This is
`Stacks.StrictTransformFittingRank.isFiniteLocallyFreeOfRank_strictTransform_fittingBlowUp` with
its quasi-coherence hypothesis discharged by
`Stacks.StrictTransformFittingRank.strictTransformQuasicoherent`. What remains carried is
[Stacks, Tag 0C3G], the sheaf-level Fitting-ideal criterion, and [Stacks, Tag 0CZP], the
generation statement. -/
theorem isFiniteLocallyFreeOfRank_strictTransform_fittingBlowUp'
    (hcrit : FittingRankCriterion.{u}) (hgenz : StrictTransformGeneration.{u})
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (k : ℕ)
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback
          (Scheme.Opens.ι (AlgebraicGeometry.fittingIdeal F (k : ℤ)).support.compl)).obj F) k) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (strictTransformSheaf (𝟙 S) (AlgebraicGeometry.fittingIdeal F (k : ℤ)) F) k :=
  isFiniteLocallyFreeOfRank_strictTransform_fittingBlowUp hcrit hgenz
    strictTransformQuasicoherent.{u} F k h

end Stacks.StrictTransformFittingRank

end
