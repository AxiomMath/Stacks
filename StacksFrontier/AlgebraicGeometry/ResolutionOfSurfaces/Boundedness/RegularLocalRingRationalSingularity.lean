module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.FirstCohomologyModificationTransfer

/-!
# The argument of Tag 0B4Q over two of its inputs

The assembly of the source's argument for [Stacks, Tag 0B4Q] out of the pieces of the sibling module
`Boundedness.RegularLocalRing`: a modification `X ⟶ Spec(A)` with `X` normal is dominated by a
sequence of blowups at closed points, the vanishing of the first cohomology of the structure
sheaf holds along that whole sequence, and it descends from the dominating modification to `X`.

The statement lives here rather than next to its ingredients because the descent,
`AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_comp_eq`, is proved downstream of
`Boundedness.RegularLocalRing`.

## Main results

* `AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_unconditional`: the
  source's argument over its two remaining cited inputs. The complete statement of
  [Stacks, Tag 0B4Q], with nothing assumed, is
  `AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`.

## Implementation notes

Two hypotheses of the source's proof are carried rather than discharged here; they are
`dominate` and `blowUpStep`, documented in the module docstring of
`Boundedness.RegularLocalRing`, where they were carried alongside a third, `transfer`.

`transfer` was the injectivity half of the first conclusion of [Stacks, Tag 0AXF], in the form in
which the source uses it: the vanishing of the first cohomology passes from a dominating normal
modification back to the one it dominates. It is no longer carried — it is
`AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_comp_eq` of
`Boundedness.FirstCohomologyModificationTransfer`, proved there from `q_*𝒪_Z = 𝒪_Y` for a
modification of a normal integral scheme ([Stacks, Tag 0AY8]) and the unconditional injectivity
of the first Leray edge map ([Stacks, Tag 01F2]).

The `blowUpStep` hypothesis refers to the right-hand exactness of the same sequence of
[Stacks, Tag 0AXF], and remains carried by this declaration. The library proves the survival of
the vanishing across such a blowup as
`AlgebraicGeometry.isZeroFirstStructureSheafCohomology_blowUp_of_isRegularLocalRing`, and
`dominate` is replaced by [Stacks, Tag 0BBT] in the complete statement
`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`.

## References

* [Stacks Project, Tag 0B4Q](https://stacks.math.columbia.edu/tag/0B4Q)
* [Stacks Project, Tag 0AHI](https://stacks.math.columbia.edu/tag/0AHI)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0567](https://stacks.math.columbia.edu/tag/0567)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ResolutionOfSurfaces

universe u

namespace AlgebraicGeometry

/-- **The argument of [Stacks, Tag 0B4Q] over two of its inputs.** A Nagata regular local ring
`A` of dimension two defines a rational singularity, once the two inputs below are given. The
complete statement is
`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`.

Two inputs of the source's proof are carried as hypotheses. `dominate` is [Stacks, Tag 0AHI],
that every such modification is dominated by a sequence of blowups at closed points over the
closed point of `Spec(A)`, together with the regularity of the members of that sequence
([Stacks, Tag 0AGR]) and their consequent normality ([Stacks, Tag 0567]). `blowUpStep` is the
survival of the vanishing across a single blowup at a closed point, which the source gets from
[Stacks, Tag 0AGS] and the right-hand exactness of the sequence of [Stacks, Tag 0AXF].

What is proved is the rest: the vanishing at the start of the sequence, its propagation along
the whole sequence, and the descent of the vanishing from the dominating sequence to the given
modification — the last being the injectivity half of [Stacks, Tag 0AXF], which the source's
proof also uses and which this development now has.

Cf. Stacks Tag 0B4Q; not registered because it carries the hypotheses `dominate` (Stacks Tag 0AHI)
and `blowUpStep` (Stacks Tag 0AGS with the right-hand exactness of Stacks Tag 0AXF). -/
public theorem definesRationalSingularity_of_isRegularLocalRing_unconditional (A : Type u)
    [CommRing A] [IsDomain A] [IsRegularLocalRing A] [IsNagataRing A] (_hdim : ringKrullDim A = 2)
    (dominate : ∀ (X : Scheme.{u}), IsNormal X → ∀ f : X ⟶ Spec (.of A), IsModification f →
      ∃ (Y : Scheme.{u}) (p : Y ⟶ Spec (.of A)) (g : Y ⟶ X),
        PointBlowupChain (Spec (.of A)) {IsLocalRing.closedPoint A} Y p ∧
          IsNormal Y ∧ IsModification p ∧ g ≫ f = p)
    (blowUpStep : ∀ (W : Scheme.{u}) (h : W ⟶ Spec (.of A)),
      PointBlowupChain (Spec (.of A)) {IsLocalRing.closedPoint A} W h →
      ∀ (w : W) (hw : IsClosed ({w} : Set W)),
        FirstStructureSheafCohomologyVanishes W →
        FirstStructureSheafCohomologyVanishes
          (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))) :
    DefinesRationalSingularity A := by
  intro X hX f hf
  obtain ⟨Y, p, g, hchain, hYnormal, hpmod, hgp⟩ := dominate X hX f hf
  exact firstStructureSheafCohomologyVanishes_of_comp_eq f p g hX hf hpmod hgp
    (firstStructureSheafCohomologyVanishes_of_pointBlowupChain A blowUpStep hchain)

end AlgebraicGeometry

end
