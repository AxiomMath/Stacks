module

public import StacksFrontier.AlgebraicGeometry.EulerCharVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# A regular local ring of dimension two defines a rational singularity

A ring `A` defines a rational singularity when `H¹(X, 𝒪_X) = 0` for every modification
`X ⟶ Spec(A)` with `X` normal. For a Nagata regular local ring of dimension two this holds, and
the argument is: any such `X` is dominated by the last term `Xₙ` of a sequence of blowups at
closed points over the closed point of `Spec(A)`; those `Xₙ` are regular, hence normal; the
first cohomology of `X` injects into that of `Xₙ`; and the first cohomology of `Xₙ` vanishes
because the structure sheaf has no higher direct images along a blowup at a closed point of a
regular two-dimensional scheme.

Of that argument this file proves the two ends — the vanishing at the base of the sequence, and
the propagation of the vanishing along the whole sequence from its propagation across one
blowup — over the three cited inputs. The library proves the complete statement, with nothing
assumed, as `AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`
(`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational`),
[Stacks, Tag 0B4Q].

## Main definitions

* `AlgebraicGeometry.FirstStructureSheafCohomologyVanishes` is `H¹(X, 𝒪_X) = 0`, written in the
  spelling that `AlgebraicGeometry.DefinesRationalSingularity` uses.

## Main results

* `AlgebraicGeometry.isNormalDomain_of_isRegularLocalRing`: a regular local ring is a normal
  domain, so it lies in the context in which the source introduces rational singularities.
* `AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_isAffine`: `H¹(X, 𝒪_X) = 0` for an
  affine scheme. This is Serre vanishing, and it is the start of the sequence of blowups.
* `AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_pointBlowupChain`: the vanishing
  holds along a whole sequence of blowups at closed points once it propagates across a single
  one.
* `AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing`: the source's argument
  over its three cited inputs.

## Implementation notes

`AlgebraicGeometry.DefinesRationalSingularity` is stated with Mathlib's
`CategoryTheory.Sheaf.H` of the abelian sheaf underlying `𝒪_X`, together with the `EnoughInjectives`
and `HasExt` instances that a category of abelian sheaves on a small site carries. The predicate
`FirstStructureSheafCohomologyVanishes` repeats that spelling at a fixed scheme, so that it is
the body of `DefinesRationalSingularity` and the two are interchangeable without comparison.

Serre vanishing is available in the same spelling as
`Stacks.Cohomology.FiniteCover.isZero_H'_of_isAffineOpen`, over an affine open of any scheme;
applied to the terminal open of an affine scheme and transported to global cohomology by
`Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top`, it gives the
vanishing at the start of the sequence. The abelian sheaf
`DefinesRationalSingularity` speaks about is `𝒪_X` composed with the two forgetful functors,
and the one Serre vanishing speaks about is the image of `SheafOfModules.unit` under
`SheafOfModules.toSheaf`; the two are the same sheaf.

Sequences of blowups at closed points are `Stacks.ResolutionOfSurfaces.PointBlowupChain`, an
inductive family over the composite morphism to the base, so the propagation of the vanishing
along a sequence is an induction over that family whose base case is the affine vanishing.

Three hypotheses of the source's proof are carried by
`definesRationalSingularity_of_isRegularLocalRing` rather than discharged; the notes below
describe them as this module stands. All three are discharged downstream, and the complete
statement of [Stacks, Tag 0B4Q] is
`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`: there
`dominate` is replaced by the domination of [Stacks, Tag 0BBT] through normalized blowups,
`transfer` is `AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_dominates`, and
`blowUpStep` is
`AlgebraicGeometry.isZeroFirstStructureSheafCohomology_blowUp_of_isRegularLocalRing`.

* `dominate` is [Stacks, Tag 0AHI], that a modification of a Noetherian scheme which is an
  isomorphism away from finitely many closed points with regular two-dimensional local rings is
  dominated by a sequence of blowups at closed points, together with the regularity of the
  members of that sequence ([Stacks, Tag 0AGR]) and their consequent normality
  ([Stacks, Tag 0567]). Tag 0AHI is not proved in this development: it rests on
  [Stacks, Tag 081T], available only conditionally, and on [Stacks, Tag 0AHH], available only
  granted the local splitting of [Stacks, Tag 0AGT]. Tag 0AGR is proved here for the blowup of
  the spectrum of a regular local ring of dimension two at its closed point, as
  `AlgebraicGeometry.isRegular_blowUp_maximalIdeal`, but not for an arbitrary scheme blown up at
  a closed point, which is what a sequence needs.
* `transfer` is the injectivity half of [Stacks, Tag 0AXF], in the form in which the source uses
  it: the vanishing of the first cohomology passes from a dominating normal modification back to
  the one it dominates. Tag 0AXF has two carriers in this development, both in the namespace
  `AlgebraicGeometry.SemistableReduction.TwoModifications`:
  `topologicalKrullDim_supp_rightDerived_one_pushforward_le_zero` and
  `nonempty_generatingSections_rightDerived_one_pushforward`. They are its two side conclusions
  about `R¹g_*𝒪_{X'}`; the short exact sequence itself, which is what is needed here, is not
  among them.
* `blowUpStep` is [Stacks, Tag 0AGS] combined with the same short exact sequence: the vanishing
  of the first cohomology survives one blowup at a closed point. The carrier of Tag 0AGS in this
  development, `AlgebraicGeometry.isZero_cohomology_of_two_le`, is its first clause, the
  vanishing in degrees at least two; the clause used here is the second,
  `H¹(X, 𝒪_X(n)) = 0` for `n ≥ -1`, which is not among them.

The hypothesis `[IsDomain A]` of the main theorem is implied by `[IsRegularLocalRing A]`; it is
listed because `DefinesRationalSingularity` is stated for a domain, and
`isNormalDomain_of_isRegularLocalRing` discharges it. The Nagata hypothesis and the dimension
are those of the source's statement: the source remarks that neither is needed for the argument
itself, the notion of a rational singularity having been introduced only for Nagata normal local
domains of dimension two. Here they are the hypotheses under which the carried inputs hold, and
the dimension is therefore named `_hdim`: it is what makes `dominate` and `blowUpStep` true, and
the assembly of those two with `transfer` does not refer to it again.

## References

* [Stacks Project, Tag 0B4Q](https://stacks.math.columbia.edu/tag/0B4Q)
* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
* [Stacks Project, Tag 0AHI](https://stacks.math.columbia.edu/tag/0AHI)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0567](https://stacks.math.columbia.edu/tag/0567)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ResolutionOfSurfaces

universe u

namespace AlgebraicGeometry

/-- A regular local ring is a normal domain: it is a domain, and it is integrally closed in its
fraction field because a regular ring is normal ([Stacks, Tag 0567]). -/
@[ega "0 17.1.3"]
theorem isNormalDomain_of_isRegularLocalRing (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsNormalDomain A :=
  ⟨IsRegularLocalRing.isDomain A, isIntegrallyClosed_of_isRegularLocalRing A⟩

/-- The vanishing `H¹(X, 𝒪_X) = 0` of the first cohomology of the structure sheaf of `X`,
written in the spelling that `AlgebraicGeometry.DefinesRationalSingularity` uses: Mathlib's
`CategoryTheory.Sheaf.H` of the abelian sheaf underlying `𝒪_X`. -/
abbrev FirstStructureSheafCohomologyVanishes (X : Scheme.{u}) : Prop :=
  letI : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  letI : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  Subsingleton (Sheaf.H.{u, u, u, u}
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj X.sheaf) 1)

/-- **`H¹(X, 𝒪_X) = 0` on an affine scheme.** This is Serre vanishing, [Stacks, Tag 01XB], at
the terminal open of `X`, which is affine; global cohomology is the value of the cohomology
presheaf at that open because it is terminal in the site. -/
@[sga "1 XI 6.9" "partial", sga "3 XXII 5.9.6" "special case"]
theorem firstStructureSheafCohomologyVanishes_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    FirstStructureSheafCohomologyVanishes X := by
  let _ : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  let _ : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  have hzero := Stacks.Cohomology.FiniteCover.isZero_H'_of_isAffineOpen X
    (SheafOfModules.unit X.ringCatSheaf) (⊤ : X.Opens) (isAffineOpen_top X) 1 one_pos
  exact (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf)) 1).2
    (AddCommGrpCat.subsingleton_of_isZero hzero)

/-- **`H¹ = 0` propagates along a sequence of blowups at closed points.** Let `A` be a local
ring and let `Y ⟶ Spec(A)` be a finite sequence of blowups at closed points lying over the
closed point of `Spec(A)`. If the vanishing of the first cohomology of the structure sheaf
survives one such blowup, then it holds on `Y`: the sequence starts at the affine scheme
`Spec(A)`, where the vanishing is Serre's. -/
theorem firstStructureSheafCohomologyVanishes_of_pointBlowupChain (A : Type u) [CommRing A]
    [IsLocalRing A]
    (blowUpStep : ∀ (W : Scheme.{u}) (h : W ⟶ Spec (.of A)),
      PointBlowupChain (Spec (.of A)) {IsLocalRing.closedPoint A} W h →
      ∀ (w : W) (hw : IsClosed ({w} : Set W)),
        FirstStructureSheafCohomologyVanishes W →
        FirstStructureSheafCohomologyVanishes
          (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)))
    {Y : Scheme.{u}} {p : Y ⟶ Spec (.of A)}
    (hp : PointBlowupChain (Spec (.of A)) {IsLocalRing.closedPoint A} Y p) :
    FirstStructureSheafCohomologyVanishes Y := by
  induction hp with
  | refl => exact firstStructureSheafCohomologyVanishes_of_isAffine _
  | step hh w hw _ ih => exact blowUpStep _ _ hh w hw ih

/-- **The argument of [Stacks, Tag 0B4Q] over three of its inputs.** A Nagata regular local
ring `A` of dimension two defines a rational singularity once the three inputs below are given.
The complete statement of Tag 0B4Q, with none of them assumed, is
`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`.

Three inputs of the source's proof are carried as hypotheses. `dominate` is [Stacks, Tag 0AHI],
that every such modification is dominated by a sequence of blowups at closed points over the
closed point of `Spec(A)`, together with the regularity of the members of that sequence
([Stacks, Tag 0AGR]) and their consequent normality ([Stacks, Tag 0567]). `transfer` is the
injectivity of `H¹(X, 𝒪_X) → H¹(X', 𝒪_{X'})` along a dominating normal modification, the first
conclusion of [Stacks, Tag 0AXF]. `blowUpStep` is the survival of the vanishing across a single
blowup at a closed point, which the source gets from [Stacks, Tag 0AGS] and the same exact
sequence of Tag 0AXF.

What is proved is the rest: the vanishing at the start of the sequence, its propagation along
the whole sequence, and the descent of the vanishing from the dominating sequence to the given
modification. -/
theorem definesRationalSingularity_of_isRegularLocalRing (A : Type u) [CommRing A] [IsDomain A]
    [IsRegularLocalRing A] [IsNagataRing A] (_hdim : ringKrullDim A = 2)
    (dominate : ∀ (X : Scheme.{u}), IsNormal X → ∀ f : X ⟶ Spec (.of A), IsModification f →
      ∃ (Y : Scheme.{u}) (p : Y ⟶ Spec (.of A)) (g : Y ⟶ X),
        PointBlowupChain (Spec (.of A)) {IsLocalRing.closedPoint A} Y p ∧
          IsNormal Y ∧ IsModification p ∧ g ≫ f = p)
    (transfer : ∀ (X Y : Scheme.{u}) (f : X ⟶ Spec (.of A)) (p : Y ⟶ Spec (.of A)) (g : Y ⟶ X),
      IsNormal X → IsNormal Y → IsModification f → IsModification p → g ≫ f = p →
        FirstStructureSheafCohomologyVanishes Y → FirstStructureSheafCohomologyVanishes X)
    (blowUpStep : ∀ (W : Scheme.{u}) (h : W ⟶ Spec (.of A)),
      PointBlowupChain (Spec (.of A)) {IsLocalRing.closedPoint A} W h →
      ∀ (w : W) (hw : IsClosed ({w} : Set W)),
        FirstStructureSheafCohomologyVanishes W →
        FirstStructureSheafCohomologyVanishes
          (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))) :
    DefinesRationalSingularity A := by
  intro X hX f hf
  obtain ⟨Y, p, g, hchain, hYnormal, hpmod, hgp⟩ := dominate X hX f hf
  exact transfer X Y f p g hX hYnormal hf hpmod hgp
    (firstStructureSheafCohomologyVanishes_of_pointBlowupChain A blowUpStep hchain)

end AlgebraicGeometry

end
