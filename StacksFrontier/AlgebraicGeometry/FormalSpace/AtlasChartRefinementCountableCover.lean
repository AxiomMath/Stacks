module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartRefinementTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductRepresentableEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PrescribedCoverFiniteSubfamily
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType

/-!
# A countably indexed chart dominating an affine étale chart

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` admitting an atlas as in Definition **Stacks 0AIM** all of whose members are countably
indexed, and let `g : Y ⟶ X` be a morphism from an affine formal algebraic space which is
representable by algebraic spaces and étale. Then `Y` receives a surjective, flat morphism,
representable by algebraic spaces and locally of finite type, from a *single* countably
indexed affine formal algebraic space.

This is the whole refinement half of the proof of the implication (2) ⟹ (1) of
**Stacks 0AKX** for countable indexing. The atlas is refined against the chart by
`AlgebraicGeometry.FormalSpace.exists_countablyIndexed_affineEtaleFamily_over_chart`, which
delivers a jointly locally surjective family of countably indexed affine formal algebraic
spaces over `Y`; quasi-compactness of the affine formal algebraic space `Y` cuts that family
down to a finite jointly surjective subfamily, by the implication (1) ⟹ (2) of **Stacks 0AJ9**
in the prescribed-covering form
`exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace`;
and the coproduct of the subfamily is the single chart sought, affine formal and countably
indexed because a finite coproduct of such is such.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_countablyIndexed_surjective_flat_over_chart`: the
  single countably indexed chart dominating `Y`.

## What is assumed

Nothing. Every input is a theorem of this library:

* the refined family — `…exists_countablyIndexed_affineEtaleFamily_over_chart`, itself resting
  on **Stacks 0AJ3** in its chart form and on clause (1) of **Stacks 0AKQ**;
* the finite cut — `…exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace`,
  the implication (1) ⟹ (2) of **Stacks 0AJ9** applied to a prescribed covering;
* the coproduct being affine formal — `…isAffineFormalAlgebraicSpace_sigma`;
* the coproduct being countably indexed — `…isCountablyIndexed_sigma`;
* the morphism out of the coproduct being representable étale —
  `…coproductsRepresentableEtale`, and hence flat and locally of finite type by
  `…IsRepresentableFlat.of_isRepresentableEtale` and
  `…IsLocallyOfFiniteType.of_isRepresentableEtale`.

## Implementation notes

The hypothesis `hX` that `X` is a formal algebraic space is the standing hypothesis of
Stacks 0AKX, which is stated for a formal algebraic space over `S`. It is *not* implied by the
atlas data alone, which is why this is stated as a lemma about a formal algebraic space rather
than as a proof of `AlgebraicGeometry.FormalSpace.HasAffineEtaleRefinementWithProperty` at
`P = IsCountablyIndexed`: that predicate quantifies over an arbitrary `X` carrying only the
atlas, so it additionally asks for the set-theoretic condition of
`AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace` out of nothing — and, more decisively,
it is false for arbitrary `P`.

NO TAG IS ATTACHED. This is the refinement half of the proof of the implication (2) ⟹ (1) of
Stacks 0AKX, not a numbered statement of the source; the implication itself additionally needs
the transfer of countable indexing along the morphism produced here, which is the forward
implication of **Stacks 0AKS**.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AKQ](https://stacks.math.columbia.edu/tag/0AKQ)
* [Stacks Project, Tag 0AKS](https://stacks.math.columbia.edu/tag/0AKS)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A countably indexed chart dominating an affine étale chart.** Let `X` be a formal
algebraic space over `S` with an atlas as in Definition **Stacks 0AIM** all of whose members
are countably indexed, and let `g : Y ⟶ X` be a morphism from an affine formal algebraic space
which is representable by algebraic spaces and étale. Then there is a countably indexed affine
formal algebraic space `W` and a morphism `w : W ⟶ Y` which is representable by algebraic
spaces, surjective, flat and locally of finite type.

Refining the atlas against `Y` gives a jointly locally surjective family of countably indexed
affine formal algebraic spaces representable étale over `Y`; since `Y` is an affine formal
algebraic space it is quasi-compact, so a finite subfamily is already jointly surjective, and
`W` is the coproduct of that subfamily. The morphism out of the coproduct is representable
étale, hence flat and locally of finite type, and it is surjective because the subfamily is
jointly surjective. -/
theorem exists_countablyIndexed_surjective_flat_over_chart
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (hatlas : HasAffineEtaleAtlasWithProperty B S hS X (IsCountablyIndexed B S hS))
    {Y : FppfSheaf B S hS} (g : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) (hg : IsRepresentableEtale B S hS g) :
    ∃ (W : FppfSheaf B S hS) (w : W ⟶ Y), IsAffineFormalAlgebraicSpace B S hS W ∧
      IsCountablyIndexed B S hS W ∧
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS w.hom ∧
      IsSurjective B S hS w ∧ IsRepresentableFlat B S hS w ∧
      IsLocallyOfFiniteType B S hS w := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  -- the atlas refined against the chart, every member countably indexed
  obtain ⟨K, U, w, hUaff, hUet, hUcov, hUcount⟩ :=
    exists_countablyIndexed_affineEtaleFamily_over_chart B S hS hX hatlas g hY hg
  -- quasi-compactness of the affine formal algebraic space `Y` cuts it down to a finite one
  obtain ⟨σ, hσ, k, hsub⟩ :=
    exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace B S hS hY U w
      ⟨hUaff, hUet, hUcov⟩
  let : Finite σ := hσ
  obtain ⟨hsubaff, hsubet, hsubcov⟩ := hsub
  -- the coproduct of the finite subfamily
  have hWet : IsRepresentableEtale B S hS (Sigma.desc fun s ↦ w (k s)) :=
    coproductsRepresentableEtale B S hS σ (fun s ↦ U (k s)) Y (fun s ↦ w (k s)) hσ hsubet
  exact ⟨∐ fun s ↦ U (k s), Sigma.desc fun s ↦ w (k s),
    isAffineFormalAlgebraicSpace_sigma B S hS _ hsubaff,
    isCountablyIndexed_sigma B S hS _ fun s ↦ hUcount (k s),
    hWet.1, isSurjective_of_isLocallySurjective B S hS hsubcov,
    IsRepresentableFlat.of_isRepresentableEtale B S hS _ hWet,
    IsLocallyOfFiniteType.of_isRepresentableEtale B S hS _ hWet⟩

end AlgebraicGeometry.FormalSpace

end
