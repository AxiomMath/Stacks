module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartRefinement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined

/-!
# The refined family of a countably indexed atlas is countably indexed

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` admitting an atlas as in Definition **Stacks 0AIM** all of whose members are countably
indexed, and let `g : Y ⟶ X` be a morphism from an affine formal algebraic space which is
representable by algebraic spaces and étale. Refining the atlas against the chart
(`AlgebraicGeometry.FormalSpace.exists_affineEtaleFamily_over_chart_of_atlas`) produces a
jointly locally surjective family of representable étale morphisms into `Y` out of affine formal
algebraic spaces, each of which also maps representably and étale to a member of the atlas;
clause (1) of **Stacks 0AKQ**,
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isRepresentable'`, then makes every member
of the refined family countably indexed.

This is the first half of the proof of the implication (2) ⟹ (1) of **Stacks 0AKX** for countable
indexing, carried out with no hypothesis beyond the data of the tag.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_countablyIndexed_affineEtaleFamily_over_chart`: the
  refined family, with every member countably indexed.

## What is assumed

Nothing. The three inputs used are all theorems of this library: **Stacks 0AJ3** in the chart
form `…isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`, the coverings of
Definition 0AIM carried by `IsFormalAlgebraicSpace`, and clause (1) of **Stacks 0AKQ**, which is
unconditional because **Stacks 0AKN** is the library's
`…relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`.

What the implication (2) ⟹ (1) of Stacks 0AKX still needs beyond this is the second half of its
proof — quasi-compactness of `Y` cutting the family down to a finite one, and the finite disjoint
union of the resulting charts mapping to `Y` surjectively, flatly and representably — and, on the
other side of the equivalence, the transfer of countable indexing along that morphism, which is
**Stacks 0AKS** and is carried unconditionally by
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_iff_of_surjective_flat'`.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AKQ](https://stacks.math.columbia.edu/tag/0AKQ)
* [Stacks Project, Tag 0AKS](https://stacks.math.columbia.edu/tag/0AKS)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The refinement of a countably indexed atlas against an affine étale chart.** Let `X` be a
formal algebraic space over `S` with an atlas as in Definition **Stacks 0AIM** all of whose
members are countably indexed, and let `g : Y ⟶ X` be a morphism from an affine formal algebraic
space which is representable by algebraic spaces and étale. Then `Y` receives a jointly locally
surjective family of representable étale morphisms out of countably indexed affine formal
algebraic spaces.

Each member of the family is a chart of a fibre product `Xᵢ ×_X Y`, a formal algebraic space by
**Stacks 0AJ3**, and is countably indexed by clause (1) of **Stacks 0AKQ** applied to its
representable étale morphism to `Xᵢ`. -/
theorem exists_countablyIndexed_affineEtaleFamily_over_chart
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (hatlas : HasAffineEtaleAtlasWithProperty B S hS X (IsCountablyIndexed B S hS))
    {Y : FppfSheaf B S hS} (g : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) (hg : IsRepresentableEtale B S hS g) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (K : Type (u + 1)) (U : K → FppfSheaf B S hS) (w : ∀ k, U k ⟶ Y),
      (∀ k, IsAffineFormalAlgebraicSpace B S hS (U k)) ∧
      (∀ k, IsRepresentableEtale B S hS (w k)) ∧
      Sheaf.IsLocallySurjective (Sigma.desc w) ∧
      ∀ k, IsCountablyIndexed B S hS (U k) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, Xi, fi, hXiaff, hXiet, hXicov, hXicount⟩ := hatlas
  obtain ⟨K, U, w, κ, v, hUaff, hUet, hVet, hcov⟩ :=
    exists_affineEtaleFamily_over_chart_of_atlas B S hS hX Xi fi hXiaff hXiet hXicov g hY hg
  exact ⟨K, U, w, hUaff, hUet, hcov, fun k ↦
    isCountablyIndexed_of_isRepresentable' B S hS (v k) (hUaff k) (hXiaff (κ k))
      (hVet k).1 (hXicount (κ k))⟩

end AlgebraicGeometry.FormalSpace

end
