module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsLocallyClosedChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Surjectivity from the finite type points

An open subset of the point space of an algebraic stack which contains every finite type point
is the whole point space, and consequently a flat, locally finitely presented 1-morphism whose
image on points contains every finite type point of the target is surjective.

This is the step the proofs of **Stacks 06MF** and **Stacks 06N3** finish with. Both build a
chart near each finite type point of `𝒳` and take the disjoint union `W = ∐_x W_x`; the
resulting `f : W ⟶ 𝒳` is flat and locally of finite presentation, so `|f|` has open image by
**Stacks 06R7**, and that image contains every finite type point by construction. The source
concludes surjectivity by citing **Stacks 06G2** together with Properties of Stacks,
Lemma 100.4.4; that step is
`AlgebraicGeometry.Stack.isSurjective_of_finiteTypePoints_subset_range` below.

## What is proved

Both results are proved outright, with no carried hypothesis. The input is the first assertion
of **Stacks 06G2**, `AlgebraicGeometry.Stack.exists_mem_finiteTypePoints_of_isLocallyClosed`: a
nonempty locally closed subset of the point space meets the set of finite type points. The
complement of an open set is closed, hence locally closed, so if it were nonempty it would
contain a finite type point — which the hypothesis places in the open set.

Both are deliberately left untagged. **Stacks 06G2** asserts exactly two things, that a nonempty
locally closed subset of `|𝒳|` meets `𝒳_{ft-pts}` and that for closed `T` the intersection
`T ∩ 𝒳_{ft-pts}` is dense in `T`; both already carry the tag, in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsLocallyClosed`. What is below is the
corollary the source draws from it in the proofs of Stacks 06MF and Stacks 06N3, not a further
clause of it.

## Main results

* `AlgebraicGeometry.Stack.eq_univ_of_finiteTypePoints_subset`: an open subset of the point space
  containing every finite type point is everything.
* `AlgebraicGeometry.Stack.isSurjective_of_finiteTypePoints_subset_range`: a flat, locally
  finitely presented 1-morphism of algebraic stacks whose image on points contains every finite
  type point of the target is surjective.

## Implementation notes

Surjectivity is `AlgebraicGeometry.Stack.IsSurjective` (**Stacks 04ZS**), whose point map is
formed with the fibred-in-groupoids witness `Classical.choose 𝒳.property`, while
`AlgebraicGeometry.Stack.finiteTypePoints` and the topology
`AlgebraicGeometry.Stack.pointTopology` are formed with `𝒳.val.property`. The two witnesses are
proofs of the same proposition, so the point types and point maps they give are definitionally
equal and no transport is needed.

## References

* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06G2](https://stacks.math.columbia.edu/tag/06G2)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An open subset of the point space containing every finite type point is everything.**

Its complement is closed, hence locally closed, so were it nonempty the first assertion of
**Stacks 06G2** (`AlgebraicGeometry.Stack.exists_mem_finiteTypePoints_of_isLocallyClosed`) would
put a finite type point in it, contradicting the hypothesis that every finite type point lies in
the open set.

This is the corollary of Stacks 06G2 that the proofs of **Stacks 06MF** and **Stacks 06N3** use
to conclude that the chart they assemble out of charts at the finite type points is surjective;
see `AlgebraicGeometry.Stack.isSurjective_of_finiteTypePoints_subset_range`. -/
theorem eq_univ_of_finiteTypePoints_subset (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hU : letI := pointTopology B S hS 𝒳.val; IsOpen U)
    (hft : finiteTypePoints B S hS 𝒳 ⊆ U) :
    U = Set.univ := by
  let := pointTopology B S hS 𝒳.val
  refine Set.eq_univ_iff_forall.2 fun x => ?_
  by_contra hx
  obtain ⟨t, htU, htft⟩ := exists_mem_finiteTypePoints_of_isLocallyClosed.{u, w} B S hS 𝒳 Uᶜ
    hU.isClosed_compl.isLocallyClosed ⟨x, hx⟩
  exact htU (hft htft)

/-- **A flat, locally finitely presented 1-morphism whose image on points contains every finite
type point of the target is surjective.**

The image is open by **Stacks 06R7**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isOpenMap_pointsMap`), so
`AlgebraicGeometry.Stack.eq_univ_of_finiteTypePoints_subset` makes it the whole point space.

This is the last step of the proofs of **Stacks 06MF** and **Stacks 06N3**: the chart assembled
from charts at the individual finite type points is flat and locally of finite presentation and
its image contains every finite type point, and the source concludes surjectivity exactly this
way, citing **Stacks 06G2** together with Properties of Stacks, Lemma 100.4.4. -/
theorem isSurjective_of_finiteTypePoints_subset_range
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hft : finiteTypePoints B S hS 𝒴 ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS f)) :
    IsSurjective B S hS f := by
  let := pointTopology B S hS 𝒳.val
  let := pointTopology B S hS 𝒴.val
  have hopen : IsOpen (Set.range (AlgebraicStacks.pointsMap B S hS f)) :=
    (AlgebraicStacks.isOpenMap_pointsMap.{u, w} B S hS f hflat hlfp).isOpen_range
  exact Set.range_eq_univ.1
    (eq_univ_of_finiteTypePoints_subset.{u, w} B S hS 𝒴 _ hopen hft)

end AlgebraicGeometry.Stack

end
