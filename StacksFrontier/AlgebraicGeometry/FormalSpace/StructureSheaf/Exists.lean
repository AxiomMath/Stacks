module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.StructureSheaf.Existence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StructureSheaf.ReductionSquares

/-!
# Every formal algebraic space has a structure sheaf (Stacks 0DEJ)

Let `X` be a formal algebraic space over a scheme `S` of a big fppf site. **Stacks 0DEJ** says
that `X` has a structure sheaf in the sense of Section 0DEI
(`AlgebraicGeometry.FormalSpace.IsStructureSheaf`): a sheaf of topological rings `𝒪_X` on
`X_étale` with `𝒪_X(U_red) = lim Γ(U_λ, 𝒪_{U_λ})` as topological rings, canonically, for every
affine formal algebraic space `U` representable étale over `X` and every colimit presentation
`U = colim U_λ` as in Stacks 0AI7.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isStructureSheaf`: **Stacks 0DEJ**.
* `AlgebraicGeometry.FormalSpace.exists_isStructureSheaf_of_isEquivalence`: the existence, given
  that the functor `U ↦ U_red` of Stacks 0DEH is an equivalence.

## Implementation notes

The proof is the source's. By Stacks 0DEH the functor `U ↦ U_red` identifies the affine formal
algebraic spaces representable étale over `X` with `X_affine,étale`, so the rule of Section 0DEI
defines a presheaf of topological rings on `X_affine,étale`; it is a sheaf by étale descent on the
stages, the limits commuting with limits and the topologies being the limit topologies; and it
extends to `X_étale` by Stacks 0DEB. The construction is
`AlgebraicGeometry.FormalSpace.Reduction.AffineEtaleCorrespondence.structureSheaf`; the passage
from the equivalence of Stacks 0DEH to the correspondence of reduction squares it is built from is
`AlgebraicGeometry.FormalSpace.affineEtaleCorrespondence_of_isEquivalence`.

## References

* [Stacks Project, Tag 0DEJ](https://stacks.math.columbia.edu/tag/0DEJ)
* [Stacks Project, Section 0DEI](https://stacks.math.columbia.edu/tag/0DEI)
* [Stacks Project, Tag 0DEH](https://stacks.math.columbia.edu/tag/0DEH)
* [Stacks Project, Tag 0DEB](https://stacks.math.columbia.edu/tag/0DEB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A formal algebraic space has a structure sheaf as soon as the functor `U ↦ U_red` of
Stacks 0DEH is an equivalence. -/
theorem exists_isStructureSheaf_of_isEquivalence {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X)
    [(affineEtaleReductionFunctor hX (canonicalReduction hX)).IsEquivalence] :
    ∃ O : Sheaf (canonicalSmallEtaleTopology hX) TopCommRingCat.{u + 1}, IsStructureSheaf hX O :=
  ⟨_, isStructureSheaf_structureSheaf hX
    (affineEtaleCorrespondence_of_isEquivalence hX (canonicalReduction hX))⟩

/-- **Stacks 0DEJ.** Every formal algebraic space has a structure sheaf: a sheaf of topological
rings `𝒪_X` on its small étale site `X_étale` such that `𝒪_X(U_red) = lim Γ(U_λ, 𝒪_{U_λ})` as
topological rings, canonically, for every affine formal algebraic space `U` with a morphism
`U ⟶ X` representable by algebraic spaces and étale, and every colimit presentation
`U = colim U_λ` of `U` as in Stacks 0AI7 (`AlgebraicGeometry.FormalSpace.IsStructureSheaf`). -/
@[stacks 0DEJ]
theorem exists_isStructureSheaf {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) :
    ∃ O : Sheaf (canonicalSmallEtaleTopology hX) TopCommRingCat.{u + 1}, IsStructureSheaf hX O :=
  have := affineEtaleReductionFunctor_isEquivalence hX (canonicalReduction hX)
  exists_isStructureSheaf_of_isEquivalence hX

end AlgebraicGeometry.FormalSpace

end
