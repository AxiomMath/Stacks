module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompJoin
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompUnitEq

/-!
# The compatibility of Stacks 03LU with étale restriction, at representable morphisms

Along an étale morphism of algebraic spaces the inverse image of `𝒪`-modules of Stacks 03LU is
étale restriction, by Stacks 03LW.  Étale restriction composes on the nose while the inverse
image composes only up to the comparison of Stacks 03LU, and the compatibility of the two is
`AlgebraicGeometry.Space.QuasiCoherentDescent.EtaleRestrictionComp` at the pair in question.

The compatibility is **not** available at an arbitrary composable pair of étale morphisms of
algebraic spaces; it is available as soon as both adjunctions of étale restriction along the
composite have the same unit — that is
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit`, which holds for a composable
pair of étale morphisms with no representability hypothesis at all.  (This file originally took
that equality from the chart projection of a section of a direct image, which exists only at a
representable morphism, and carried the representability hypotheses for it; the hypothesis-free
proof supersedes that route.)  Feeding the equality to
`AlgebraicGeometry.Space.etaleRestrictionComp_of_unit` is all this file does for the
compatibility itself.

The consequence that descent of morphisms consumes is the compatibility at the pairs a family of
étale morphisms needs — the two projections of a pairwise fibre product followed by the two
members.  Those projections are base changes of members of the family, hence relatively
representable as soon as the members are, so a family of relatively representable étale
morphisms satisfies
`AlgebraicGeometry.Space.QuasiCoherentDescent.PairEtaleRestrictionComp` with nothing carried.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleRestrictionComp_of_representable`: **the
  compatibility of Stacks 03LU with étale restriction holds at a composable pair of relatively
  representable étale morphisms.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.relativelyRepresentable_pairFst` and
  `…_pairSnd`: the two projections of a pairwise fibre product of a family of relatively
  representable morphisms are relatively representable.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pairEtaleRestrictionComp_of_representable`:
  **a family of relatively representable étale morphisms satisfies the compatibility at the
  pairs the pairwise condition of Stacks 04W3 is read at.**

## Implementation notes

The first result is *not* a corollary of
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_unit`: that theorem's
hypothesis is the equality of units at *every* composable pair of étale morphisms, which is
exactly what is not available.  What is shared with it is
`AlgebraicGeometry.Space.etaleRestrictionComp_of_unit`, the same reading on sections performed
at one fixed pair.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The compatibility of the comparison of Stacks 03LU with étale restriction, at a
composable pair of relatively representable étale morphisms.**  Reading a section of the
iterated inverse image through the comparison of Stacks 03LU is reading it over the two charts
in turn. -/
theorem etaleRestrictionComp_of_representable {C₀ A₀ D₀ : AlgebraicSpaces B S hS}
    (h : D₀ ⟶ A₀) (g : A₀ ⟶ C₀) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
    (_hreph : yoneda.relativelyRepresentable h.hom)
    (_hrepg : yoneda.relativelyRepresentable g.hom)
    (_hrephg : yoneda.relativelyRepresentable (h ≫ g).hom) :
    EtaleRestrictionComp B S hS h g hh hg hhg :=
  etaleRestrictionComp_of_unit B S hS h g hh hg hhg
    (etaleModulePullbackCompAdjunction_unit B S hS h g hh hg hhg)

variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X)

/-- The first projection of a pairwise fibre product is relatively representable, being a base
change of the second member. -/
theorem relativelyRepresentable_pairFst
    (hrep : ∀ i, yoneda.relativelyRepresentable (f i).hom) (i j : I) :
    yoneda.relativelyRepresentable (pairFst B S hS Yi f i j).hom :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (f i).hom (f j).hom).flip (hrep j)

/-- The second projection of a pairwise fibre product is relatively representable, being a base
change of the first member. -/
theorem relativelyRepresentable_pairSnd
    (hrep : ∀ i, yoneda.relativelyRepresentable (f i).hom) (i j : I) :
    yoneda.relativelyRepresentable (pairSnd B S hS Yi f i j).hom :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (f i).hom (f j).hom) (hrep i)

/-- **A family of relatively representable étale morphisms satisfies the compatibility of
Stacks 03LU with étale restriction at the pairs the pairwise condition of Stacks 04W3 is read
at.**  The two projections of a pairwise fibre product are base changes of the members, hence
relatively representable, and so are their composites with the members. -/
theorem pairEtaleRestrictionComp_of_representable (hf : ∀ i, IsEtale B S hS (f i).hom)
    (hrep : ∀ i, yoneda.relativelyRepresentable (f i).hom) :
    PairEtaleRestrictionComp B S hS Yi f hf where
  fst i j :=
    etaleRestrictionComp_of_representable B S hS (pairFst B S hS Yi f i j) (f i)
      (isEtale_pairFst B S hS Yi f hf i j) (hf i)
      (isEtale_comp B S hS (isEtale_pairFst B S hS Yi f hf i j) (hf i))
      (relativelyRepresentable_pairFst B S hS Yi f hrep i j) (hrep i)
      (MorphismProperty.comp_mem _ _ _
        (relativelyRepresentable_pairFst B S hS Yi f hrep i j) (hrep i))
  snd i j :=
    etaleRestrictionComp_of_representable B S hS (pairSnd B S hS Yi f i j) (f j)
      (isEtale_pairSnd B S hS Yi f hf i j) (hf j)
      (isEtale_comp B S hS (isEtale_pairSnd B S hS Yi f hf i j) (hf j))
      (relativelyRepresentable_pairSnd B S hS Yi f hrep i j) (hrep j)
      (MorphismProperty.comp_mem _ _ _
        (relativelyRepresentable_pairSnd B S hS Yi f hrep i j) (hrep j))

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
