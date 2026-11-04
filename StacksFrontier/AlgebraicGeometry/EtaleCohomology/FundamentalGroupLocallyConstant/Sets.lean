module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtaleEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RepresentabilityDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.FundamentalGroupTheorem
public import StacksFrontier.CategoryTheory.Action.UniverseChange

/-!
# Finite locally constant sheaves of sets and the étale fundamental group

Let `X` be a connected scheme and `x` a geometric point of it. The finite locally constant
sheaves of sets on the small étale site of `X` form a category equivalent to the category of
finite sets with a continuous action of `π₁(X, x)`.

## Main results

* `AlgebraicGeometry.essSurj_finiteSmallEtaleToFiniteLocallyConstant`: every finite locally
  constant sheaf of sets is represented by a finite étale cover.
* `AlgebraicGeometry.finiteLocallyConstantFiniteEtaleEquivalence`: the finite locally constant
  sheaves of sets on the small étale site of `X` are equivalent to the finite étale covers of `X`.
* `AlgebraicGeometry.finiteLocallyConstantSetsEquivalence`: for connected `X`, the finite locally
  constant sheaves of sets on the small étale site of `X` are equivalent to the finite continuous
  `π₁(X, x)`-sets.
* `AlgebraicGeometry.nonempty_finiteLocallyConstantSetsEquivalence`: such an equivalence exists.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf
open scoped FintypeCatDiscrete

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- Every finite locally constant sheaf of sets is represented by a finite étale cover: the
embedding `finiteSmallEtaleToFiniteLocallyConstant` is essentially surjective. -/
public theorem essSurj_finiteSmallEtaleToFiniteLocallyConstant :
    (finiteSmallEtaleToFiniteLocallyConstant B X).EssSurj where
  mem_essImage G := by
    obtain ⟨U, hU, ⟨c⟩⟩ :=
      (Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable
        B X G.obj).mp G.property
    exact ⟨⟨U, hU⟩, ⟨ObjectProperty.isoMk _ c.symm⟩⟩

/-- The embedding of the finite objects of the small étale site into the finite locally
constant sheaves of sets is an equivalence. -/
public instance isEquivalence_finiteSmallEtaleToFiniteLocallyConstant :
    (finiteSmallEtaleToFiniteLocallyConstant B X).IsEquivalence :=
  letI := (finiteSmallEtaleToFiniteLocallyConstantFullyFaithful B X).full
  letI := (finiteSmallEtaleToFiniteLocallyConstantFullyFaithful B X).faithful
  letI := essSurj_finiteSmallEtaleToFiniteLocallyConstant B X
  {}

/-- The equivalence between the finite locally constant sheaves of sets on the small étale site
of `X` and the finite étale covers of `X`. -/
@[stacks 03RV "the equivalence of categories; the object-level statement is \
  Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable"]
public noncomputable def finiteLocallyConstantFiniteEtaleEquivalence :
    FiniteLocallyConstantSheaf B X ≌ FiniteEtaleOver X.1 :=
  (finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.symm.trans
    (finiteEtaleSiteEquivalence B X)

variable [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- For a connected scheme `X` with a geometric point `x`, the equivalence between the finite
locally constant sheaves of sets on the small étale site of `X` and the finite sets with a
continuous action of the étale fundamental group `π₁(X, x)`. It is
`finiteLocallyConstantFiniteEtaleEquivalence` followed by
`finiteEtaleEquivalenceOfIsGaloisCategory` and the change of universe
`contActionUniverseEquivalence`. -/
@[stacks 0DV5 "(1) finite locally constant sheaves of sets are the finite continuous \
  π₁(X, x)-sets"]
public noncomputable def finiteLocallyConstantSetsEquivalence :
    FiniteLocallyConstantSheaf B X ≌
      ContAction FintypeCat.{u + 1} (EtaleFundamentalGroup X.1 x) :=
  (finiteLocallyConstantFiniteEtaleEquivalence B X).trans
    ((finiteEtaleEquivalenceOfIsGaloisCategory X.1 x).trans
      (contActionUniverseEquivalence.{u, u + 1} (EtaleFundamentalGroup X.1 x)))

/-- For a connected scheme with a geometric point there is an equivalence between the finite
locally constant sheaves of sets on its small étale site and the finite sets with a continuous
action of its étale fundamental group. -/
public theorem nonempty_finiteLocallyConstantSetsEquivalence :
    Nonempty (FiniteLocallyConstantSheaf B X ≌
      ContAction FintypeCat.{u + 1} (EtaleFundamentalGroup X.1 x)) :=
  ⟨finiteLocallyConstantSetsEquivalence B X x⟩

end AlgebraicGeometry

end
