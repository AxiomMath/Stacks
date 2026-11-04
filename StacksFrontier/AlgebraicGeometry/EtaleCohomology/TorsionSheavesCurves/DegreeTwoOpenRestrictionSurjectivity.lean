module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# Surjectivity of restriction to an open in degree two

For a scheme `X` and an abelian sheaf `F` on the small étale site of `X`, the statement that the
restriction map `H²_étale(X, F) → H²_étale(U, F)` is surjective for every open subscheme `U ⊆ X`.
This is statement (8) of the list in Situation 0A52; here it is a predicate on `F`, imposing none
of the hypotheses of that situation, and not the assertion that the predicate holds.

## Main definitions

* `Stacks.EtaleCohomology.IsDegreeTwoOpenRestrictionSurjective`: restriction of degree-two étale
  cohomology from `X` to every open subscheme of `X` is surjective, for every choice of `HasExt`
  on the open subscheme.

## Main results

* `Stacks.EtaleCohomology.isDegreeTwoOpenRestrictionSurjective_of_subsingleton`: if the
  degree-two étale cohomology of the restriction of `F` to each open subscheme is a subsingleton,
  then the restriction maps are surjective.

## References

* [Stacks Project, Tag 0A5A](https://stacks.math.columbia.edu/tag/0A5A)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- The restriction map `H²_étale(X, F) → H²_étale(U, F)` is surjective for every open subscheme
`U ⊆ X`. -/
@[stacks 0A5A "item (8) of 0A52: H²(X, F) → H²(U, F) surjective for all open U ⊆ X"]
def IsDegreeTwoOpenRestrictionSurjective
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) : Prop :=
  ∀ (U : X.Opens)
    [HasExt.{w} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})],
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} U.ι F 2)

/-- If the degree-two étale cohomology of the restriction of `F` to every open subscheme is a
subsingleton, then restriction of degree-two étale cohomology to every open subscheme is
surjective. -/
theorem isDegreeTwoOpenRestrictionSurjective_of_subsingleton
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : ∀ (U : X.Opens)
      [HasExt.{w} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})],
      Subsingleton (Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} U.ι).obj F) 2)) :
    IsDegreeTwoOpenRestrictionSurjective.{u, v, w} F := fun U _ _ ↦
  have := h U
  ⟨0, Subsingleton.elim _ _⟩

end Stacks.EtaleCohomology

end
