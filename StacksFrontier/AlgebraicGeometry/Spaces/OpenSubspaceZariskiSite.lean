module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# The small Zariski site of an algebraic space is the site of its space of points

For an algebraic space `X` over `S`, the open subspaces of `X` and the open subsets of the
topological space `|X|` of its points are the same thing, and a family of open subspaces is a
Zariski covering exactly when the corresponding open subsets cover `|X|`. Together these say
that the small Zariski site of `X` is the site attached to the topological space `|X|`, which is
the assertion of [Stacks, Tag 03BZ].

Both halves are proved elsewhere in this library; what is recorded here is the single statement
of the source lemma, with its two parts conjoined.

## Main results

* `AlgebraicGeometry.Space.openSubspacesOrderIso_and_isZariskiCover_iff`: **Stacks Tag 03BZ**,
  both parts in one statement.

## Implementation notes

The two parts are `AlgebraicGeometry.Space.existsUnique_openSubspacesOrderIso` for the
inclusion-preserving bijection and `AlgebraicGeometry.Space.isZariskiCover_iff_iUnion_pointsMap`
for the covering criterion; the second file imports the first, so both are available together
and the conjunction needs no further input.

The bijection is stated as the existence of a unique order isomorphism sending an open subspace
to the image of its point set, rather than as a bare function with an inverse: that is the form
in which the inclusion-preserving half of the source's assertion is the uniqueness clause.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02YY](https://stacks.math.columbia.edu/tag/02YY)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks Tag 03BZ.** Let `X` be an algebraic space over `S`.

Part (1): taking the image of the point set is an inclusion-preserving bijection from the open
subspaces of `X` to the open subsets of `|X|`; it is the unique order isomorphism doing so.

Part (2): a family of open subspaces of `X` is a Zariski covering exactly when the images of
the point sets of its members cover `|X|`.

Together these identify the small Zariski site of `X` with the site attached to the topological
space `|X|`. -/
@[stacks 03BZ]
theorem openSubspacesOrderIso_and_isZariskiCover_iff
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    (∃! e : {G : Subfunctor F // IsOpenSubspace B S hS G} ≃o
        TopologicalSpace.Opens (points B S hS F),
        ∀ G, (e G).1 = Set.range (pointsMap B S hS G.1.toFunctor G.1.ι)) ∧
      ∀ (I : Type u) (X : I → Subfunctor F), (∀ i, IsOpenSubspace B S hS (X i)) →
        (IsZariskiCover B S hS I X ↔
          (⋃ i, Set.range (pointsMap B S hS (X i).toFunctor (X i).ι)) = Set.univ) :=
  ⟨existsUnique_openSubspacesOrderIso B S hS F hF,
    fun I X hX => isZariskiCover_iff_iUnion_points B S hS F hF I X hX⟩

end AlgebraicGeometry.Space

end
