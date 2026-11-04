module

public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.SegreClosedImmersion

/-!
# The Segre projections, II: what Tag 01WD still needs, stated at its weakest

`Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegre_of_projSegreIso` hands Stacks Tag
01WD over to an *isomorphism* between `AlgebraicGeometry.Proj` of the Segre product and the
product of the two integral models of projective space.  An isomorphism is more than the tag
needs.  The tag asserts the existence of a closed immersion, and the morphism it is built from,
`Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegreHom`, is already known to be a closed
immersion unconditionally; so a morphism in one direction only, itself merely a closed immersion,
suffices.  That is the hypothesis recorded here.

## Main results

* `Stacks.AlgebraicGeometry.SegreProjection.absoluteSegre_of_closedImmersion`: a closed immersion
  of the product of the two integral models into `Proj` of the Segre product — no isomorphism, no
  inverse, nothing about the other direction — gives
  `Stacks.AlgebraicGeometry.SegreEmbedding.AbsoluteSegre`.

* `Stacks.AlgebraicGeometry.SegreProjection.exists_segreEmbedding_of_closedImmersion`: the
  statement of Tag 01WD itself, over an arbitrary base scheme, from that hypothesis.  Its
  conclusion is the tag's statement with the folded definitions replaced by their library names
  and nothing else changed, so this declaration is the machine check that the reduction chain of
  `StacksDraft/AlgebraicGeometry/F3/SegreEmbedding/` really reaches the tag's statement.

* `Stacks.AlgebraicGeometry.SegreProjection.exists_segreEmbedding_of_projSegreIso`: the same
  conclusion from the isomorphism hypothesis, i.e. the full chain
  `absoluteSegre_of_projSegreIso` → `exists_segreEmbedding_of_absolute` composed and elaborated
  against the tag's statement.

## Implementation notes

The weakening is exactly the observation that `IsClosedImmersion` is closed under composition
(`AlgebraicGeometry.IsClosedImmersion.comp`).  Nothing else about the two schemes is used, and in
particular the argument does not care which of the two is the product.

## What is not done

The hypothesis is still open.  No morphism in either direction between `Proj` of the Segre
product and the product of the two projective spaces is constructed in this library; the
ring-level ingredients for constructing one are in
`StacksFrontier/AlgebraicGeometry/SegreProjection/Substitution.lean`, and the gluing that would
turn them into a morphism is not performed.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.AlgebraicGeometry.SegreProjection

universe u

/-- **The weakest hypothesis that closes Tag 01WD.**  A closed immersion of the product of the
two integral models of projective space into `AlgebraicGeometry.Proj` of the Segre product yields
`Stacks.AlgebraicGeometry.SegreEmbedding.AbsoluteSegre`, because the Segre presentation already
provides a closed immersion out of that `Proj` and closed immersions compose.  No inverse of `g`
is needed, so this is strictly weaker than the isomorphism asked for by
`Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegre_of_projSegreIso`. -/
public theorem absoluteSegre_of_closedImmersion (n m : ℕ)
    (g : projectiveSpaceOver m (projectiveSpaceAtUniverse.{u} n) ⟶
      SegreClosedImmersion.projSegre (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
    (hg : IsClosedImmersion g) :
    SegreEmbedding.AbsoluteSegre.{u} n m := by
  have := hg
  have := SegreClosedImmersion.isClosedImmersion_absoluteSegreHom.{u} n m
  exact ⟨g ≫ SegreClosedImmersion.absoluteSegreHom n m, inferInstance⟩

/-- **Tag 01WD from the weakened hypothesis.**  The conclusion is the statement of the tag
verbatim, the folded definitions replaced by their library names. -/
public theorem exists_segreEmbedding_of_closedImmersion (n m : ℕ) (S : Scheme.{u})
    (g : projectiveSpaceOver m (projectiveSpaceAtUniverse.{u} n) ⟶
      SegreClosedImmersion.projSegre (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)))
    (hg : IsClosedImmersion g) :
    ∃ f : pullback ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ⟶
        projectiveSpaceOver (n * m + n + m) S,
      IsClosedImmersion f ∧
        f ≫ ((projectiveSpaceOver (n * m + n + m) S) ↘ S) =
          pullback.fst ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ≫
            ((projectiveSpaceOver n S) ↘ S) :=
  SegreEmbedding.exists_segreEmbedding_of_absolute n m S
    (absoluteSegre_of_closedImmersion n m g hg)

/-- **Tag 01WD from the isomorphism hypothesis**, which is the chain assembled by
`StacksDraft/AlgebraicGeometry/F3/SegreEmbedding/`, elaborated against the tag's statement. -/
public theorem exists_segreEmbedding_of_projSegreIso (n m : ℕ) (S : Scheme.{u})
    (e : SegreClosedImmersion.projSegre (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) ≅
      projectiveSpaceOver m (projectiveSpaceAtUniverse.{u} n)) :
    ∃ f : pullback ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ⟶
        projectiveSpaceOver (n * m + n + m) S,
      IsClosedImmersion f ∧
        f ≫ ((projectiveSpaceOver (n * m + n + m) S) ↘ S) =
          pullback.fst ((projectiveSpaceOver n S) ↘ S) ((projectiveSpaceOver m S) ↘ S) ≫
            ((projectiveSpaceOver n S) ↘ S) :=
  SegreEmbedding.exists_segreEmbedding_of_absolute n m S
    (SegreClosedImmersion.absoluteSegre_of_projSegreIso n m e)

end Stacks.AlgebraicGeometry.SegreProjection

end
