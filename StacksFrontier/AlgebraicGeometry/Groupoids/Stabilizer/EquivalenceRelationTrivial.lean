module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksFrontier.CategoryTheory.Limits.PullbackAlongFactoringMono

/-!
# The stabilizer of an equivalence-relation groupoid scheme is trivial

Let `(U, R, s, t, c)` be a groupoid scheme over `S` whose target and source maps form an internal
equivalence relation, so that `j = (t, s) : R ⟶ U ×_S U` is a monomorphism.  Then the stabilizer
`G = R ×_{(t,s), U ×_S U, Δ} U` of `AlgebraicGeometry.stabilizerOverBase` is `U` itself: its
structure morphism to the object scheme is an isomorphism.

The reason is that the diagonal of `U` factors through `(t, s)`, namely through the identity
section `e : U ⟶ R`, because `e` is a section of both the source and the target; the pullback of
a monomorphism along a morphism that factors through it is an isomorphism.

## Main results

* `AlgebraicGeometry.mono_sourceTarget`: `(t, s)` is a monomorphism.
* `AlgebraicGeometry.diagonal_eq_identity_comp_sourceTarget`: the diagonal of the object scheme
  factors through `(t, s)` via the identity section.
* `AlgebraicGeometry.isIso_stabilizer_hom`: the stabilizer is the object scheme.
* `AlgebraicGeometry.locallyQuasiFinite_stabilizer_hom`: hence the stabilizer is locally
  quasi-finite over the object scheme.

## Implementation notes

The last result is the form in which the hypothesis is consumed:
`AlgebraicGeometry.exists_affine_slice_locallyQuasiFinite`, the library's [Stacks, Tag 04N0],
asks for `LocallyQuasiFinite (stabilizer G).hom` as an instance, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EquivalenceRelationQuasiFiniteRefinement.lean`
name the triviality of the stabilizer of an equivalence-relation groupoid as one of the four
pieces of substrate that [Stacks, Tag 0489] needs and that this library did not record.  It is
registered as an instance, so that Tag 04N0 applies to an equivalence-relation groupoid with no
further argument.

`AlgebraicGeometry.sourceTarget` is formed with the cartesian-monoidal `lift` into `U ⊗ U`, while
`CategoryTheory.IsEquivalenceRelation` is a condition on the pair `(t, s)` directly; monicity of
the one from joint monicity of the other is the first result, and is the only place the two
encodings of the fibre square meet here.  The pre-relation form of the same monomorphism, with
the binary product `U ⨯ U` instead, is
`AlgebraicGeometry.GroupoidScheme.mono_groupoidPreRelation`.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The source-target morphism of a groupoid scheme whose target and source form an internal
equivalence relation is a monomorphism: the pair is jointly monic, and the two projections of
`U ⊗ U` recover its two components. -/
theorem mono_sourceTarget (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source] : Mono (sourceTarget G) := by
  obtain ⟨⟨E⟩⟩ := ‹IsEquivalenceRelation G.target G.source›
  refine ⟨fun {_} a b h => E.right_cancellation a b ?_ ?_⟩
  · simpa using congrArg (· ≫ fst G.objects G.objects) h
  · simpa using congrArg (· ≫ snd G.objects G.objects) h

/-- The diagonal of the object scheme of a groupoid scheme factors through its source-target
morphism, through the identity section: `e` is a section of both the target and the source. -/
theorem diagonal_eq_identity_comp_sourceTarget (G : GroupoidScheme S) :
    diagonal G = G.identity ≫ sourceTarget G := by
  refine hom_ext _ _ ?_ ?_
  · simp [diagonal, sourceTarget, G.target_identity]
  · simp [diagonal, sourceTarget, G.source_identity]

/-- **The stabilizer of an equivalence-relation groupoid scheme is its object scheme.** The
diagonal factors through the monomorphism `(t, s)`, so the pullback defining the stabilizer is
the object scheme itself. -/
theorem isIso_stabilizer_hom (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source] : IsIso (stabilizer G).hom := by
  have _ : Mono (sourceTarget G) := mono_sourceTarget G
  have _ : IsIso (pullback.snd (sourceTarget G) (diagonal G)) :=
    isIso_pullback_snd_of_factors_through_mono (sourceTarget G) (diagonal G) G.identity
      (diagonal_eq_identity_comp_sourceTarget G).symm
  exact inferInstanceAs (IsIso ((Over.forget S).map (pullback.snd (sourceTarget G) (diagonal G))))

/-- The stabilizer of an equivalence-relation groupoid scheme is locally quasi-finite over the
object scheme, being isomorphic to it.  This is the instance that
`AlgebraicGeometry.exists_affine_slice_locallyQuasiFinite`, the library's [Stacks, Tag 04N0],
asks for. -/
instance locallyQuasiFinite_stabilizer_hom (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source] : LocallyQuasiFinite (stabilizer G).hom := by
  have _ := isIso_stabilizer_hom G
  infer_instance

end AlgebraicGeometry

end
