module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.GroupSpaceTranslation

/-!
# Finite presentation of a closed subscheme of a representable algebraic space

Let `j : W ⟶ V` be a morphism of the big fppf category over `S` whose underlying morphism of
schemes is a closed immersion of finite presentation. Then `Subfunctor.range (yoneda.map j)` is
a closed subspace of `yoneda.obj V` — that is
`AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map` — and this file adds that the
inclusion of that subspace is of finite presentation in the sense of Stacks 03XP, part (3).

Together the two give both of the closed-part hypotheses that
`AlgebraicGeometry.Space.FormalGlueingSituation` asks of its closed subspace `Z`, for a `Z` cut
out by a finitely generated ideal of a ring in the site.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_ι_range_yoneda_map`: the inclusion of the range
  of a represented closed immersion of finite presentation is of finite presentation.

## Implementation notes

The inclusion `(Subfunctor.range (yoneda.map j)).ι` is not syntactically `yoneda.map j`; the two
differ by the isomorphism of `yoneda.obj W` onto the range, which is an isomorphism because
`yoneda.map j` is a monomorphism. The identification is
`AlgebraicGeometry.Space.inv_toRange_comp`, and monomorphy comes from the closed immersion
hypothesis via `AlgebraicGeometry.Space.mono_of_isClosedImmersion`.

Finite presentation of `yoneda.map j` itself is
`AlgebraicGeometry.Space.isFinitePresentation_yoneda_map`, which is unconditional on the scheme
morphism being a closed immersion. So the closed immersion hypothesis is used only to move the
conclusion along that isomorphism, and it is carried separately from finite presentation rather
than being derived from it — a morphism of finite presentation need not be a monomorphism.

The three conjuncts of `AlgebraicGeometry.Space.IsFinitePresentation` are moved across the
isomorphism one at a time, because each has its own invariance lemma: local finite presentation
is `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_precomp_iso`, quasi-compactness is
`AlgebraicGeometry.Space.isQuasiCompact_isIso_comp`, and quasi-separatedness is
`AlgebraicGeometry.Space.isQuasiSeparated_isIso_comp_iff`.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inclusion of a closed subscheme of a representable algebraic space is of finite
presentation**, when the closed immersion of schemes it comes from is.

This is the companion of `AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map`: that one
says the range is a closed subspace, this one says its inclusion is of finite presentation. -/
theorem isFinitePresentation_ι_range_yoneda_map {W V : BigFppfOver B S hS} (j : W ⟶ V)
    (hclosed : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))
    (hfp : AlgebraicGeometry.FinitePresentation ((BigFppfOver.toScheme B S hS).map j)) :
    IsFinitePresentation B S hS (Subfunctor.range (yoneda.map j)).ι := by
  have hpClosed : IsClosedImmersion B S hS (yoneda.map j) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) j).2 hclosed
  have hmono : Mono (yoneda.map j) := mono_of_isClosedImmersion B S hS _ hpClosed
  obtain ⟨hlfp, hqc, hqs⟩ := isFinitePresentation_yoneda_map B S hS j hfp
  have heq : (asIso (Subfunctor.toRange (yoneda.map j))).inv ≫ yoneda.map j =
      (Subfunctor.range (yoneda.map j)).ι := inv_toRange_comp (yoneda.map j)
  rw [← heq]
  refine ⟨?_, ?_, ?_⟩
  · exact (holdsOnEveryEtaleChart_precomp_iso B S hS
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u})
      (asIso (Subfunctor.toRange (yoneda.map j))).symm (yoneda.map j)).1 hlfp
  · exact isQuasiCompact_isIso_comp B S hS _ hqc
  · exact (isQuasiSeparated_isIso_comp_iff B S hS _ (yoneda.map j)).2 hqs

end AlgebraicGeometry.Space

end
