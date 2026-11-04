module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfSchemeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.AffineOfAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedRefinable
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningSchemeRepresentableClosedImmersion

/-!
# A thickening of a scheme is a scheme (Stacks 05ZR, 07VU)

Let `S` be a scheme and let `X ⊂ X'` be a thickening of algebraic spaces over `S`. If `X` is
(representable by) a scheme, then so is `X'`. In particular an algebraic space whose reduction
is a scheme is itself a scheme.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isThickeningHom`: a thickening of an affine algebraic
  space is affine, in the morphism form.
* `AlgebraicGeometry.Space.isRepresentable_of_isThickening_of_isRepresentable`: **Stacks 05ZR**.
* `AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable`:
  **Stacks 05ZR**, in the morphism form.
* **Stacks 07VU** is registered on
  `AlgebraicGeometry.IsAlgebraicSpace.isRepresentable_of_isRepresentable_reduction` of
  `StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfSchemeReduction`, by `add_to_stacks` in
  `StacksFrontier.AlgebraicGeometry.Spaces.ThickeningSchemeRepresentableClosedImmersion`.

## Implementation notes

The proof is the source's direct proof, with the affine case
`AlgebraicGeometry.Space.C1573.isAffineSpace_of_isThickening` available at arbitrary order. The
affine opens of the scheme representing `X` give affine open subspaces `U ⊂ X`; each is
`X ×_{X'} U'` for a unique open subspace `U' ⊂ X'` (Stacks 05ZP), and `X ×_{X'} U' ⊂ U'` is a
thickening of an affine algebraic space, so `U'` is affine. The `U'` cover `X'` because `X` and
`X'` have the same points, and an algebraic space with a Zariski covering by schemes is a scheme
(Stacks 03KE).

For Stacks 07VU the reduction `X_{red} ⊂ X` is a thickening: a closed subspace with every point.

The conditional statements `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_thickening`,
`AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom` and
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_reduction` carry the three inputs of
Stacks 07VT as hypotheses; the statements here carry none of them.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 03KE](https://stacks.math.columbia.edu/tag/03KE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A thickening of an affine algebraic space is affine**, in the morphism form. -/
theorem isAffineSpace_of_isThickeningHom {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X')
    (hi : IsThickeningHom B S hS i) (hX : IsAffineSpace B S hS X.1) :
    IsAffineSpace B S hS X'.1 :=
  C1573.isAffineSpace_of_isThickening B S hS hi.2
    (hX.of_iso (@asIso _ _ _ _ (Subfunctor.toRange i.hom) hi.1))

/-- **An affine open subspace of a representable thickening restricts to an affine open of the
ambient space.** Let `G ⊂ X` be a thickening and let `U ⊂ G` be an open subspace which is
affine. The open subspace `U' ⊂ X` with `G ×_X U' = U` (Stacks 05ZP) is affine: `G ×_X U' ⊂ U'`
is a thickening of an affine algebraic space. -/
theorem exists_isOpenSubspace_isAffineSpace_of_isThickening {X : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (hG : IsThickening B S hS X G) (U : Subfunctor G.toFunctor)
    (hU : IsOpenSubspace B S hS U) (hUa : IsAffineSpace B S hS U.toFunctor) :
    ∃ U' : Subfunctor X.1, IsOpenSubspace B S hS U' ∧ U'.preimage G.ι = U ∧
      IsAffineSpace B S hS U'.toFunctor := by
  obtain ⟨U', ⟨hU', hUeq⟩, -⟩ :=
    existsUnique_isOpenSubspace_preimage_eq_of_isThickening B S hS hG U hU
  refine ⟨U', hU', hUeq, ?_⟩
  let U'sp : AlgebraicSpaces B S hS := ⟨U'.toFunctor, hU'.1⟩
  have hT : IsThickening B S hS U'sp (G.preimage U'.ι) :=
    isThickening_preimage B S hS G (ObjectProperty.homMk U'.ι : U'sp ⟶ X) hG
  subst hUeq
  have h₁ := Subfunctor.isPullback_preimage G.ι U'
  have h₂ := Subfunctor.isPullback_preimage U'.ι G
  exact C1573.isAffineSpace_of_isThickening B S hS hT
    (hUa.of_iso (h₁.flip.isoIsPullback _ _ h₂))

/-- The reduction of an algebraic space is a thickening of it: a closed subspace containing every
point. -/
theorem isThickening_reduction (X : AlgebraicSpaces B S hS) :
    IsThickening B S hS X (reduction B S hS X.1 X.2) :=
  ⟨isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 Set.univ
      (@isClosed_univ _ (pointTopology B S hS X.1)),
    surjective_pointsMap_ι_reduction B S hS X.1 X.2⟩

end AlgebraicGeometry.Space

end
