module

public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceConstruction

/-!
# Existence of the normalizations in Stacks 0BBG

A decent algebraic space over a scheme `S` whose space of points has finitely many irreducible
components has a normalization. Together with the commutative square and the birationality of
`StacksFrontier.AlgebraicGeometry.Spaces.BirationalNormalization`, which hold for given
normalizations, this gives the whole of **Stacks 0BBG**, with the two normalizations produced
rather than assumed.

## Main results

* `AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isDecentSpace`: a decent
  algebraic space with finitely many irreducible components satisfies the equivalent
  conditions of Stacks 0BB1, by Stacks 0BB9.
* `AlgebraicGeometry.Space.nonempty_normalizationData_of_isDecentSpace`: the first clause of
  **Stacks 0BBG**, that such a space has a normalization.
* `AlgebraicGeometry.Space.exists_normalizationData_isBirational_lift_of_isBirational` is
  **Stacks 0BBG**: the normalizations exist, the square commutes and the induced morphism is
  birational, with no normalization assumed.

## References

* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 0BB9](https://stacks.math.columbia.edu/tag/0BB9)
* [Stacks Project, Tag 0BBG](https://stacks.math.columbia.edu/tag/0BBG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A decent algebraic space over `S` with finitely many irreducible components satisfies the
finiteness condition of Stacks 0BB1:** every quasi-compact open of every étale scheme chart of
it has finitely many irreducible components. -/
theorem hasLocallyFiniteIrreducibleComponents_of_isDecentSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hFdec : IsDecentSpace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite)) :
    HasLocallyFiniteIrreducibleComponents B S hS F := by
  have hetale : HasFiniteEtaleIrreducibleComponents B S hS F :=
    ((IsDecentWithFinitelyManyComponents.hasQuasiCompactGenericDenseOpenScheme B S hS hF
      ⟨hFdec, hfinite⟩).hasFiniteEtaleComponentsAndCodimensionZeroPoints B S hS hF).1
  refine (hasLocallyFiniteIrreducibleComponents_iff_finite_irreducibleComponents B S hS).2 ?_
  intro G hG hqc g hg
  obtain ⟨U, v, hUcompact, hvSurj, hvEtale⟩ := hqc
  exact (ncard_irreducibleComponents_le_of_surjective
    (pointsMap B S hS (yoneda.obj U) v ∘ (schemePointsHomeomorph B S hS U).symm)
    ((continuous_pointsMap B S hS v).comp (schemePointsHomeomorph B S hS U).symm.continuous)
    (((surjective_iff_surjective_pointsMap B S hS G hG U v).mp hvSurj).comp
      (schemePointsHomeomorph B S hS U).symm.surjective)
    (hetale U (v ≫ g) hUcompact (isEtale_comp B S hS hvEtale hg))).1

/-- **Stacks 0BBG, the existence of the normalizations.** A decent algebraic space over `S`
whose space of points has finitely many irreducible components has normalization data: an
algebraic space `F^ν` over `S` with a morphism `F^ν ⟶ F` whose base change along every
surjective étale scheme chart of `F` is the normalization of that chart.

This is the first clause of Stacks 0BBG, and the source proves it the same way: the hypotheses
give the equivalent conditions of Stacks 0BB1 by Stacks 0BB9
(`AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isDecentSpace`), and under
those conditions the normalization exists by the existence half of Stacks 07U4,
`AlgebraicGeometry.Space.nonempty_normalizationData`. Applied to the source and the target of
a birational morphism it is the assertion that `X^ν ⟶ X` and `Y^ν ⟶ Y` exist. -/
@[stacks 0BBG "the existence of the normalizations"]
theorem nonempty_normalizationData_of_isDecentSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hFdec : IsDecentSpace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite)) :
    Nonempty (NormalizationData B S hS F) :=
  nonempty_normalizationData B S hS hF
    (hasLocallyFiniteIrreducibleComponents_of_isDecentSpace B S hS hF hFdec hfinite)

/-- **Stacks 0BBG.** Let `f : X ⟶ Y` be a birational morphism between algebraic spaces over
`S` which are decent and have finitely many irreducible components. Then the normalizations
`X^ν ⟶ X` and `Y^ν ⟶ Y` exist and there is a commutative diagram with rows `X^ν ⟶ Y^ν` and
`X ⟶ Y` and columns the two normalization morphisms, and the morphism `X^ν ⟶ Y^ν` is
birational.

Nothing is assumed about the normalizations: they are produced by
`AlgebraicGeometry.Space.nonempty_normalizationData_of_isDecentSpace` from decency and the
finiteness of the irreducible components, which is the source's own route through Stacks 0BB9
and Stacks 0BB1. The square is then
`AlgebraicGeometry.Space.existsUnique_lift_normalization_of_isBirational` and the
birationality of the morphism closing it is
`AlgebraicGeometry.Space.isBirational_lift_normalization_of_isBirational`, both of which hold
for an arbitrary choice of the two normalizations.

The decency of `X^ν` and `Y^ν` and the finiteness of their irreducible components, which the
conclusion's `AlgebraicGeometry.Space.IsBirational` is parameterised by, are
`AlgebraicGeometry.Space.NormalizationData.isDecentSpace` and
`AlgebraicGeometry.Space.NormalizationData.finite_irreducibleComponents`; the source records
them in its second paragraph, citing Stacks 0ABT. -/
@[stacks 0BBG]
theorem exists_normalizationData_isBirational_lift_of_isBirational
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hXdec hYdec hfiniteX hfiniteY f) :
    ∃ (DX : NormalizationData B S hS X) (DY : NormalizationData B S hS Y)
      (g : DX.space ⟶ DY.space), g ≫ DY.hom = DX.hom ≫ f ∧
        IsBirational B S hS DX.isAlgebraicSpace DY.isAlgebraicSpace
          (DX.isDecentSpace hX hXdec) (DY.isDecentSpace hY hYdec)
          (DX.finite_irreducibleComponents hX hXdec hfiniteX)
          (DY.finite_irreducibleComponents hY hYdec hfiniteY) g := by
  obtain ⟨DX⟩ := nonempty_normalizationData_of_isDecentSpace B S hS hX hXdec hfiniteX
  obtain ⟨DY⟩ := nonempty_normalizationData_of_isDecentSpace B S hS hY hYdec hfiniteY
  obtain ⟨g, hg, hgbir⟩ := exists_isBirational_lift_normalization_of_isBirational
    B S hS hX hY hXdec hYdec hfiniteX hfiniteY DX DY hf
  exact ⟨DX, DY, g, hg, hgbir⟩

end AlgebraicGeometry.Space

end
