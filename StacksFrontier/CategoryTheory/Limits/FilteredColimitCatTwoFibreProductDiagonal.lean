module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProductComparison
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackDiagonalMap

/-!
# The colimit of the stagewise diagonal is the diagonal of the colimit

Let `α : X ⟶ Y` be a morphism of diagrams of categories indexed by `J`. Its stagewise diagonal
`Δ_j : X j ⥤ X j ×_{Y j} X j` assembles into a morphism of diagrams
`X ⟶ CategoryTheory.Cat.twoFibreProductDiagram α α`, strictly and not merely up to isomorphism:
on an object `x` of a stage both composites in the naturality square give the triple
`(x, x, 𝟙)` transported to the later stage, and the two transports the stagewise 2-fibre product
inserts are mutually inverse because the two components coincide.

Taking colimits and composing with the comparison
`CategoryTheory.Cat.colimitTwoFibreProductComparison` recovers the diagonal of `colimMap α` on the
nose. The proof of Stacks 0CMW uses this to recognise the colimit of the diagonals of the stage
fibres inside the 2-fibre product of the colimits. No filteredness of `J` is assumed: only the
universal property of the colimit is used.

## Main definitions

* `CategoryTheory.Cat.twoFibreProductDiagonalDiagram`: the stagewise diagonal, as a morphism of
  diagrams.

## Main results

* `CategoryTheory.Cat.twoFibreProductDiagonalDiagram_naturality`: the stagewise diagonal is
  strictly natural in the stage.
* `CategoryTheory.Cat.colimMap_twoFibreProductDiagonalDiagram_comp_comparison`: the colimit of
  the stagewise diagonal, followed by the comparison into the 2-fibre product of the colimits,
  is the diagonal of `colimMap α`.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Cat

universe t v w

variable {J : Type v} [Category.{w} J] {X Y : J ⥤ Cat.{t, t}} (α : X ⟶ Y)

/-- The stagewise diagonal is strictly natural in the stage: for `s : j ⟶ k`, the transition
functor `X.map s` followed by the diagonal of `α.app k` equals the diagonal of `α.app j` followed
by the transition functor `twoFibreProductMap α α s` of the stagewise 2-fibre product. -/
lemma twoFibreProductDiagonalDiagram_naturality {j k : J} (s : j ⟶ k) :
    (X.map s).toFunctor ⋙ CategoricalPullback.diagonal (α.app k).toFunctor =
      CategoricalPullback.diagonal (α.app j).toFunctor ⋙ twoFibreProductMap α α s :=
  (CategoricalPullback.diagonal_comp_map (α.app j).toFunctor (α.app k).toFunctor
    (X.map s).toFunctor (Y.map s).toFunctor (naturality_toFunctor α s)).symm

/-- The stagewise diagonal of `α`, as a morphism of diagrams from `X` to the stagewise 2-fibre
product of `α` with itself; its component at a stage is the diagonal of the component of `α`. -/
noncomputable def twoFibreProductDiagonalDiagram : X ⟶ twoFibreProductDiagram α α where
  app j := (CategoricalPullback.diagonal (α.app j).toFunctor).toCatHom
  naturality _ _ s := Cat.Hom.ext (twoFibreProductDiagonalDiagram_naturality α s)

/-- The component of `twoFibreProductDiagonalDiagram α` at the stage `j` is the diagonal of
`α.app j`. -/
@[simp]
lemma twoFibreProductDiagonalDiagram_app (j : J) :
    ((twoFibreProductDiagonalDiagram α).app j).toFunctor =
      CategoricalPullback.diagonal (α.app j).toFunctor := rfl

variable [HasColimit X] [HasColimit Y]

/-- The diagonal of `α.app j` followed by the stagewise comparison `twoFibreProductStage α α j`
equals the colimit inclusion `colimit.ι X j` followed by the diagonal of `colimMap α`. -/
lemma diagonal_comp_twoFibreProductStage (j : J) :
    CategoricalPullback.diagonal (α.app j).toFunctor ⋙ twoFibreProductStage α α j =
      (colimit.ι X j).toFunctor ⋙
        CategoricalPullback.diagonal (colimMap α).toFunctor :=
  CategoricalPullback.diagonal_comp_map (α.app j).toFunctor (colimMap α).toFunctor
    (colimit.ι X j).toFunctor (colimit.ι Y j).toFunctor (ι_colimMap_toFunctor α j)

variable [HasColimit (twoFibreProductDiagram α α)]

/-- The colimit of the stagewise diagonal, followed by the comparison
`colimitTwoFibreProductComparison α α` into the 2-fibre product of the colimits, is the diagonal
of `colimMap α`. -/
lemma colimMap_twoFibreProductDiagonalDiagram_comp_comparison :
    (colimMap (twoFibreProductDiagonalDiagram α)).toFunctor ⋙
        colimitTwoFibreProductComparison α α =
      CategoricalPullback.diagonal (colimMap α).toFunctor := by
  obtain ⟨hd, hdf⟩ :
      Σ' hd : (colimit X : Cat.{t, t}) ⟶ (twoFibreProductCocone α α).pt,
        hd.toFunctor = CategoricalPullback.diagonal (colimMap α).toFunctor :=
    ⟨(CategoricalPullback.diagonal (colimMap α).toFunctor).toCatHom, rfl⟩
  have h : colimMap (twoFibreProductDiagonalDiagram α) ≫
      colimit.desc (twoFibreProductDiagram α α) (twoFibreProductCocone α α) = hd := by
    refine colimit.hom_ext fun j => ?_
    rw [← Category.assoc, ι_colimMap, Category.assoc, colimit.ι_desc]
    refine Cat.Hom.ext ?_
    rw [Cat.Hom.comp_toFunctor, Cat.Hom.comp_toFunctor,
      twoFibreProductDiagonalDiagram_app, hdf,
      show ((twoFibreProductCocone α α).ι.app j).toFunctor = twoFibreProductStage α α j from rfl]
    exact diagonal_comp_twoFibreProductStage α j
  have h₂ := congrArg Cat.Hom.toFunctor h
  rw [Cat.Hom.comp_toFunctor, hdf] at h₂
  exact h₂

end CategoryTheory.Cat

end
