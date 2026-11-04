module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# A closed subspace of finite presentation of a relative Proj, read on a scheme chart

In Situation 0849 let `i : Z ⟶ Proj_X(𝒜)` be a closed immersion locally of finite presentation.
For an étale scheme point `f : T ⟶ X` of the base the closed subscheme
`Z ×_X T ⊆ Proj_T(𝒜|_T)` (`AlgebraicGeometry.Space.RelativeProjSituation.chartClosedSubscheme`)
is locally of finite presentation: it is the base change of `i` along the étale morphism
`Proj_T(𝒜|_T) ⟶ Proj_X(𝒜)`, read on étale charts.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.locallyOfFinitePresentation_chartClosedSubscheme`

## References

* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 085M](https://stacks.math.columbia.edu/tag/085M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable {s : RelativeProjSituation.{u, u}} {Z : AlgebraicSpaces s.site s.base s.containsBase}
  (i : Z ⟶ s.Proj) (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)

/-- **The base change of a closed subspace locally of finite presentation to an étale scheme
point is locally of finite presentation.** -/
theorem locallyOfFinitePresentation_chartClosedSubscheme
    (hfp : IsLocallyOfFinitePresentation s.site s.base s.containsBase i.hom)
    (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)
    (hfE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase))) f) :
    LocallyOfFinitePresentation (chartClosedSubscheme i hi T f) := by
  set g := s.relativeProjPoints.fibreToSpace T f
  have hst := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme s.site s.base s.containsBase))
  have hgE := hst.of_isPullback (s.relativeProjPoints.isPullback T f).flip hfE
  let Z₁ := closedSubspaceOfIsClosedImmersion _ _ _ i hi
  let R := Z₁.2.2.rep
  have : Mono i.hom := mono_of_isClosedImmersion _ _ _ i.hom hi
  let e : (Subfunctor.range i.hom).toFunctor ≅ Z.1 := (asIso (Subfunctor.toRange i.hom)).symm
  let a : yoneda.obj (R.pullback g) ⟶ Z.1 := R.fst g ≫ e.hom
  have hsq : IsPullback a (yoneda.map (R.snd g)) i.hom g := by
    refine IsPullback.of_iso (R.isPullback g) (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [a]
    · simp
    · show Z₁.1.ι ≫ 𝟙 _ = e.hom ≫ i.hom
      rw [Category.comp_id]
      exact ((asIso (Subfunctor.toRange i.hom)).eq_inv_comp).2 (Subfunctor.toRange_ι i.hom)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  have haE := hst.of_isPullback hsq.flip hgE
  unfold chartClosedSubscheme
  have : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map (R.snd g)) :=
    hfp _ _ a g (R.snd g) haE hgE hsq.w.symm
  infer_instance

end AlgebraicGeometry.Space.RelativeProjSituation

end
