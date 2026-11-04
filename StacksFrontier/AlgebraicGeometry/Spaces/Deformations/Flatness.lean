module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.FlatDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Flatness along a flat deformation of algebraic spaces

In a flat deformation diagram of algebraic spaces, flatness of the morphism of special fibres
implies flatness of its ambient deformation, and the ambient target is then flat over the
ambient base at every point in the image of the ambient morphism.

## Main results

* `AlgebraicGeometry.Space.isFlat_of_flatDeformationDiagram`: flatness of the ambient morphism.
* `AlgebraicGeometry.Space.isFlatAt_target_of_flatDeformationDiagram`: flatness of the ambient
  target over the ambient base along the image.

## References

* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04ND](https://stacks.math.columbia.edu/tag/04ND)
* [Stacks Project, Tag 0CF3](https://stacks.math.columbia.edu/tag/0CF3)
* [Stacks Project, Tag 0CGW](https://stacks.math.columbia.edu/tag/0CGW)
* [Stacks Project, Tag 0CGX](https://stacks.math.columbia.edu/tag/0CGX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- In a flat deformation diagram of algebraic spaces, flatness of the morphism of special fibres
implies flatness of its ambient deformation. -/
@[stacks 0CGW "flatness of the ambient morphism"]
theorem isFlat_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS)
    (hf : IsFlat B S hS D.f.hom) : IsFlat B S hS D.f'.hom :=
  (isFlat_iff_of_flatDeformationDiagram B S hS D).mp hf

/-- In a flat deformation diagram of algebraic spaces whose morphism of special fibres is flat,
the ambient target is flat over the ambient base at every point in the image of the ambient
morphism. -/
@[stacks 0CGW "flatness of the ambient target over the ambient base along the image"]
theorem isFlatAt_target_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS)
    (hf : IsFlat B S hS D.f.hom) (x' : points B S hS D.X'.1) :
    IsFlatAt B S hS D.g'.hom (pointsMap B S hS D.X'.1 D.f'.hom x') := by
  classical
  let Tscheme := BigFppfOver.toScheme B S hS
  obtain ⟨U', qB', hqB'surj, hqB'etale⟩ := D.B'.property.exists_atlas
  obtain ⟨V', qY', α, hqYcomm, hqYsurj, hqYetale⟩ :=
    exists_surjective_etale_presentation_lift B S hS D.Y'.property D.B'.property D.g'.hom
      U' qB' hqB'surj hqB'etale
  obtain ⟨W', qX', β, hqXcomm, hqXsurj, hqXetale⟩ :=
    exists_surjective_etale_presentation_lift B S hS D.X'.property D.Y'.property D.f'.hom
      V' qY' hqYsurj hqYetale
  have hβα : yoneda.map (β ≫ α) ≫ qB' = qX' ≫ D.f'.hom ≫ D.g'.hom := by
    calc
      yoneda.map (β ≫ α) ≫ qB' = yoneda.map β ≫ yoneda.map α ≫ qB' := by
        rw [Functor.map_comp, Category.assoc]
      _ = (yoneda.map β ≫ qY') ≫ D.g'.hom := by rw [← hqYcomm, Category.assoc]
      _ = qX' ≫ D.f'.hom ≫ D.g'.hom := by rw [← hqXcomm, Category.assoc]
  have hftα : LocallyOfFiniteType (Tscheme.map α) :=
    D.finiteType_Y' V' U' qY' qB' α hqYetale hqB'etale hqYcomm.symm
  have hflatβα : Flat (Tscheme.map (β ≫ α)) :=
    D.flat_X' W' U' qX' qB' (β ≫ α) hqXetale hqB'etale hβα
  have hfpβα : LocallyOfFinitePresentation (Tscheme.map (β ≫ α)) :=
    D.finitePresentation_X' W' U' qX' qB' (β ≫ α) hqXetale hqB'etale hβα
  have hflatβ : Flat (Tscheme.map β) :=
    isFlat_of_flatDeformationDiagram B S hS D hf W' V' qX' qY' β hqXetale hqYetale hqXcomm.symm
  have hstalk : ∀ w : Tscheme.obj W',
      ((Tscheme.map α).stalkMap ((Tscheme.map β) w)).hom.Flat := by
    intro w
    have hi (X : Scheme.{u}) : Stacks.Thickenings.IsThickening (𝟙 X) :=
      ⟨inferInstance, fun z => ⟨z, rfl⟩⟩
    exact Stacks.Flatness.flat_stalkMap_of_flat_baseChange_thickening
      (𝟙 (Tscheme.obj W')) (𝟙 (Tscheme.obj V')) (𝟙 (Tscheme.obj U'))
      (Tscheme.map β) (Tscheme.map β) (Tscheme.map (β ≫ α)) (Tscheme.map (β ≫ α))
      (Tscheme.map α) (Tscheme.map α) (hi _) (hi _) (hi _) (by simp)
      (Tscheme.map_comp β α).symm (Tscheme.map_comp β α).symm
      IsPullback.of_id_fst IsPullback.of_id_fst hflatβ w
  obtain ⟨z, hz⟩ := (surjective_iff_pointsMap_surjective B S hS
    (isAlgebraicSpace_yoneda B S hS W') D.X'.property qX' hqXsurj.1).mp hqXsurj x'
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  let c : EtaleChartAtPoint B S hS D.g'.hom (pointsMap B S hS D.X'.1 D.f'.hom x') :=
    { U := V'
      V := U'
      a := qY'
      b := qB'
      h := α
      a_etale := hqYetale
      b_etale := hqB'etale
      comm := hqYcomm.symm
      representative := FieldValuedPoint.map B S hS (yoneda.obj W') (yoneda.map β) p
      point := ⟨⊥, inferInstance⟩
      maps_to := by
        have h1 : pointsMap B S hS (yoneda.obj V') qY'
            ((FieldValuedPoint.map B S hS (yoneda.obj W') (yoneda.map β) p).class B S hS
              (yoneda.obj V')) =
            pointsMap B S hS (yoneda.obj W') (yoneda.map β ≫ qY')
              (p.class B S hS (yoneda.obj W')) := by
          rw [pointsMap_comp]
          rfl
        rw [h1, ← hqXcomm, pointsMap_comp]
        exact congrArg (pointsMap B S hS D.X'.1 D.f'.hom) hz }
  refine (holdsOnEveryEtaleChartAtPoint_iff_some B S hS (@MorphismOfGerms.IsFlat.{u})
    MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat D.Y'.property D.B'.property
    D.g'.hom _).mpr ⟨c, ?_⟩
  have hpoint : c.sourcePoint B S hS =
      (Tscheme.map β) ((Tscheme.map p.value) (⟨⊥, inferInstance⟩ :
        Spec (.of p.carrier))) := by
    show (Tscheme.map (p.value ≫ β)) _ = _
    rw [Tscheme.map_comp]
    rfl
  rw [hpoint]
  exact (MorphismOfGerms.isFlat_ofSchemeHom_iff _ _).mpr (hstalk _)

end AlgebraicGeometry.Space

end
