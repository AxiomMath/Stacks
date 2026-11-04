module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart

/-!
# Reading the transcendence degree at a point off a single étale chart

The transcendence degree of a point of a morphism of algebraic spaces over its image, the third
of the three invariants of Stacks 04NM, is defined by the germ property of Tag 04NK holding in
every pointed pair of étale charts at the point. This file reads it off one chart, as the
residue field transcendence degree of the chart morphism at the chart point.

## Main results

* `AlgebraicGeometry.MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom` and
  `AlgebraicGeometry.MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff`: the
  germ morphism induced by a morphism of schemes `f` at `x` has residue-field transcendence
  degree the transcendence degree of the residue field extension of `f` at `x`.
* `AlgebraicGeometry.Space.hasTranscendenceDegreeAt_iff_of_chart` and
  `AlgebraicGeometry.Space.hasTranscendenceDegreeAt_pointsMap_iff`: the transcendence degree at
  a point of a morphism of algebraic spaces is the residue field transcendence degree of the
  chart morphism of any pointed étale chart at the point.

## References

* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04NK](https://stacks.math.columbia.edu/tag/04NK)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.MorphismOfGerms

/-- Restricting the source of a morphism of schemes along an open immersion does not change the
transcendence degree of the residue field extension at a point. -/
private theorem trdeg_residueField_comp_isOpenImmersion {X Y Z : Scheme.{u}} (j : Z ⟶ X)
    [IsOpenImmersion j] (f : X ⟶ Y) (z : Z) :
    letI : Algebra (Y.residueField (f (j z))) (X.residueField (j z)) :=
      (f.residueFieldMap (j z)).hom.toAlgebra
    letI : Algebra (Y.residueField (f (j z))) (Z.residueField z) :=
      ((j ≫ f).residueFieldMap z).hom.toAlgebra
    Algebra.trdeg (Y.residueField (f (j z))) (Z.residueField z) =
      Algebra.trdeg (Y.residueField (f (j z))) (X.residueField (j z)) := by
  let _ : Algebra (Y.residueField (f (j z))) (X.residueField (j z)) :=
    (f.residueFieldMap (j z)).hom.toAlgebra
  let _ : Algebra (Y.residueField (f (j z))) (Z.residueField z) :=
    ((j ≫ f).residueFieldMap z).hom.toAlgebra
  let e : Z.residueField z ≃ₐ[Y.residueField (f (j z))] X.residueField (j z) :=
    { toRingEquiv := (asIso (j.residueFieldMap z)).commRingCatIsoToRingEquiv.symm
      commutes' := fun k ↦ by
        have h : (j.residueFieldMap z).hom ((f.residueFieldMap (j z)).hom k) =
            ((j ≫ f).residueFieldMap z).hom k :=
          congrArg (fun m : CommRingCat.Hom _ _ ↦ m.hom k)
            (Scheme.residueFieldMap_comp j f z).symm
        exact h ▸ (asIso (j.residueFieldMap z)).commRingCatIsoToRingEquiv.symm_apply_apply
          ((f.residueFieldMap (j z)).hom k) }
  exact e.trdeg_eq

/-- **Stacks 04NK for the germ of a morphism of schemes.** The germ morphism induced by `f` at
`x` has residue-field transcendence degree the transcendence degree of the residue field of `X`
at `x` over the residue field of `Y` at `f x`. -/
public theorem hasResidueFieldTranscendenceDegree_ofSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    HasResidueFieldTranscendenceDegree
      (Cardinal.toENat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)))
      (ofSchemeHom f x) := by
  refine ⟨{ source := ⊤
            mem_source := by simp
            hom := X.topIso.hom ≫ f
            map_point := rfl }, rfl, ?_⟩
  exact congrArg Cardinal.toENat
    (trdeg_residueField_comp_isOpenImmersion X.topIso.hom f (⟨x, by simp⟩ : (⊤ : X.Opens)))

/-- **Stacks 04NK read off a morphism of schemes.** The germ morphism induced by `f` at `x` has
residue-field transcendence degree `r` exactly when the residue field extension of `f` at `x`
has transcendence degree `r`. -/
public theorem hasResidueFieldTranscendenceDegree_ofSchemeHom_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (r : ℕ∞) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    HasResidueFieldTranscendenceDegree r (ofSchemeHom f x) ↔
      Cardinal.toENat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) = r := by
  let _ : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  exact ⟨fun h ↦ hasResidueFieldTranscendenceDegree_unique
      (hasResidueFieldTranscendenceDegree_ofSchemeHom f x) h,
    fun h ↦ h ▸ hasResidueFieldTranscendenceDegree_ofSchemeHom f x⟩

end AlgebraicGeometry.MorphismOfGerms

namespace AlgebraicGeometry.Space

open CategoryTheory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The chart equation for Tag 04NM, transcendence degree at a point.** The transcendence
degree of a point of a morphism of algebraic spaces over its image is `r` exactly when the
residue field extension of the chart morphism of one pointed étale chart has transcendence
degree `r` at the chart point. -/
theorem hasTranscendenceDegreeAt_iff_of_chart (r : ℕ∞) (f : F ⟶ G) (x : points B S hS F)
    (c : EtaleChartAtPoint B S hS f x) :
    HasTranscendenceDegreeAt B S hS f x r ↔
      letI := (((BigFppfOver.toScheme B S hS).map c.h).residueFieldMap
        (c.sourcePoint B S hS)).hom.toAlgebra
      Cardinal.toENat (Algebra.trdeg
          (((BigFppfOver.toScheme B S hS).obj c.V).residueField
            ((BigFppfOver.toScheme B S hS).map c.h (c.sourcePoint B S hS)))
          (((BigFppfOver.toScheme B S hS).obj c.U).residueField (c.sourcePoint B S hS))) = r := by
  have key := MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff
    ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS) r
  exact ⟨fun hall ↦ key.mp (hall c), fun hc d ↦ (chart_property_iff_of_pointedCharts B S hS
    (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r)
    (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget r)
    f x c d).mp (key.mpr hc)⟩

/-- **The chart equation for Tag 04NM at a point of the chart.** For a commuting square of étale
charts and a point `u` of the source chart, the transcendence degree of the point of the space
below `u` over its image is `r` exactly when the residue field extension of the chart morphism
at `u` has transcendence degree `r`. -/
theorem hasTranscendenceDegreeAt_pointsMap_iff (r : ℕ∞) (f : F ⟶ G)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ f)
    (u : (BigFppfOver.toScheme B S hS).obj U) :
    HasTranscendenceDegreeAt B S hS f
        (pointsMap B S hS (yoneda.obj U) a ((pointsEquivScheme B S hS U).symm u)) r ↔
      letI := (((BigFppfOver.toScheme B S hS).map h).residueFieldMap u).hom.toAlgebra
      Cardinal.toENat (Algebra.trdeg
          (((BigFppfOver.toScheme B S hS).obj V).residueField
            ((BigFppfOver.toScheme B S hS).map h u))
          (((BigFppfOver.toScheme B S hS).obj U).residueField u)) = r := by
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS U u
  have hclass : (pointsEquivScheme B S hS U).symm u = p.class B S hS (yoneda.obj U) :=
    (Equiv.symm_apply_eq _).mpr hp.symm
  rw [hclass, hasTranscendenceDegreeAt_iff_of_chart B S hS r f _
    (EtaleChartAtPoint.ofFieldValuedPoint B S hS f U V a b h ha hb hcomm p),
    EtaleChartAtPoint.sourcePoint_ofFieldValuedPoint, hp]
  exact Iff.rfl

end AlgebraicGeometry.Space

end
