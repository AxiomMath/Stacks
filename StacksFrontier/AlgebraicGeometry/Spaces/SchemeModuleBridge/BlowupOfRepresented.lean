module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartRees
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupSecondCentreChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.BlowupRepresentable

/-!
# Blowups of the algebraic space of a scheme

Let `V` be a scheme of the big fppf site and `I` an ideal sheaf on `V` whose closed subscheme is
of finite presentation.  A blowup of the algebraic space of `V` in the closed subspace
`AlgebraicGeometry.Space.closedSubspaceOfIdeal V I` cut out by `I`, in the sense of the universal
property of Stacks 085U, is, over `V`, the algebraic space of the scheme blowup
`AlgebraicGeometry.Space.blowUpObj V I` of `V` in `I`.  No affineness is asked of `V`.

## Main results

* `AlgebraicGeometry.Space.ker_rep_snd_of_preimage_eq_closedSubspaceOfIdeal`: on a chart along
  which a closed subspace pulls back to the closed subspace cut out by `I`, the ideal sheaf it
  induces is `I`.
* `AlgebraicGeometry.Space.exists_iso_yoneda_blowUpObj_of_isBlowupAlong`: every blowup of the
  algebraic space of `V` in the closed subspace cut out by `I` is, over `V`, the algebraic space
  of the scheme blowup of `V` in `I`.

## Implementation notes

The blowup comparison is Stacks 085R for the identity chart of `V`,
`AlgebraicGeometry.Space.exists_iso_schemeSpace_reesProjChart_of_isEtale`: the base change of a
blowup to the identity chart is the blowup itself, and it is the relative `Proj` of the Rees
algebra of the ideal sheaf the centre induces on the chart.  That ideal sheaf is the kernel of
the base change of the centre to the chart, which is `I` because the base change has the same
image as the closed immersion of the closed subscheme of `I`.  The relative `Proj` of the Rees
algebra is the scheme blowup by `Stacks.Blowup.reesSituationBlowUpIso`.  For affine `V` the
same comparison is `AlgebraicGeometry.Space.exists_iso_schemeSpace_blowUpObj`, which asks no
finite presentation of the centre.

## References

* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Subscheme

variable (V : BigFppfOver B S hS) (I : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)

/-- **The ideal sheaf induced on a chart by a closed subspace whose preimage there is cut out by
`I` is `I`.**  For a closed subspace `Z` of an algebraic space `X` and a morphism
`c : V ⟶ X` from the space of `V` along which `Z` pulls back to the closed subspace cut out by
`I`, the kernel of the base change of `Z` along `c` is `I`. -/
theorem ker_rep_snd_of_preimage_eq_closedSubspaceOfIdeal {X : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1) (c : yoneda.obj V ⟶ X.1)
    (hZ : Z.1.preimage c = (closedSubspaceOfIdeal V I).1) :
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd c)).ker = I := by
  have hr : Subfunctor.range (yoneda.map (Z.2.2.rep.snd c)) =
      Subfunctor.range (yoneda.map (closedSubschemeOverι B S hS V I)) :=
    (range_yoneda_snd_eq_preimage B S hS c Z.2.2.rep).trans hZ
  have hq : ((BigFppfOver.toScheme B S hS).map (closedSubschemeOverι B S hS V I)).ker = I := by
    rw [toScheme_map_closedSubschemeOverι]
    exact Scheme.IdealSheafData.ker_subschemeι I
  have : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd c)) :=
    Z.2.2.property_snd _
  rw [← hq]
  exact le_antisymm (ker_le_of_range_yoneda_map_le _ _ hr.ge)
    (ker_le_of_range_yoneda_map_le _ _ hr.le)

private theorem exists_blowUp_iso_of_eq {J : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData}
    (h : J = I) : ∃ e : AlgebraicGeometry.blowUp J ≅ AlgebraicGeometry.blowUp I,
      e.hom ≫ AlgebraicGeometry.blowUpToBase I = AlgebraicGeometry.blowUpToBase J := by
  subst h
  exact ⟨Iso.refl _, Category.id_comp _⟩

/-- **A blowup of the algebraic space of a scheme is the space of the scheme blowup.**  Let `V`
be a scheme of the site and `I` an ideal sheaf on it whose closed subscheme is of finite
presentation.  Every blowup `b : W' ⟶ V` of the algebraic space of `V` in the closed subspace cut
out by `I` is isomorphic, over `V`, to the algebraic space of the blowup of the scheme `V` in
`I`.

This is Stacks 085R for the identity chart of `V`: the base change of `b` to `V` is `b` itself,
the relative `Proj` of the Rees algebra of the ideal the centre induces on the chart, and that
ideal is `I`. -/
theorem exists_iso_yoneda_blowUpObj_of_isBlowupAlong (hI : FinitePresentation I.subschemeι)
    {W' : AlgebraicSpaces B S hS} {b : W' ⟶ schemeSpace V}
    (hb : IsBlowupAlong B S hS (closedSubspaceOfIdeal V I) b) :
    ∃ e : yoneda.obj (blowUpObj V I) ≅ W'.1,
      e.hom ≫ b.hom = yoneda.map (blowUpObjHom V I) := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  have hZ'fp : IsFinitePresentation B S hS
      (preimageClosedSubspace (𝟙 (schemeSpace V)) (closedSubspaceOfIdeal V I)).1.ι :=
    isFinitePresentation_closedSubspaceOfIdeal V I hI
  have hcU := contains_reesChartSituation_centreIdeal _ hZ'fp (selfPresentation B S hS V)
  have hcR := contains_reesRelationSituation_centreIdeal _ hZ'fp (selfPresentation B S hS V)
  have hcRR := contains_reesDoubleSituation_centreIdeal _ hZ'fp (selfPresentation B S hS V)
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_reesProjChart_of_isEtale hb V
    (a := 𝟙 (schemeSpace V)) (fun _ _ hφ => by simpa using hφ) hcU hcR hcRR
    (IsPullback.id_vert b)
  have hJ : reesChartIdeal (centreIdeal
      (preimageClosedSubspace (𝟙 (schemeSpace V)) (closedSubspaceOfIdeal V I)))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) = I := by
    have h1 := ker_rep_snd_eq_idealSheafDataOfChart B S hS (schemeSpace V)
      (preimageClosedSubspace (𝟙 (schemeSpace V)) (closedSubspaceOfIdeal V I))
      (presentationChart (selfPresentation B S hS V))
    have h2 := ker_rep_snd_of_preimage_eq_closedSubspaceOfIdeal V I
      (preimageClosedSubspace (𝟙 (schemeSpace V)) (closedSubspaceOfIdeal V I))
      (presentationChart (selfPresentation B S hS V)).1.hom rfl
    exact h1.symm.trans h2
  obtain ⟨κ₁, hκ₁⟩ := exists_blowUp_iso_of_eq V I hJ
  let κ := Stacks.Blowup.reesSituationBlowUpIso _ ≪≫ κ₁
  have hκ : κ.hom ≫ AlgebraicGeometry.blowUpToBase I = (BigFppfOver.toScheme B S hS).map
      (reesProjChartHom _ (isCartesianOnAffineCharts_centreIdeal _)
        (selfPresentation B S hS V) hcU) := by
    show ((Stacks.Blowup.reesSituationBlowUpIso _).hom ≫ κ₁.hom) ≫ _ = _
    rw [Category.assoc, hκ₁, Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase]
    rfl
  have hw := congrArg B.inclusion.map (Over.w (reesProjChartHom _
    (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU))
  rw [Functor.map_comp] at hw
  let κs : reesProjChart _ (isCartesianOnAffineCharts_centreIdeal _)
      (selfPresentation B S hS V) hcU ≅ blowUpObj V I :=
    Over.isoMk (ObjectProperty.isoMk _ κ) (by
      apply B.inclusion.map_injective
      rw [Functor.map_comp]
      show κ.hom ≫ AlgebraicGeometry.blowUpToBase I ≫ B.inclusion.map V.hom = _
      rw [← Category.assoc, hκ]
      exact hw)
  have hκs : κs.hom ≫ blowUpObjHom V I = reesProjChartHom _
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU :=
    (BigFppfOver.toScheme B S hS).map_injective ((Functor.map_comp _ _ _).trans hκ)
  let eF := (ObjectProperty.ι _).mapIso e.symm
  refine ⟨yoneda.mapIso κs.symm ≪≫ eF, ?_⟩
  have h1' : e.inv ≫ b = schemeSpaceMap (reesProjChartHom _
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU) := by
    rw [← he, Iso.inv_hom_id_assoc]
  have h1 : e.inv.hom ≫ b.hom = yoneda.map (reesProjChartHom _
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU) :=
    congrArg (fun k => k.hom) h1'
  show yoneda.map κs.inv ≫ (e.inv.hom ≫ b.hom) = _
  refine (congrArg (yoneda.map κs.inv ≫ ·) h1).trans ?_
  have h2 : κs.inv ≫ reesProjChartHom _ (isCartesianOnAffineCharts_centreIdeal _)
      (selfPresentation B S hS V) hcU = blowUpObjHom V I := by
    rw [← hκs, Iso.inv_hom_id_assoc]
  exact (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map h2)

end Subscheme

end AlgebraicGeometry.Space

end
