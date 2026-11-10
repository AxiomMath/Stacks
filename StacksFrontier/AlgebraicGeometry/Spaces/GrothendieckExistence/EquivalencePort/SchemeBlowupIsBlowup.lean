module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupDivisorPullback
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartRees
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationTransitivity
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCentreCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSubschemeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Morphisms.SchemeTheoreticImageRepresented

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573
namespace AlgebraicGeometry.Space.IsBlowupAlong.C1573
end AlgebraicGeometry.Space.IsBlowupAlong.C1573

/-!
# The blowup of an affine Noetherian scheme is its blowup as an algebraic space

Let `V` be an affine, locally Noetherian scheme of the big fppf site over `S` and let `Z` be a
closed subspace of the algebraic space it represents. The blowup of the scheme `V` in the ideal
of `Z`, `AlgebraicGeometry.blowUp`, is again an object of the site, and the algebraic space it
represents is the blowup of the algebraic space of `V` in `Z`, in the sense of the universal
property of Stacks 085U.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `C1573.contains_relativeProj_reesSituation_of_contains_of_isLocallyNoetherian`:
  the relative `Proj` of the Rees algebra of an ideal sheaf of a locally Noetherian scheme of the
  site lies in the site.
* `IsBlowupAlong.C1573.isIso_of_comp_eq`: a morphism over the base between
  two blowups in the same centre is an isomorphism.
* `C1573.exists_isBlowupAlong_reesProjChart`: the statement above.
* `C1573.exists_idealSheafData_subschemePoints_eq`: every closed subspace of
  the algebraic space of a scheme is the closed subspace of a closed subscheme.
* `C1573.exists_isBlowupAlong_blowUp`: the same for the blowup
  `AlgebraicGeometry.blowUp J` of the scheme `V` in a quasi-coherent ideal `J`, the centre being
  the closed subspace whose points are those of the closed subscheme `V(J)`.

## References

* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The relative `Proj` of the Rees algebra of an ideal sheaf of a locally Noetherian scheme of
the site lies in the site: it is isomorphic to the blowup, which is proper, in particular of
finite type and quasi-compact, over the base. -/
theorem C1573.contains_relativeProj_reesSituation_of_contains_of_isLocallyNoetherian
    {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (hY : B.Contains Y) (I : Y.IdealSheafData) :
    B.Contains (Stacks.Blowup.reesSituation I).relativeProj := by
  have : _root_.AlgebraicGeometry.IsProper (AlgebraicGeometry.blowUpToBase I) :=
    AlgebraicGeometry.isProper_blowUpToBase I
  have hb : B.Contains (AlgebraicGeometry.blowUp I) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (AlgebraicGeometry.blowUpToBase I) hY
  change (Stacks.Blowup.reesSituation I).relativeProj.size < B.cutoff
  rw [Scheme.size_congr (Stacks.Blowup.reesSituationBlowUpIso I)]
  exact hb

/-- **A morphism over the base between two blowups in the same centre is an isomorphism.** -/
theorem IsBlowupAlong.C1573.isIso_of_comp_eq {X X' X'' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} {b' : X'' ⟶ X}
    (hb : IsBlowupAlong B S hS Z b) (hb' : IsBlowupAlong B S hS Z b') (f : X'' ⟶ X')
    (hf : f ≫ b = b') : IsIso f := by
  obtain ⟨g, hg, -⟩ := hb'.existsUnique_lift b hb.isPullbackDefined
  have h1 : f ≫ g = 𝟙 _ := by
    obtain ⟨l, -, hlu⟩ := hb'.existsUnique_lift b' hb'.isPullbackDefined
    rw [hlu (f ≫ g) (by change (f ≫ g) ≫ b' = b'; rw [Category.assoc, hg, hf]),
      hlu (𝟙 _) (Category.id_comp _)]
  have h2 : g ≫ f = 𝟙 _ := by
    obtain ⟨l, -, hlu⟩ := hb.existsUnique_lift b hb.isPullbackDefined
    rw [hlu (g ≫ f) (by change (g ≫ f) ≫ b = b; rw [Category.assoc, hf, hg]),
      hlu (𝟙 _) (Category.id_comp _)]
  exact ⟨g, h1, h2⟩

/-- The scheme underlying an object of the site lies in the site. -/
theorem C1573.contains_toScheme_obj (V : BigFppfOver B S hS) :
    B.Contains ((BigFppfOver.toScheme B S hS).obj V) :=
  V.left.property

/-- The subobject of a scheme cut out by an ideal sheaf is an immersion. -/
private theorem isImmersion_mk_subschemeι {X : Scheme.{u}} (J : X.IdealSheafData) :
    _root_.AlgebraicGeometry.IsImmersion (Subobject.mk J.subschemeι).arrow := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

/-- The morphism of the site induced by the immersed subobject cut out by `J` maps to the
closed immersion `J.subschemeι`, up to the canonical isomorphism. -/
private theorem toScheme_map_homMk_preimage_arrow (V : BigFppfOver B S hS)
    (J : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)
    (himm : _root_.AlgebraicGeometry.IsImmersion (Subobject.mk J.subschemeι).arrow) :
    (BigFppfOver.toScheme B S hS).map
      (Over.homMk (B.inclusion.preimage
        (X := B.obj (site_contains_underlying_of_isImmersion B V.left.property _ himm))
        (Y := V.left) (Subobject.mk J.subschemeι).arrow) :
          siteObjectOfImmersedSubobject B S hS _ himm ⟶ V) =
      (Subobject.underlyingIso J.subschemeι).hom ≫ J.subschemeι := by
  change B.inclusion.map (B.inclusion.preimage
    (X := B.obj (site_contains_underlying_of_isImmersion B V.left.property _ himm))
    (Y := V.left) (Subobject.mk J.subschemeι).arrow) = _
  rw [Functor.map_preimage, Subobject.underlyingIso_hom_comp_eq_mk]

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The blowup of a locally Noetherian scheme of the site, as an algebraic space.** Let `V` be
a locally Noetherian scheme of the site and `Z` a closed subspace of the algebraic space it
represents. Then the relative `Proj` `P_V` of the Rees algebra of the ideal sheaf of `Z` on `V`
lies in the site, and the algebraic space it represents is the blowup of `V` in `Z`. -/
theorem C1573.exists_isBlowupAlong_reesProjChart (V : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (Z : ClosedSubspaces B S hS (schemeSpace V).obj) :
    ∃ hcU : B.Contains (reesChartSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) (selfPresentation B S hS V)).relativeProj,
      IsBlowupAlong B S hS Z
        (schemeSpaceMap (reesProjChartHom (centreIdeal Z)
          (isCartesianOnAffineCharts_centreIdeal Z) (selfPresentation B S hS V) hcU)) := by
  have hRR : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      (presentationDouble (selfPresentation B S hS V))) := by
    have := etale_toScheme_map_presentationDoubleRho (selfPresentation B S hS V)
    exact LocallyOfFiniteType.isLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst (selfPresentation B S hS V) ≫
        (selfPresentation B S hS V).source))
  have hcU := contains_relativeProj_reesSituation_of_contains_of_isLocallyNoetherian
    (contains_toScheme_obj V)
    (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
      (selfPresentation B S hS V))
  have hcR := contains_relativeProj_reesSituation_of_contains_of_isLocallyNoetherian
    (contains_toScheme_obj V)
    (reesRelationIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
      (selfPresentation B S hS V))
  have hcRR := contains_relativeProj_reesSituation_of_contains_of_isLocallyNoetherian
    (contains_toScheme_obj (presentationDouble (selfPresentation B S hS V)))
    (reesDoubleIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
      (selfPresentation B S hS V))
  refine ⟨hcU, ?_⟩
  have hbV := isBlowupAlong_blowUpAlongHom' Z (selfPresentation B S hS V) hcU hcR hcRR
  have hid : preimageClosedSubspace (𝟙 (schemeSpace V)) Z = Z := rfl
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_reesProjChart_of_isEtale (Z := Z) hbV V
    (a := 𝟙 (schemeSpace V)) (isEtale_of_isIso B S hS (𝟙 (yoneda.obj V))) hcU hcR hcRR
    (IsPullback.of_id_snd (f := blowUpAlongHom' Z (selfPresentation B S hS V) hcU hcR hcRR))
  have key : schemeSpaceMap (reesProjChartHom (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) (selfPresentation B S hS V) hcU) =
      e.inv ≫ blowUpAlongHom' Z (selfPresentation B S hS V) hcU hcR hcRR := by
    rw [← he, Iso.inv_hom_id_assoc]
    rfl
  rw [key]
  exact hbV.of_iso_over e.symm

/-- **The blowup of a locally Noetherian scheme of the site in an ideal sheaf is its blowup as
an algebraic space.** Let `V` be a locally Noetherian scheme of the site, `J` a quasi-coherent
ideal on it and `Z` the closed subspace of the algebraic space of `V` whose points are those of
the closed subscheme `V(J)`. Then the blowup `AlgebraicGeometry.blowUp J` is, up to an isomorphism
over `V`, an object of the site whose algebraic space is the blowup of `V` in `Z`. -/
theorem C1573.exists_isBlowupAlong_blowUp (V : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (J : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)
    (Z : ClosedSubspaces B S hS (schemeSpace V).obj)
    (hZ : Z.1 = subschemePoints B S hS (Subobject.mk J.subschemeι)) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ V)
      (e : (BigFppfOver.toScheme B S hS).obj W ≅ AlgebraicGeometry.blowUp J),
      e.hom ≫ AlgebraicGeometry.blowUpToBase J = (BigFppfOver.toScheme B S hS).map p ∧
        IsBlowupAlong B S hS Z (schemeSpaceMap p) := by
  obtain ⟨hcU, hb⟩ := exists_isBlowupAlong_reesProjChart V Z
  -- the chart ideal of the centre is `J`
  have himm := isImmersion_mk_subschemeι J
  have hJ : reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
      (selfPresentation B S hS V) = J := by
    rw [← ker_rep_snd_eq_reesChartIdeal]
    refine (ker_eq_iff_exists_closedSubschemePresentation B S hS (schemeSpace V) Z V
      (𝟙 (yoneda.obj V)) J).2 ⟨siteObjectOfImmersedSubobject B S hS _ himm, _,
        Subobject.underlyingIso J.subschemeι, toScheme_map_homMk_preimage_arrow V J himm, ?_⟩
    exact hZ.trans (subschemePoints_eq_range_of_isImmersion B S hS _ himm)
  subst hJ
  exact ⟨reesProjChart (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
      (selfPresentation B S hS V) hcU,
    reesProjChartHom (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
      (selfPresentation B S hS V) hcU,
    Stacks.Blowup.reesSituationBlowUpIso _,
    Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase _, hb⟩

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **A closed subspace of the algebraic space of a scheme is a closed subscheme**: its points
are those of `V(J)` for a quasi-coherent ideal `J`, the kernel ideal sheaf of a represented
closed immersion onto it. -/
theorem C1573.exists_idealSheafData_subschemePoints_eq (V : BigFppfOver B S hS)
    (Z : ClosedSubspaces B S hS (schemeSpace V).obj) :
    ∃ J : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData,
      Z.1 = subschemePoints B S hS (Subobject.mk J.subschemeι) := by
  obtain ⟨R, j, hj, hZ⟩ := exists_closedImmersion_range B S hS Z.1 Z.2
  have := hj
  set J := ((BigFppfOver.toScheme B S hS).map j).ker
  have himm := isImmersion_mk_subschemeι J
  refine ⟨J, ?_⟩
  rw [subschemePoints_eq_range_of_isImmersion B S hS _ himm, hZ]
  set j' : siteObjectOfImmersedSubobject B S hS _ himm ⟶ V :=
    Over.homMk (B.inclusion.preimage
      (X := B.obj (site_contains_underlying_of_isImmersion B V.left.property _ himm))
      (Y := V.left) (Subobject.mk J.subschemeι).arrow) with hj'
  have hj'map := toScheme_map_homMk_preimage_arrow V J himm
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j') := by
    rw [hj'map]; infer_instance
  have hker : ((BigFppfOver.toScheme B S hS).map j').ker = J := by
    rw [hj'map, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]
  exact le_antisymm ((range_yoneda_map_le_iff_ker_le _ _ _ j' j inferInstance).2 hker.le)
    ((range_yoneda_map_le_iff_ker_le _ _ _ j j' inferInstance).2 hker.ge)

end AlgebraicGeometry.Space

end
