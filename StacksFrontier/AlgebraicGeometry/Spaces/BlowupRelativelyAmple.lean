module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.BlowupRepresentableScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCentreCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdeal
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwist
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafUniqueness

/-!
# Blowups of algebraic spaces are representable

Let `X` be an algebraic space over a scheme `S`, let `Z ⊆ X` be a closed subspace whose closed
immersion is of finite presentation, and let `b : X' ⟶ X` be the blowup of `X` in `Z`.  Then the
ideal sheaf `𝓘_E` of the exceptional divisor `E = b⁻¹(Z)` is an invertible `𝒪_{X'}`-module which
is ample relative to `b`, in the sense of Stacks 0D31.  In particular `b` is representable: for
every scheme `T` and every morphism `T ⟶ X` the algebraic space `T ×_X X'` is a scheme.  The same
therefore holds for every admissible blowup of Stacks 086B.

The source obtains representability from Stacks 084B: the blowup is the relative `Proj` of the
Rees algebra `⨁_{n ≥ 0} 𝓘ⁿ`, and the base change of a relative `Proj` to a scheme `T` is
`Proj_T` of the pulled back algebra.  This file proves representability without the functor of
quadruples of Stacks 084A, by descent of relative ampleness along an étale chart (Stacks 0D3C).
It is therefore **not** Stacks 084B, and carries no Stacks attribute.

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_idealSheafOfModules_of_isBlowupAlong`: the ideal
  sheaf of the exceptional divisor of a blowup in a finitely presented centre is relatively
  ample.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_isBlowupAlong`: such a blowup is
  representable.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_isAdmissibleBlowup`: an admissible blowup
  is representable.
* `AlgebraicGeometry.Space.baseChangeModuleDefiningIdealSheafIso`: on an étale scheme chart the
  defining ideal sheaf of a closed subspace reads as the ideal sheaf of the closed subscheme it
  cuts out there.

## Proof

Relative ampleness is fpqc local on the base (Stacks 0D3C,
`AlgebraicGeometry.Space.isRelativelyAmple_iff_forall_isRelativelyAmple_of_isFpqcCovering`), and a
surjective étale morphism is an fpqc covering (Stacks 0DFQ).  So it suffices to prove relative
ampleness of the pullback of `𝓘_E` over a surjective étale chart `a : V ⟶ X` from a scheme.  Over
such a chart the blowup is the relative `Proj` of the Rees algebra of the induced sheaf of ideals
`K` on `V` (Stacks 085S and 085R,
`AlgebraicGeometry.Space.exists_iso_schemeSpace_reesProjChart_of_isEtale`), that is, the scheme
blowup `Bl_K V ⟶ V`; the chart is taken where the relative `Proj`s lie in the site
(`AlgebraicGeometry.Space.hasReesProjChartInSite_of_isFinitePresentation`).  Over a scheme
base, relative ampleness of a module on a scheme is the scheme-level notion (Stacks 0D32).  The
pullback of `𝓘_E` to `Bl_K V` is the ideal sheaf of the inverse image of `E`, the base change of a
defining ideal sheaf along an étale morphism being the defining ideal sheaf of the inverse image
(Stacks 04CO); this inverse image is the exceptional divisor of `Bl_K V`, cut out by `K·𝒪`; and
`K·𝒪 ≅ 𝒪(1)` (Stacks 02OS part (3)), which is relatively ample because `K` is of finite type
(Stacks 02NS part (2), `K` being finitely generated over affines by Stacks 084Q).  Finally a
relatively ample module lives on a representable morphism (Stacks 0D34).

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 086B](https://stacks.math.columbia.edu/tag/086B)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 0D34](https://stacks.math.columbia.edu/tag/0D34)
* [Stacks Project, Tag 0D3C](https://stacks.math.columbia.edu/tag/0D3C)
* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The ideal sheaf of a closed immersion is the ideal sheaf of the closed subscheme cut out by
its kernel.**  A closed immersion `j` factors as the isomorphism `j.toImage` onto the closed
subscheme of its kernel followed by that closed subscheme's inclusion, and the ideal sheaf of a
morphism is unchanged by an isomorphism of its source. -/
def idealSheafIsoSubschemeιOfKerEq {Z Y : Scheme.{u}} (j : Z ⟶ Y) [IsClosedImmersion j]
    {J : Y.IdealSheafData} (h : j.ker = J) :
    Stacks.ClosedImmersion.idealSheaf j.toLRSHom.toShHom ≅
      Stacks.ClosedImmersion.idealSheaf J.subschemeι.toLRSHom.toShHom :=
  Stacks.ClosedImmersion.idealSheafCongr
      (congrArg (fun f : Z ⟶ Y => f.toLRSHom.toShHom) (Scheme.Hom.toImage_imageι j).symm) ≪≫
    Stacks.ClosedImmersion.idealSheafCompIso
      (Scheme.forgetToLocallyRingedSpace.mapIso (asIso j.toImage)) j.imageι.toLRSHom ≪≫
    eqToIso (congrArg (fun I : Y.IdealSheafData =>
      Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom) h)

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The chart ideal of an inverse image is the chart ideal of the composite.**  For a closed
subspace `D` of `X`, a morphism `φ : Y ⟶ X` and a scheme point `ψ` of `Y`, the sheaf of ideals
which the inverse image `φ⁻¹(D)` cuts out on `ψ` is the one `D` cuts out on `ψ ≫ φ`: both are
read off the same subfunctor `(φ⁻¹D)ψ = D(ψ ≫ φ)` of the scheme. -/
theorem ker_rep_snd_preimage {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {D : Subfunctor X}
    (hD : IsClosedImmersion B S hS D.ι) (φ : Y ⟶ X)
    (hD' : IsClosedImmersion B S hS (D.preimage φ).ι) {U : BigFppfOver B S hS}
    (ψ : yoneda.obj U ⟶ Y) :
    ((BigFppfOver.toScheme B S hS).map (hD'.rep.snd ψ)).ker =
      ((BigFppfOver.toScheme B S hS).map (hD.rep.snd (ψ ≫ φ))).ker :=
  ker_rep_snd_eq_of_preimage_eq hD' ψ (by
    rw [← Subfunctor.preimage_comp]
    exact (idealPoints_ker_rep_snd hD (ψ ≫ φ)).symm)

/-- **The chart ideal of an inverse image along a scheme point, at the identity chart, is the chart
ideal at that point.** -/
theorem ker_rep_snd_preimage_id {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {D : Subfunctor X}
    (hD : IsClosedImmersion B S hS D.ι) {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)
    (hD' : IsClosedImmersion B S hS (D.preimage φ).ι) :
    ((BigFppfOver.toScheme B S hS).map (hD'.rep.snd (𝟙 _))).ker =
      ((BigFppfOver.toScheme B S hS).map (hD.rep.snd φ)).ker :=
  ker_rep_snd_preimage hD φ hD' (𝟙 _)

/-- **The base change of a defining ideal sheaf along an étale chart is the ideal sheaf of the
inverse image.**  For a closed subspace `E` of an algebraic space `X'` and an étale morphism
`c : h_U ⟶ X'` from a scheme of the site along which `E` is cut out by the sheaf of ideals `J`,
the reading of `𝓘_E` on `U` (`AlgebraicGeometry.Space.baseChangeModule`) is the ideal sheaf of the
closed subscheme `V(J)`. -/
def baseChangeModuleDefiningIdealSheafIso {X' : AlgebraicSpaces B S hS}
    (E : ClosedSubspaces B S hS X'.1) {U : BigFppfOver B S hS} (c : yoneda.obj U ⟶ X'.1)
    (hc : IsEtale B S hS c) {J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData}
    (hJ : ((BigFppfOver.toScheme B S hS).map (E.2.2.rep.snd c)).ker = J) :
    baseChangeModule B S hS (definingIdealSheaf B S hS X' E).toSheafOfModules U c ≅
      Stacks.ClosedImmersion.idealSheaf J.subschemeι.toLRSHom.toShHom :=
  let c' : schemeSpace U ⟶ X' := ObjectProperty.homMk c
  let E' : ClosedSubspaces B S hS (schemeSpace U).1 :=
    ⟨E.1.preimage c'.hom, isClosedSubspace_preimage B S hS c'.hom E.1 X'.2 (schemeSpace U).2 E.2⟩
  haveI : _root_.AlgebraicGeometry.IsClosedImmersion
      (chartBaseChangeHom B S hS (schemeSpace U) E' (idEtaleChart B S hS U)) :=
    E'.2.2.property_snd _
  (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U)).mapIso
      ((modulePullbackIsoEtaleModulePullback B S hS c' hc).app
        (definingIdealSheaf B S hS X' E).toSheafOfModules) ≪≫
    eqToIso (congrArg (fun M => restrictToChartScheme B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) M (idEtaleChart B S hS U))
      (etaleModulePullback_definingIdealSheaf_eq B S hS c' hc E)) ≪≫
    restrictToChartSchemeIsoPushforward B S hS (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U) (definingIdealSheaf B S hS (schemeSpace U) E').toSheafOfModules ≪≫
    chartSchemePushforwardDefiningIdealIso B S hS (schemeSpace U) (idEtaleChart B S hS U) E' ≪≫
    idealSheafIsoSubschemeιOfKerEq _
      ((ker_rep_snd_preimage_id E.2.2 c E'.2.2).trans hJ)

variable {X X' : AlgebraicSpaces B S hS}

/-- **The exceptional ideal sheaf of a blowup is relatively ample.**  Let `b : X' ⟶ X` be the
blowup of an algebraic space `X` in a closed subspace `Z` whose closed immersion is of finite
presentation.  The ideal sheaf `𝓘_E` of the exceptional divisor `E = b⁻¹(Z)` is ample relative to
`b` (Stacks 0D31).

See the module documentation for the proof: Stacks 0D3C reduces the claim to a surjective étale
scheme chart of `X`, over which the blowup is the scheme blowup and `𝓘_E` is its twisting sheaf
`𝒪(1)`. -/
theorem isRelativelyAmple_idealSheafOfModules_of_isBlowupAlong
    {Z : ClosedSubspaces B S hS X.1} (hfp : IsFinitePresentation B S hS Z.1.ι)
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b) :
    IsRelativelyAmple B S hS b (idealSheafOfModules B S hS X' (preimageClosedSubspace b Z)) := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  have hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X'.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).property
      (idealSheafOfModules B S hS X' (preimageClosedSubspace b Z)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hb.isPullbackDefined
  obtain ⟨V, a, ha, hasurj, hcU, hcR, hcRR⟩ :=
    hasReesProjChartInSite_of_isFinitePresentation B S hS Z hfp
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS a b
  refine (isRelativelyAmple_iff_forall_isRelativelyAmple_of_isFpqcCovering (I := PUnit.{1})
    (fun _ => sq.flip) _ hL ?_).mpr fun _ => ?_
  · exact isFpqcCovering_of_isEtaleCovering B S hS _ _
      ⟨X.2, fun _ => (schemeSpace V).2, fun _ => ha,
        Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨PUnit.unit, hasurj x⟩⟩
  set K := reesChartIdeal (centreIdeal (preimageClosedSubspace a Z))
    (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) with hK
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_reesProjChart_of_isEtale hb V ha hcU hcR hcRR sq
  obtain ⟨e', he'⟩ := exists_iso_schemeSpace_blowUpObj_of_iso V K _ e he
    (Stacks.Blowup.reesSituationBlowUpIso K)
    (Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase K)
  have hL' : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (AlgebraicSpaces.fiberProduct B S hS a b).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (AlgebraicSpaces.fiberProduct B S hS a b).1
        (AlgebraicSpaces.fiberProduct B S hS a b).2).O)).property
      ((modulePullback B S hS (ObjectProperty.homMk (pullback.snd a.hom b.hom))).obj
        (idealSheafOfModules B S hS X' (preimageClosedSubspace b Z))) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
    (isInvertible_modulePullback_obj B S hS
      (ObjectProperty.homMk (pullback.snd a.hom b.hom) :
        AlgebraicSpaces.fiberProduct B S hS a b ⟶ X')
      _ hb.isPullbackDefined)
  refine isRelativelyAmple_of_exists_scheme _ _ hL' V (Iso.refl _)
    ⟨blowUpObj V K, (ObjectProperty.ι _).mapIso e'.symm,
      isInvertibleModule_baseChangeModule _ hL' _ _, ?_⟩
  have hinv : e'.inv ≫ ObjectProperty.homMk (pullback.fst a.hom b.hom) =
      schemeSpaceMap (blowUpObjHom V K) := by
    rw [← he', Iso.inv_hom_id_assoc]
  -- the chart `c : U ⟶ X'` of the blowup, étale, and the ideal it cuts out
  set c : yoneda.obj (blowUpObj V K) ⟶ X'.1 :=
    ((ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F).mapIso e'.symm).hom ≫
      (ObjectProperty.homMk (pullback.snd a.hom b.hom) :
        AlgebraicSpaces.fiberProduct B S hS a b ⟶ X').hom with hc_def
  have hiso : IsIso ((ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F).mapIso e'.symm).hom :=
    Iso.isIso_hom _
  have hc : IsEtale B S hS c :=
    isEtale_comp B S hS (@isEtale_of_isIso B S hS _ _ _ hiso)
      (isEtale_of_isPullback B S hS _ _ _ _ sq ha)
  have hcb : c ≫ b.hom = yoneda.map (blowUpObjHom V K) ≫ a.hom := by
    have h : c ≫ b.hom = (e'.inv ≫ ObjectProperty.homMk (pullback.snd a.hom b.hom) ≫ b).hom :=
      rfl
    rw [h, ← sq.w, ← Category.assoc, hinv]
    rfl
  have hJ : ((BigFppfOver.toScheme B S hS).map
      ((preimageClosedSubspace b Z).2.2.rep.snd c)).ker =
        _root_.AlgebraicGeometry.exceptionalIdeal K := by
    have hKa : ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd a.hom)).ker = K :=
      (ker_rep_snd_preimage_id Z.2.2 a.hom (preimageClosedSubspace a Z).2.2).symm.trans
        (ker_rep_snd_eq_reesChartIdeal B S hS (schemeSpace V) (preimageClosedSubspace a Z)
          (selfPresentation B S hS V))
    exact (ker_rep_snd_preimage Z.2.2 b.hom (preimageClosedSubspace b Z).2.2 c).trans
      ((congrArg (fun φ => ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)).ker) hcb).trans
        ((schemeKer_snd_comp B S hS Z a.hom (blowUpObjHom V K)).trans
          (congrArg (fun J => J.comap ((BigFppfOver.toScheme B S hS).map (blowUpObjHom V K)))
            hKa)))
  have hfin : K.IsFiniteType := fg_ideal_reesChartIdeal_preimage B S hS Z hfp V a
  have := isInvertibleModule_baseChangeModule _ hL' (blowUpObj V K)
    ((ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F).mapIso e'.symm).hom
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj (blowUpObj V K))
      (blowUpTwist K 1) := isInvertibleModule_blowUpTwist K 1
  have hamp := (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _
    ((baseChangeModuleCompIso B S hS
        (ObjectProperty.homMk (pullback.snd a.hom b.hom) :
          AlgebraicSpaces.fiberProduct B S hS a b ⟶ X')
        (idealSheafOfModules B S hS X' (preimageClosedSubspace b Z))
        (blowUpObj V K)
        ((ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F).mapIso e'.symm).hom).symm ≪≫
      baseChangeModuleDefiningIdealSheafIso (preimageClosedSubspace b Z) c hc hJ ≪≫
      (twistOneIsoExceptionalIdealModule K).symm)).mpr (isRelativelyAmple_blowUpTwist K hfin)
  have hmap : (BigFppfOver.toScheme B S hS).map (yoneda.preimage
      (((ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F).mapIso e'.symm).hom ≫
        (ObjectProperty.homMk (pullback.fst a.hom b.hom) :
          AlgebraicSpaces.fiberProduct B S hS a b ⟶ schemeSpace V).hom ≫
        (Iso.refl (schemeSpace V).obj).hom)) = _root_.AlgebraicGeometry.blowUpToBase K := by
    rw [show _root_.AlgebraicGeometry.blowUpToBase K =
      (BigFppfOver.toScheme B S hS).map (blowUpObjHom V K) from rfl]
    congr 1
    apply yoneda.map_injective
    simp only [Functor.map_preimage, Iso.refl_hom]
    exact congrArg (fun f => f.hom) hinv
  rw [hmap]
  exact hamp

/-- **A blowup of an algebraic space in a finitely presented closed subspace is representable.**
For every scheme `T` and morphism `T ⟶ X` the base change `T ×_X X'` is a scheme: `b` carries the
relatively ample module `𝓘_E`
(`AlgebraicGeometry.Space.isRelativelyAmple_idealSheafOfModules_of_isBlowupAlong`), and a
relatively ample module lives on a representable morphism (Stacks 0D34). -/
theorem relativelyRepresentable_of_isBlowupAlong {Z : ClosedSubspaces B S hS X.1}
    (hfp : IsFinitePresentation B S hS Z.1.ι) {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b) :
    yoneda.relativelyRepresentable b.hom :=
  (isRelativelyAmple_idealSheafOfModules_of_isBlowupAlong hfp hb).relativelyRepresentable

/-- **An admissible blowup of an algebraic space is representable.**  A `U`-admissible blowup of
Stacks 086B is a blowup in a closed subspace whose closed immersion is of finite presentation, so
`AlgebraicGeometry.Space.relativelyRepresentable_of_isBlowupAlong` applies.  This is the
representability that Stacks 088R asks of the blowup `Z' ⟶ Z` it constructs, and the source
derives it from Stacks 084B. -/
theorem relativelyRepresentable_of_isAdmissibleBlowup (V : OpenSubspaces B S hS X.1) (b : X' ⟶ X)
    (hb : IsAdmissibleBlowup B S hS V b) : yoneda.relativelyRepresentable b.hom := by
  obtain ⟨Z, hfp, -, hbl⟩ := hb
  exact relativelyRepresentable_of_isBlowupAlong hfp hbl

end Space

end AlgebraicGeometry

end
