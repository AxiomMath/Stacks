module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.KernelPairCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.ProblemStepLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# The problem step of the proof of Stacks 07SU

This file carries out the problem step of the proof of Stacks 07SU. Let `X` be a
quasi-separated algebraic space over `Spec ℤ`, `U ⊆ X` an open subspace, `Z ⊆ X` a subspace with
`|X| = |U| ⊔ |Z|`, and `f : V ⟶ X` a surjective étale morphism from a quasi-compact separated
scheme such that `f⁻¹(Z) ⟶ Z` is an isomorphism. If `U` is presented as the limit of a system
of étale quotients of finite type over `Spec ℤ` (`AlgebraicGeometry.Space.QuotientApproximation`),
then so is `X`.

## Main results

* `AlgebraicGeometry.Space.QuotientApproximation.problemStep`: the problem step.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)]

namespace QuotientApproximation

/-- **The problem step of the proof of Stacks 07SU.** Let `X` be a quasi-separated algebraic
space over `Spec ℤ`, `U ⊆ X` an open subspace, `Z ⊆ X` a subfunctor with `|Z| = |X| ∖ |U|`, and
`f : V ⟶ X` a surjective étale morphism from a quasi-compact separated scheme such that
`f⁻¹(Z) ⟶ Z` is an isomorphism. If `U` is presented as the limit of a system of étale quotients
of finite type over `Spec ℤ`, then so is `X`. -/
theorem problemStep {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hXqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X)
    (U : Subfunctor X) (hU : IsOpenSubspace B (⊤_ Scheme.{u}) hZ U)
    (AU : QuotientApproximation hZ U.toFunctor) (Z : Subfunctor X)
    (hUZ : Set.range (pointsMap B (⊤_ Scheme.{u}) hZ Z.toFunctor Z.ι) =
      (Set.range (pointsMap B (⊤_ Scheme.{u}) hZ U.toFunctor U.ι))ᶜ)
    (Vs : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    [CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Vs)]
    [((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Vs).IsSeparated]
    (f : yoneda.obj Vs ⟶ X)
    (hfsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f)
    (hfet : IsEtale B (⊤_ Scheme.{u}) hZ f) (hZiso : IsIso (pullback.fst Z.ι f)) :
    Nonempty (QuotientApproximation hZ X) := by
  classical
  have hUalg : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ U.toFunctor := hU.1
  have hUsh := hUalg.isSheaf
  -- the system approximating `U`, made small
  obtain ⟨A, hA⟩ := AU.exists_small
  have hb := A.chartsBounded_of_small hA
  obtain ⟨eU, heU⟩ := A.exists_iso_limit hUsh
  let E := A.E
  have hL : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (limit E.quotient) := hUalg.of_iso eU
  -- `W = f⁻¹(U)`, an open subscheme of `V`
  have hUo := hU.2
  let Wr := hUo.rep.pullback f
  let a : Wr ⟶ Vs := hUo.rep.snd f
  let bW : yoneda.obj Wr ⟶ U.toFunctor := hUo.rep.fst f
  have hsqW : IsPullback bW (yoneda.map a) U.ι f := hUo.rep.isPullback f
  have ha : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map a) := hUo.property_snd f
  let Wo : ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Vs).Opens :=
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map a).opensRange
  let Ws := openSiteObject B (⊤_ Scheme.{u}) hZ Vs Wo
  let ι : Ws ⟶ Vs := openSiteObjectHom B (⊤_ Scheme.{u}) hZ Vs Wo
  let eW : Ws ⟶ Wr := overIntegersHom
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map a).isoOpensRange.inv
  have heW : eW ≫ a = ι := by
    apply (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map_injective
    rw [map_openSiteObjectHom, Functor.map_comp]
    show ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map a).isoOpensRange.inv ≫
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map a = Wo.ι
    exact Scheme.Hom.isoOpensRange_inv_comp _
  have : IsIso eW := by
    have : IsIso ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map eW) := by
      show IsIso ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map a).isoOpensRange.inv
      infer_instance
    exact isIso_of_reflects_iso eW (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)
  let wU : yoneda.obj Ws ⟶ U.toFunctor := yoneda.map eW ≫ bW
  have hsqWs : IsPullback wU (yoneda.map ι) U.ι f :=
    hsqW.of_iso (yoneda.mapIso (asIso eW)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [wU]) (by simp [← heW]) (by simp) (by simp)
  -- finiteness of `W ⟶ U`
  have hVsp := isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ Vs
  have hWsp := isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ Ws
  have hwUet : IsEtale B (⊤_ Scheme.{u}) hZ wU :=
    isEtale_of_isPullback_of_isAlgebraicSpace B (⊤_ Scheme.{u}) hZ hsqWs hWsp hUalg hVsp hX hfet
  have hVqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (yoneda.obj Vs) :=
    isQuasiCompactSpace_yoneda_obj B (⊤_ Scheme.{u}) hZ inferInstance
  have hfqc : IsQuasiCompact B (⊤_ Scheme.{u}) hZ f :=
    isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hX hXqs hVqc f
  have hwUqc : IsQuasiCompact B (⊤_ Scheme.{u}) hZ wU :=
    isQuasiCompact_of_isPullback B (⊤_ Scheme.{u}) hZ hsqWs.flip hfqc
  have hWqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (yoneda.obj Ws) :=
    isQuasiCompactSpace_source_of_isQuasiCompact B (⊤_ Scheme.{u}) hZ hUalg AU.isQuasiCompactSpace
      hwUqc
  have : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Ws) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B (⊤_ Scheme.{u}) hZ hWqc
  have : CompactSpace Wo := ‹CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Ws)›
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Ws) :=
    QuasiSeparatedSpace.of_isOpenEmbedding Wo.ι.isOpenEmbedding
  have hWqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (yoneda.obj Ws) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (⊤_ Scheme.{u}) hZ _ hZ
      ⟨Ws, inferInstance, ⟨Functor.representableByEquiv.symm (Iso.refl _)⟩⟩
  have hwUfp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ wU :=
    ⟨isLocallyOfFinitePresentation_of_isEtale B (⊤_ Scheme.{u}) hZ hwUet, hwUqc,
      isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B (⊤_ Scheme.{u}) hZ hZ hWsp hWqs wU⟩
  let w : yoneda.obj Ws ⟶ limit E.quotient := wU ≫ eU.hom
  have hwfp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ w :=
    isFinitePresentation_comp_iso hWsp hUalg hL wU eU hwUfp
  have hwet : IsEtale B (⊤_ Scheme.{u}) hZ w :=
    isEtale_comp B (⊤_ Scheme.{u}) hZ hwUet (isEtale_of_isIso B (⊤_ Scheme.{u}) hZ _)
  -- the descent of `W ⟶ U` to a scheme stage `W_k ⟶ U_k`
  obtain ⟨k, Wk, wk, g, hwk, hWk, hLk⟩ :=
    E.exists_schemeStage_of_isEtale (hZ := hZ) A.hobj A.cV A.hV hb A.isQuasiCompactSpace_quotient
      A.isAbsolutelyQuasiSeparated_quotient hL w hwfp hwet
  -- Stacks 07RN
  obtain ⟨Q, hQ⟩ := E.exists_finiteTypeApproximation_nbhd hZ A.hobj k wk A.hlft hwk A.cV A.hV Vs
    Wo w g hLk
  have : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj Wk) := hWk
  -- the glueing data and its limits
  let G := E.problemStepData hZ A.hobj k wk hwk Vs Wo w g hLk Q
  obtain ⟨R, s, t, hR⟩ := exists_kernelPair_of_etale_atlas B (⊤_ Scheme.{u}) hZ f
    ((isEtale_iff_presheaf_of_yoneda B (⊤_ Scheme.{u}) hZ f).1 hfet)
  let d : Vs ⟶ R := yoneda.preimage (hR.lift (𝟙 _) (𝟙 _) rfl)
  have hds : d ≫ s = 𝟙 _ := yoneda.map_injective (by simp [d])
  have hdt : d ≫ t = 𝟙 _ := yoneda.map_injective (by simp [d])
  let L : G.LimitData :=
    { coneV := E.problemStepAmbientCone hZ A.hobj k wk hwk Vs Wo w g hLk Q
      isLimitV := (E.isLimit_problemStepAmbientCone hZ A.hobj k wk hwk Vs Wo w g hLk Q).some
      coneW := E.problemStepNbhdCone hZ A.hobj k wk hwk Vs Wo w g hLk Q
      isLimitW := (E.isLimit_problemStepNbhdCone' hZ A.hobj k wk hwk Vs Wo w g hLk Q hQ A.hlft
        A.cV A.hV).some
      inclL := ι
      inclL_π := E.problemStep_incl_π hZ A.hobj k wk hwk Vs Wo w g hLk Q
      baseL := limit E.quotient
      baseπ :=
        { app j := limit.π E.quotient
            ((E.problemStepBaseIndex hZ A.hobj k wk Vs Wo w g hLk Q).obj j)
          naturality {i j} u := by
            simp only [Functor.const_obj_obj, Functor.const_obj_map]
            exact (limit.w E.quotient _).symm }
      toBaseL := w
      isPullback_toBaseL := E.isPullback_problemStepNbhdLeg hZ A.hobj k wk hwk Vs Wo w g hLk Q
      space := X
      atlas := f
      etale_atlas := (isEtale_iff_presheaf_of_yoneda B (⊤_ Scheme.{u}) hZ f).1 hfet
      baseIncl := eU.inv ≫ U.ι
      mono_baseIncl := inferInstance
      isPullback_baseIncl := hsqWs.of_iso (Iso.refl _) eU (Iso.refl _) (Iso.refl _)
        (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm)
        (by simp) ((Category.comp_id _).trans (Category.id_comp _).symm)
      kernel := R
      kernelFst := s
      kernelSnd := t
      isPullback_kernel := hR
      kernelDiag := d
      kernelDiag_fst := hds
      kernelDiag_snd := hdt
      cover := mem_range_diag_or_mem_range_of_isIso_pullback_fst f U Z hUZ hZiso ι wU hsqWs s t hR
        d hds hdt }
  refine ⟨L.quotientApproximation (fun g => Q.transition_affine _)
    (fun j => (quasiCompact_iff_compactSpace (terminal.from _)).mp (Q.quasiCompact _))
    (fun j => Q.locallyOfFiniteType _)
    (E.compactSpace_problemStepKernelPair hZ A.hobj k wk hwk Vs Wo w g hLk Q
      A.isAbsolutelyQuasiSeparated_quotient) hfsurj⟩

end QuotientApproximation

end AlgebraicGeometry.Space

end
