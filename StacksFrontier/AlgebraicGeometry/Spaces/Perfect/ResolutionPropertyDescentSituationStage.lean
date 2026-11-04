module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ZeroLocusComplementStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStageSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyIdealDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSupportedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated

/-!
# The situation of Stacks 0GUY at a stage of a Noetherian approximation

Let `X = lim X_i` be a directed limit of quasi-compact quasi-separated algebraic spaces with
affine transition morphisms (Stacks 07SU), and let a situation of Stacks 0GUY over `X` be given
whose finite morphism `π : Y ⟶ X` is the base change of a finite morphism of finite presentation
`π_i : Y_i ⟶ X_i`, and whose ideal `ℐ` has zero locus the inverse image of a closed subspace
`V(ℐ_i) ⊆ Y_i` of finite presentation.  Then for a later stage `i'` the open complement `V_{i'}`
of `V(ℐ_i) ×_{Y_i} Y_{i'}` in `Y_{i'} = Y_i ×_{X_i} X_{i'}` is affine and étale and surjective
over `X_{i'}` (Stacks 07SQ, 07SL and 07SN), so that the data at the stage `i'` is again a
situation of Stacks 0GUY.

## Main results

* `exists_resolutionPropertyDescentSituation_stage_of_siteContainsBaseChangeLimits`:
  the situation of Stacks 0GUY at a later stage, with `Y_{i'} = Y_i ×_{X_i} X_{i'}`, the square
  of `Y ⟶ Y_{i'}` over `X ⟶ X_{i'}` cartesian, and ideal that of `V(ℐ_i) ×_{Y_i} Y_{i'}`.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07SL](https://stacks.math.columbia.edu/tag/07SL)
* [Stacks Project, Tag 07SN](https://stacks.math.columbia.edu/tag/07SN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {hZ : B.Contains (⊤_ Scheme.{u})}

/-- A morphism conjugated by isomorphisms on both sides is étale and surjective if it is. -/
private theorem isEtale_and_isSurjective_iso_comp_comp_iso
    {F G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ≅ G) (f : G ⟶ H) (b : H ≅ K)
    (hf : IsEtale B S hS f) (hf' : IsSurjective B S hS f) :
    IsEtale B S hS (a.hom ≫ f ≫ b.hom) ∧ IsSurjective B S hS (a.hom ≫ f ≫ b.hom) :=
  ⟨isEtale_comp B S hS (isEtale_of_iso B S hS a) (isEtale_comp B S hS hf (isEtale_of_iso B S hS b)),
    isSurjective_comp B S hS (isSurjective_of_isIso B S hS a.hom)
      (isSurjective_comp B S hS hf' (isSurjective_of_isIso B S hS b.hom))⟩

/-- **The situation of Stacks 0GUY at a later stage of a Noetherian approximation.**  Let
`X = lim X_i` be a directed limit of quasi-compact quasi-separated algebraic spaces with affine
transition morphisms, under the chapter's convention of Section 70.2 (tag 07SD), and let a
situation of Stacks 0GUY over `X` be given, with `π : Y ⟶ X` the base change of a finite
morphism of finite presentation `π_i : Y_i ⟶ X_i` (`Y = Y_i ×_{X_i} X`), and a closed subspace
`V(ℐ_i) ⊆ Y_i` with inclusion of finite presentation whose inverse image in `Y` has the zero
locus `V(ℐ)` of the ideal of the situation as point set.

Then for some `i' ≥ i` there is a situation of Stacks 0GUY over `X_{i'}` whose space is
`Y_{i'} = Y_i ×_{X_i} X_{i'}` (the square of `Y_{i'} ⟶ Y_i` over `X_{i'} ⟶ X_i` is cartesian,
and so is the square of `Y ⟶ Y_{i'}` over `X ⟶ X_{i'}`), whose morphism `π_{i'}` is of finite
presentation, and whose ideal is the defining ideal of `V(ℐ_i) ×_{Y_i} Y_{i'}`: the open
complement `V_{i'}` of that closed subspace is affine, and étale and surjective over `X_{i'}`. -/
theorem exists_resolutionPropertyDescentSituation_stage_of_siteContainsBaseChangeLimits
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAff : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hDlim : IsAlgebraicSpace B S hS (limit D))
    {hqc : IsQuasiCompactSpace B S hS (limit D)}
    {hqs : IsAbsolutelyQuasiSeparated B S hS hZ (limit D)}
    (sit : ResolutionPropertyDescentSituation B S hS hZ ⟨limit D, hDlim⟩ hqc hqs)
    (i : I) {Yi : AlgebraicSpaces B S hS} (πi : Yi ⟶ ⟨D.obj (op i), hD _⟩)
    (hfin : IsFinite B S hS πi.hom) (hfp : IsFinitePresentation B S hS πi.hom)
    (gi : sit.Y ⟶ Yi)
    (sq : IsPullback gi (sit.πHom) πi
      (ObjectProperty.homMk (limit.π D (op i)) :
        (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj (op i), hD _⟩))
    (Zi : ClosedSubspaces B S hS Yi.1) (hZi : IsFinitePresentation B S hS Zi.1.ι)
    (hI : idealZeroLocus B S hS sit.Y sit.I =
      Set.range (pointsMap B S hS (Zi.1.preimage gi.hom).toFunctor (Zi.1.preimage gi.hom).ι)) :
    ∃ (i' : I) (hii' : i ≤ i')
      (sit' : ResolutionPropertyDescentSituation B S hS hZ ⟨D.obj (op i'), hD _⟩ (hQc _) (hQs _))
      (g' : sit'.Y ⟶ Yi) (gL : sit.Y ⟶ sit'.Y),
      IsFinitePresentation B S hS sit'.π ∧
      IsPullback g' (sit'.πHom) πi
        (ObjectProperty.homMk (D.map (homOfLE hii').op) :
          (⟨D.obj (op i'), hD _⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj (op i), hD _⟩) ∧
      IsPullback gL (sit.πHom) (sit'.πHom)
        (ObjectProperty.homMk (limit.π D (op i')) :
          (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj (op i'), hD _⟩) ∧
      gL ≫ g' = gi ∧
      sit'.I = definingIdealSheaf B S hS sit'.Y (preimageSubspace B S hS g' Zi) := by
  classical
  have key : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W₁ W₂ : Subfunctor F} (h : W₁ = W₂),
      eqToHom (congrArg Subfunctor.toFunctor h) ≫ W₂.ι = W₁.ι := by
    intro _ _ _ h
    subst h
    simp
  have hWopen : IsOpenSubspace B S hS (openComplement B S hS Zi.1) :=
    isOpenSubspace_openComplement B S hS Yi.2 Zi.1 Zi.2
  have hWalg : IsAlgebraicSpace B S hS (openComplement B S hS Zi.1).toFunctor := hWopen.1
  have hWqc : IsQuasiCompactSpace B S hS (openComplement B S hS Zi.1).toFunctor :=
    isQuasiCompactSpace_openComplement_of_isFinitePresentation Yi.2
      (isQuasiCompactSpace_source_of_isQuasiCompact B S hS (hD _) (hQc _) hfp.2.1) Zi.1 Zi.2 hZi
  have hWqs : IsAbsolutelyQuasiSeparated B S hS hZ (openComplement B S hS Zi.1).toFunctor :=
    isAbsolutelyQuasiSeparated_of_mono B S hS hZ hWalg (openComplement B S hS Zi.1).ι inferInstance
      (isAbsolutelyQuasiSeparated_of_isFinitePresentation B S hS hZ Yi.2 (hQs _) hfp)
  let t : (openComplement B S hS Zi.1).toFunctor ⟶ D.obj (op i) :=
    (openComplement B S hS Zi.1).ι ≫ πi.hom
  have ht : IsLocallyOfFinitePresentation B S hS t :=
    isLocallyOfFinitePresentation_comp B S hS hWalg Yi.2 (hD _) _ _
      (isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hWopen.2) hfp.1
  let M : MorphismDescentSituation B S hS hZ I :=
    { base := D
      base_isAlgebraicSpace := fun _ => hD _
      transition_affine := hAff
      limit_isAlgebraicSpace := hDlim
      initial := i
      source₀ := (openComplement B S hS Zi.1).toFunctor
      target₀ := D.obj (op i)
      sourceToBase := t
      targetToBase := 𝟙 _
      map₀ := t
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hWalg
      target₀_isAlgebraicSpace := hD _
      base₀_quasiCompact := hQc _
      base₀_quasiSeparated := hQs _
      source₀_quasiCompact := hWqc
      source₀_quasiSeparated := hWqs
      target₀_quasiCompact := hQc _
      target₀_quasiSeparated := hQs _ }
  have sqp : IsPullback gi.hom sit.π πi.hom (limit.π D (op i)) :=
    isPullback_hom_of_isPullback B S hS sq
  have hbig : IsPullback ((openComplement B S hS Zi.1).fromPreimage gi.hom)
      (((openComplement B S hS Zi.1).preimage gi.hom).ι ≫ sit.π) t (limit.π D (op i)) :=
    (Subfunctor.isPullback_preimage gi.hom (openComplement B S hS Zi.1)).paste_vert sqp
  have : Mono sit.j := mono_of_presheaf_isOpenImmersion sit.isOpenImmersion_j
  have hjT : Set.range (pointsMap B S hS (yoneda.obj sit.V) sit.j) =
      (Set.range (pointsMap B S hS (Zi.1.preimage gi.hom).toFunctor
        (Zi.1.preimage gi.hom).ι))ᶜ := by
    rw [← hI, sit.idealZeroLocus_I, compl_compl]
  have hrange : Subfunctor.range sit.j = (openComplement B S hS Zi.1).preimage gi.hom := by
    rw [range_eq_openSubspaceOfPoints_of_isOpenImmersion B S hS sit.j sit.isOpenImmersion_j, hjT,
      openComplement_preimage, openComplement_eq_openSubspaceOfPoints_compl]
  let e₁ : yoneda.obj sit.V ≅ ((openComplement B S hS Zi.1).preimage gi.hom).toFunctor :=
    asIso (Subfunctor.toRange sit.j) ≪≫ eqToIso (congrArg Subfunctor.toFunctor hrange)
  have he₁ : e₁.hom ≫ ((openComplement B S hS Zi.1).preimage gi.hom).ι = sit.j := by
    simp only [e₁, Iso.trans_hom, asIso_hom, eqToIso.hom, Category.assoc,
      key hrange, Subfunctor.toRange_ι]
  have hV : IsPullback (e₁.hom ≫ (openComplement B S hS Zi.1).fromPreimage gi.hom) sit.φ t
      (limit.π D (op i)) := by
    refine hbig.of_iso e₁.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · rw [← sit.comp_eq, ← he₁]
      simp
    · simp
    · simp
  let eV : yoneda.obj sit.V ≅ pullback (limit.π D (op i)) t := hV.flip.isoPullback
  have heV : eV.hom ≫ pullback.fst (limit.π D (op i)) t = sit.φ := hV.flip.isoPullback_hom_fst
  have : IsIso M.targetToBase := (inferInstance : IsIso (𝟙 (D.obj (op i))))
  let κ := asIso (pullback.fst (limit.π M.base (op M.initial)) M.targetToBase)
  have hmapLim : M.mapLimit = eV.inv ≫ sit.φ ≫ κ.inv := by
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv κ).2 ((M.mapLimit_fst).trans
      ((Iso.inv_hom_id_assoc eV _).symm.trans (congrArg (eV.inv ≫ ·) heV)))
  have hLim := isEtale_and_isSurjective_iso_comp_comp_iso eV.symm sit.φ κ.symm sit.isEtale_φ
    sit.isSurjective_φ
  rw [Iso.symm_hom, Iso.symm_hom, ← hmapLim] at hLim
  obtain ⟨hEtLim, hSuLim⟩ := hLim
  obtain ⟨i₁, hi₁, het₁⟩ := M.exists_isEtale_mapAt_of_siteContainsBaseChangeLimits hconv hEtLim ht
  obtain ⟨i₂, hi₂, hsu₂⟩ :=
    M.exists_isSurjective_mapAt_of_siteContainsBaseChangeLimits hconv hSuLim ht
  let DS := M.stagesBaseChangeDescentSituation t hWalg hWqc hWqs
  obtain ⟨j₃, -, haff₃⟩ := DS.exists_isAffineSpace_system_obj_of_siteContainsBaseChangeLimits
    (M.siteContainsBaseChangeLimits_stagesBaseChangeSystem hconv t)
    ⟨sit.V, sit.isAffine_V, ⟨eV.symm⟩⟩
  obtain ⟨k₁, hk₁, hk₂⟩ := directed_of (· ≤ ·) i₁ i₂
  obtain ⟨i', hk', hj₃'⟩ := directed_of (· ≤ ·) k₁ j₃.1
  have hii' : i ≤ i' := hi₁.trans (hk₁.trans hk')
  have het' : IsEtale B S hS (M.mapAt i' hii') := M.isEtale_mapAt_of_le hi₁ (hk₁.trans hk') het₁
  have hsu' : IsSurjective B S hS (M.mapAt i' hii') :=
    M.isSurjective_mapAt_of_le hi₂ (hk₂.trans hk') hsu₂
  obtain ⟨V', hV'aff, ⟨eV'⟩⟩ :
      IsAffineSpace B S hS (pullback (M.baseAtToInitial i' hii') M.sourceToBase) :=
    isAffineSpace_source_of_isAffineHom
      (DS.transition_affine (homOfLE (show j₃ ≤ ⟨i', hii'⟩ from hj₃')).op) haff₃
  let gst : (⟨D.obj (op i'), hD _⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj (op i), hD _⟩ :=
    ObjectProperty.homMk (D.map (homOfLE hii').op)
  let Y' : AlgebraicSpaces B S hS :=
    ⟨pullback πi.hom gst.hom, isAlgebraicSpace_pullback B S hS πi.hom gst.hom Yi.2 (hD _) (hD _)⟩
  let π' : Y' ⟶ ⟨D.obj (op i'), hD _⟩ := ObjectProperty.homMk (pullback.snd πi.hom gst.hom)
  let g' : Y' ⟶ Yi := ObjectProperty.homMk (pullback.fst πi.hom gst.hom)
  have sq₀ : IsPullback (pullback.fst πi.hom gst.hom) (pullback.snd πi.hom gst.hom) πi.hom
      gst.hom := IsPullback.of_hasPullback _ _
  have sq' : IsPullback g' π' πi gst := isPullback_of_isPullback_hom B S hS sq₀
  have hπ'fin : IsFinite B S hS π'.hom := isFinite_of_isPullback B S hS sq₀ hfin
  have hπ'fp : IsFinitePresentation B S hS π'.hom :=
    isFinitePresentation_pullback_snd B S hS πi.hom gst.hom Yi.2 (hD _) (hD _) hfp
  have hw : gi.hom ≫ πi.hom = sit.π ≫ limit.π D (op i') ≫ gst.hom := by
    rw [sqp.w, ← limit.w D (homOfLE hii').op]
    rfl
  let gL : sit.Y ⟶ Y' := ObjectProperty.homMk (pullback.lift gi.hom (sit.π ≫ limit.π D (op i')) hw)
  have hgL : gL ≫ g' = gi := ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)
  have hgL' : gL ≫ π' = sit.πHom ≫ (ObjectProperty.homMk (limit.π D (op i')) :
      (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj (op i'), hD _⟩) :=
    ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)
  have sqL : IsPullback gL sit.πHom π' (ObjectProperty.homMk (limit.π D (op i')) :
      (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj (op i'), hD _⟩) := by
    refine IsPullback.of_right ?_ hgL' sq'
    have hb : (ObjectProperty.homMk (limit.π D (op i')) :
        (⟨limit D, hDlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.obj (op i'), hD _⟩) ≫ gst =
        ObjectProperty.homMk (limit.π D (op i)) :=
      ObjectProperty.hom_ext _ (limit.w D (homOfLE hii').op)
    rw [hgL, hb]
    exact sq
  have sq'p : IsPullback g'.hom π'.hom πi.hom (D.map (homOfLE hii').op) :=
    isPullback_hom_of_isPullback B S hS sq'
  have hstage : IsPullback (((openComplement B S hS Zi.1).preimage g'.hom).ι ≫ π'.hom)
      ((openComplement B S hS Zi.1).fromPreimage g'.hom) (M.baseAtToInitial i' hii') t :=
    ((Subfunctor.isPullback_preimage g'.hom (openComplement B S hS Zi.1)).paste_vert sq'p).flip
  let e₂ := hstage.isoIsPullback _ _ (M.sourceAt_isPullback i' hii')
  have he₂ : e₂.hom ≫ pullback.fst (M.baseAtToInitial i' hii') M.sourceToBase =
      ((openComplement B S hS Zi.1).preimage g'.hom).ι ≫ π'.hom :=
    hstage.isoIsPullback_hom_fst _ _ (M.sourceAt_isPullback i' hii')
  have hW' := openComplement_preimage B S hS Zi.1 g'.hom
  let e : yoneda.obj V' ≅ (openComplement B S hS (Zi.1.preimage g'.hom)).toFunctor :=
    eV'.symm ≪≫ e₂.symm ≪≫ eqToIso (congrArg Subfunctor.toFunctor hW')
  let j' : yoneda.obj V' ⟶ Y'.1 := e.hom ≫ (openComplement B S hS (Zi.1.preimage g'.hom)).ι
  let κ' := asIso (pullback.fst (M.baseAtToInitial i' hii') M.targetToBase)
  have hφ' : j' ≫ π'.hom = eV'.inv ≫ M.mapAt i' hii' ≫ κ'.hom := by
    have h1 : j' ≫ π'.hom = eV'.inv ≫ e₂.inv ≫
        ((openComplement B S hS Zi.1).preimage g'.hom).ι ≫ π'.hom := by
      simp only [j', e, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc,
        reassoc_of% (key hW')]
    refine h1.trans ?_
    calc eV'.inv ≫ e₂.inv ≫ ((openComplement B S hS Zi.1).preimage g'.hom).ι ≫ π'.hom
        = eV'.inv ≫ pullback.fst (M.baseAtToInitial i' hii') M.sourceToBase := by
          rw [← he₂, Iso.inv_hom_id_assoc]
      _ = _ := congrArg (fun z => eV'.inv ≫ z) (M.mapAt_fst i' hii').symm
  have hφ'' := isEtale_and_isSurjective_iso_comp_comp_iso eV'.symm (M.mapAt i' hii') κ' het' hsu'
  rw [Iso.symm_hom, ← hφ'] at hφ''
  obtain ⟨hφet, hφsu⟩ := hφ''
  let Z' := preimageSubspace B S hS g' Zi
  have hZ'fp : IsFinitePresentation B S hS Z'.1.ι :=
    isFinitePresentation_of_isPullback B S hS Z'.2.1 Zi.2.1 Y'.2 Yi.2
      (Subfunctor.isPullback_preimage g'.hom Zi.1) hZi
  have hZ'ft : SheafOfModules.IsFiniteTypeOnSite
      (definingIdealSheaf B S hS Y' Z').toSheafOfModules :=
    (isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf B S hS
      (subspaceInclusion B S hS Y' Z') Z'.2.2).1 hZ'fp
  refine ⟨i', hii',
    { V := V'
      isAffine_V := hV'aff
      φ := j' ≫ π'.hom
      isSurjective_φ := hφsu
      isEtale_φ := hφet
      Y := Y'
      j := j'
      π := π'.hom
      isOpenImmersion_j := isOpenImmersion_of_iso_openComplement Z' rfl j' e rfl
      isFinite_π := hπ'fin
      comp_eq := rfl
      I := definingIdealSheaf B S hS Y' Z'
      isFiniteTypeQuasicoherent_I :=
        ⟨isQuasicoherentOnSite_definingIdealSheaf B S hS Y' Z', hZ'ft⟩
      idealZeroLocus_I := idealZeroLocus_eq_compl_range_of_iso_openComplement Z' rfl j' e rfl },
    g', gL, hπ'fp, sq', sqL, hgL, rfl⟩

end AlgebraicGeometry.Space

end
