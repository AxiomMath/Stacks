module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartDirectImageTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenInterchange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIrreducibleIdealInjection
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplementChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# An isomorphism over the complement of `V(𝒦)`, read on an étale chart

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces, `𝒦 ⊆ 𝒪_Y` the ideal of a closed
subspace `Z`, and suppose `f` is an isomorphism over the open complement `Y ∖ Z`.  Over an étale
chart `V` of `Y` with chart scheme `T`, the base change `f_V : V ×_Y X ⟶ T` is then an isomorphism
over the complement of `V(𝒦(V))` in `T`
(`AlgebraicGeometry.Space.C1573.isIso_chartBaseChangeSchemeHom_restrict_compl_support`).

For `g ∈ 𝒦(V)` the basic-open chart `D(g)` of `V` carries the unit ideal, so it maps into the unit
locus of `𝒦`, which is the point set of `Y ∖ Z`; it factors through `Y ∖ Z` by Stacks 03IE, and
the base change of `f` to it is a base change of the isomorphism over `Y ∖ Z`.  By the interchange
of chart base change and Zariski opens this base change is the restriction of `f_V` over `D(g)`,
and these opens cover the complement of `V(𝒦(V))`.
-/

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
  (K : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
  (Z : ClosedSubspaces B S hS Y.1) (hZ : definingIdealSheaf B S hS Y Z = K)
  (hiso : IsIso ((openComplement B S hS Z.1).fromPreimage f.hom))
  (V : SmallEtale B S hS Y.1) [IsAffine (chartScheme V)]

include hZ hiso in
/-- If an étale chart of `Y` carries the unit ideal of `𝒦`, the base change of `f` to it is an
isomorphism. -/
theorem C1573.isIso_chartBaseChangeSchemeHom_of_eq_top (W : SmallEtale B S hS Y.1)
    (hW : K.obj (op W) = ⊤) : IsIso (chartBaseChangeSchemeHom B S hS f hf W) := by
  have hpts : Set.range (pointsMap B S hS (yoneda.obj W.obj.left) W.1.hom) ⊆
      Set.range (pointsMap B S hS (openComplement B S hS Z.1).toFunctor
        (openComplement B S hS Z.1).ι) := by
    rw [range_pointsMap_ι_openComplement_eq_idealUnitLocus, hZ]
    exact range_subset_idealUnitLocus_of_eq_top B S hS Y K W hW
  obtain ⟨ℓ, hℓ⟩ := (factorsThrough_openSubspace_iff_points B S hS Y.2
    (isAlgebraicSpace_yoneda B S hS W.obj.left) (openComplement B S hS Z.1)
    (isOpenSubspace_openComplement B S hS Y.2 Z.1 Z.2) W.1.hom).2 hpts
  have hs : IsPullback (hf.fst W.1.hom) (yoneda.map (hf.snd W.1.hom)) f.hom
      (ℓ ≫ (openComplement B S hS Z.1).ι) := hℓ.symm ▸ hf.isPullback W.1.hom
  have ht := (Subfunctor.isPullback_preimage f.hom (openComplement B S hS Z.1)).flip
  have hleft := IsPullback.of_right' hs ht
  have : IsIso (yoneda.map (hf.snd W.1.hom)) := hleft.isIso_snd_of_isIso
  have : IsIso (hf.snd W.1.hom) := isIso_of_reflects_iso _ yoneda
  exact Functor.map_isIso (BigFppfOver.toScheme B S hS) (hf.snd W.1.hom)

omit [IsAffine (chartScheme V)] in
/-- If the base change of `f` to the chart cut out by a Zariski open `O` of the chart scheme of
`V` is an isomorphism, so is the restriction of `f_V` over `O`. -/
theorem C1573.isIso_morphismRestrict_of_isIso_openChart (O : (chartScheme V).Opens)
    (h : IsIso (chartBaseChangeSchemeHom B S hS f hf (openChart B S hS Y.1 V O))) :
    IsIso (chartBaseChangeSchemeHom B S hS f hf V ∣_ O) := by
  have h1 := congrArg (BigFppfOver.toScheme B S hS).map
    (smallBaseChangeOpenChartLeftIso_hom_comp_projection B S hS f hf V O)
  rw [Functor.map_comp] at h1
  have h2 : (BigFppfOver.toScheme B S hS).map (openChartSmallBaseChangeProjection B S hS f hf V O) =
      chartBaseChangeSchemeHom B S hS f hf V ∣_ O := rfl
  rw [h2] at h1
  have h3 : IsIso ((BigFppfOver.toScheme B S hS).map
      (smallBaseChangeOpenChartLeftIso B S hS f hf V O).hom ≫
        chartBaseChangeSchemeHom B S hS f hf V ∣_ O) :=
    (congrArg (fun k => IsIso k) h1).mpr h
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    ((BigFppfOver.toScheme B S hS).mapIso
      (smallBaseChangeOpenChartLeftIso B S hS f hf V O)).isIso_hom h3

include hZ hiso in
/-- `f_V` is an isomorphism over the complement of `V(𝒦(V))`. -/
theorem C1573.isIso_chartBaseChangeSchemeHom_restrict_compl_support :
    IsIso (chartBaseChangeSchemeHom B S hS f hf V ∣_
      (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V K)).support.compl) := by
  have hsupp : ∀ x : chartScheme V, x ∈ (Scheme.IdealSheafData.ofIdealTop
      (chartTopIdeal B S hS V K)).support ↔
        ∀ g ∈ chartTopIdeal B S hS V K, x ∉ (chartScheme V).basicOpen g := fun x => by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top _⟩) trivial,
      Stacks.Coherent.ofIdealTop_ideal_top, Scheme.mem_zeroLocus_iff]
    rfl
  have hD : ∀ g ∈ chartTopIdeal B S hS V K, (chartScheme V).basicOpen g ≤
      (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V K)).support.compl :=
    fun g hg y hy hys => (hsupp y).1 hys g hg hy
  have hDiso : ∀ g ∈ chartTopIdeal B S hS V K,
      IsIso (chartBaseChangeSchemeHom B S hS f hf V ∣_ (chartScheme V).basicOpen g) := by
    intro g hg
    refine isIso_morphismRestrict_of_isIso_openChart B S hS f hf V _ ?_
    refine isIso_chartBaseChangeSchemeHom_of_eq_top B S hS f hf K Z hZ hiso _ ?_
    exact Ideal.eq_top_of_isUnit_mem _ (K.map_mem (openChartInclusion B S hS Y.1 V _).op hg)
      (isUnit_chartRestrict_openChartInclusion_basicOpen B S hS Y.2 V ‹_› g)
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_
  obtain ⟨g, hg, hx⟩ : ∃ g ∈ chartTopIdeal B S hS V K, x.1 ∈ (chartScheme V).basicOpen g := by
    by_contra hcon
    push Not at hcon
    exact x.2 ((hsupp x.1).2 hcon)
  refine ⟨(Scheme.Opens.ι _) ⁻¹ᵁ (chartScheme V).basicOpen g, hx, ?_⟩
  have hU : Scheme.Opens.ι (X := chartScheme V)
      (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V K)).support.compl ''ᵁ
      (Scheme.Opens.ι (X := chartScheme V)
        (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V K)).support.compl ⁻¹ᵁ
        (chartScheme V).basicOpen g) = (chartScheme V).basicOpen g := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 (hD g hg)
  refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ hU)).2 ?_
  exact (MorphismProperty.isomorphisms.iff _).2 (hDiso g hg)

end AlgebraicGeometry.Space

end
