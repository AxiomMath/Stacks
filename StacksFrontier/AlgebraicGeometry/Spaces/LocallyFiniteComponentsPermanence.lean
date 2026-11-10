module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactMonomorphicFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaIrreducibleComponents
public import StacksFrontier.Topology.Dimension.LocalDimensionComponents
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension

/-!
# Local finiteness of irreducible components for normalizations

Let `S` be a scheme and let `F` be an algebraic space over `S` satisfying the equivalent
conditions of Stacks 0BB1. The normalization `F^ν` of `F` (Stacks 07U4) satisfies them again:
along a surjective étale scheme chart `U ⟶ F` the normalization base changes to the
normalization `U^ν` of `U`, which is a disjoint union of integral schemes (Stacks 035Q), and a
quasi-compact open of a disjoint union of irreducible schemes meets only finitely many of them.

## Main results

* `AlgebraicGeometry.Space.NormalizationData.hasLocallyFiniteIrreducibleComponents_space`: the
  normalization of an algebraic space satisfying the conditions of Stacks 0BB1 satisfies them.

## References

* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A set has finitely many irreducible components if its image under a homeomorphism does. -/
private theorem finite_irreducibleComponents_of_image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (S : Set X) (h : (irreducibleComponents (e '' S)).Finite) :
    (irreducibleComponents S).Finite :=
  let e' := e.image S
  (ncard_irreducibleComponents_le_of_surjective e'.symm e'.symm.continuous e'.symm.surjective h).1

/-- **The quasi-compact opens of the normalization of a scheme have finitely many irreducible
components.** The normalization is a disjoint union of integral schemes, by Stacks 035Q. -/
theorem Scheme.finite_irreducibleComponents_normalizationScheme {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (V : (X.normalizationScheme hX).Opens)
    (hV : IsCompact (V : Set (X.normalizationScheme hX))) :
    (irreducibleComponents V).Finite := by
  obtain ⟨ι, Y, -, hYint, ⟨e⟩⟩ := X.exists_iso_sigma_isIntegral_isNormal_normalizationScheme hX
  have : ∀ i, IrreducibleSpace (Y i) := fun i => inferInstance
  let h : X.normalizationScheme hX ≃ₜ (∐ Y : Scheme.{u}) := e.hom.homeomorph
  let V' : (∐ Y : Scheme.{u}).Opens := ⟨h '' (V : Set (X.normalizationScheme hX)),
    h.isOpenMap _ V.2⟩
  have hV' : IsCompact (V' : Set (∐ Y : Scheme.{u})) := hV.image h.continuous
  have hfin := finite_irreducibleComponents_of_isCompact_sigma Y V' hV'
  exact finite_irreducibleComponents_of_image h (V : Set (X.normalizationScheme hX)) hfin

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- The trace of an irreducible set on an open set it meets is irreducible in the subspace. -/
theorem isIrreducible_preimage_subtypeVal_of_isOpen {C O : Set X} (hC : IsIrreducible C)
    (hO : IsOpen O) {c : X} (hc : c ∈ C) (hcO : c ∈ O) :
    IsIrreducible (Subtype.val ⁻¹' C : Set O) := by
  refine ⟨⟨⟨c, hcO⟩, hc⟩, ?_⟩
  rintro U V hU hV ⟨a, haC, haU⟩ ⟨b, hbC, hbV⟩
  obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
  obtain ⟨V', hV', rfl⟩ := isOpen_induced_iff.1 hV
  obtain ⟨d, hdC, ⟨hdU, hdO⟩, hdV, -⟩ := hC.2 (U' ∩ O) (V' ∩ O) (hU'.inter hO) (hV'.inter hO)
    ⟨a.1, haC, haU, a.2⟩ ⟨b.1, hbC, hbV, b.2⟩
  exact ⟨⟨d, hdO⟩, hdC, hdU, hdV⟩

/-- **A space covered by finitely many open subsets, each with finitely many irreducible
components, has finitely many irreducible components.** Every irreducible component of the space
meets one of the open subsets, and is the closure of an irreducible component of it. -/
theorem finite_irreducibleComponents_of_isOpen_cover {ι : Type*} [Finite ι] (O : ι → Set X)
    (hO : ∀ j, IsOpen (O j)) (hcov : ∀ x, ∃ j, x ∈ O j)
    (hfin : ∀ j, (irreducibleComponents (O j)).Finite) :
    (irreducibleComponents X).Finite := by
  refine (Set.finite_iUnion fun j => (hfin j).image
    (fun D : Set (O j) => closure (Subtype.val '' D))).subset ?_
  intro C hC
  obtain ⟨c, hc⟩ := hC.1.nonempty
  obtain ⟨j, hj⟩ := hcov c
  obtain ⟨D, hD, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_preimage_subtypeVal_of_isOpen hC.1 (hO j) hc hj)
  have hclD := closure_image_mem_irreducibleComponents_of_isOpen (hO j) hD
  have hCsub : C ⊆ closure (Subtype.val '' D) := by
    refine (subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.isPreirreducible (hO j)
      ⟨c, hc, hj⟩).trans (closure_mono ?_)
    rintro x ⟨hxC, hxO⟩
    exact ⟨⟨x, hxO⟩, hsub hxC, rfl⟩
  exact Set.mem_iUnion.2 ⟨j, D, hD, le_antisymm (hC.2 hclD.1 hCsub) hCsub⟩

end Topology

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The normalization of an algebraic space satisfying the equivalent conditions of
Stacks 0BB1 satisfies them again.** Along a surjective étale scheme chart of the space, the
normalization data provide a surjective étale scheme chart of the normalization which is the
normalization of the chart, and the quasi-compact opens of the normalization of a scheme have
finitely many irreducible components. -/
theorem NormalizationData.hasLocallyFiniteIrreducibleComponents_space
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (N : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) :
    HasLocallyFiniteIrreducibleComponents B S hS N.space := by
  obtain ⟨U, f, hfs, hfe⟩ := hF.exists_atlas
  have hfs' := isSurjective_of_presheafSurjective B S hS f hfs
  have hfe' := isEtale_of_presheaf_etale B S hS hfe
  obtain ⟨hU, Uν, p, g, e, -, hsq⟩ := N.chart U f hfs' hfe'
  refine (exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents B S hS
    N.isAlgebraicSpace).mp ⟨Uν, g, ?_, ?_, fun V hV => ?_⟩
  · -- `g` is surjective, being a base change of `f`
    intro n
    obtain ⟨u, hu⟩ := hfs' (pointsMap B S hS _ N.hom n)
    let sq : IsPullback (ObjectProperty.homMk g : (⟨yoneda.obj Uν,
          isAlgebraicSpace_yoneda B S hS Uν⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨N.space, N.isAlgebraicSpace⟩)
        (ObjectProperty.homMk (yoneda.map p) : (⟨yoneda.obj Uν,
          isAlgebraicSpace_yoneda B S hS Uν⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
        (ObjectProperty.homMk N.hom : (⟨N.space, N.isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨F, hF⟩)
        (ObjectProperty.homMk f : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩) :=
      IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsq.w) hsq
    obtain ⟨w, hw, -⟩ := exists_point_of_isPullback B S hS sq n u hu.symm
    exact ⟨w, hw⟩
  · exact isEtale_of_isPullback_yoneda B S hS hsq.flip hfe'
  · -- the chart is the normalization of `U`
    have hV' := Scheme.finite_irreducibleComponents_normalizationScheme hU (e.hom ''ᵁ V)
      (hV.image e.hom.continuous)
    exact finite_irreducibleComponents_of_image e.hom.homeomorph _ hV'

attribute [local instance] pointTopology

set_option synthInstance.maxHeartbeats 80000 in
-- instance search for pullbacks of presheaves on the big fppf site
/-- **The conditions of Stacks 0BB1 are étale local.** If finitely many étale morphisms
`gⱼ : Vⱼ ⟶ F` from algebraic spaces satisfying the conditions of Stacks 0BB1 are jointly
surjective on points, then `F` satisfies them. A quasi-compact open of an étale scheme chart of
`F` is covered by the images of finitely many affine opens of scheme charts of the base changes
of the `gⱼ`, each of which has finitely many irreducible components, and so has the union. -/
theorem hasLocallyFiniteIrreducibleComponents_of_isEtale_cover
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) {ι : Type*}
    (V : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : ∀ j, IsAlgebraicSpace B S hS (V j))
    (g : ∀ j, V j ⟶ F) (hg : ∀ j, IsEtale B S hS (g j))
    (hfin : ∀ j, HasLocallyFiniteIrreducibleComponents B S hS (V j))
    (hcov : ∀ x : points B S hS F, ∃ j v, pointsMap B S hS (V j) (g j) v = x) :
    HasLocallyFiniteIrreducibleComponents B S hS F := by
  intro U f hf Vq hVq
  have hUalg := isAlgebraicSpace_yoneda B S hS U
  -- the base changes of the `gⱼ` to `U` and scheme atlases of them
  have hY : ∀ j, IsAlgebraicSpace B S hS (pullback f (g j)) := fun j =>
    isAlgebraicSpace_pullback B S hS f (g j) hUalg (hV j) hF
  choose C c hcs hce using fun j => (hY j).exists_atlas
  set μ : ∀ j, yoneda.obj (C j) ⟶ yoneda.obj U := fun j => c j ≫ pullback.fst f (g j)
  have hμ : ∀ j, IsEtale B S hS (μ j) := fun j =>
    isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS (hce j))
      (isEtale_pullback_fst B S hS hUalg hF (hV j) f (g j) (hg j))
  have hpb := fun j : ι => AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk f : (⟨yoneda.obj U, hUalg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
    (ObjectProperty.homMk (g j) : (⟨V j, hV j⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
  have hCfin : ∀ j (W : ((BigFppfOver.toScheme B S hS).obj (C j)).Opens),
      IsCompact (W : Set ((BigFppfOver.toScheme B S hS).obj (C j))) →
        (irreducibleComponents W).Finite := fun j =>
    hfin j (C j) (c j ≫ pullback.snd f (g j)) (isEtale_comp B S hS
      (isEtale_of_presheaf_etale B S hS (hce j)) (isEtale_of_isPullback B S hS _ _ _ _ (hpb j) hf))
  -- every point of the chart comes from one of the atlases
  have hsurj : ∀ p : points B S hS (yoneda.obj U), ∃ j q,
      pointsMap B S hS (yoneda.obj (C j)) (μ j) q = p := by
    intro p
    obtain ⟨j, v, hv⟩ := hcov (pointsMap B S hS _ f p)
    obtain ⟨y, hy, -⟩ := exists_point_of_isPullback B S hS (hpb j) p v hv.symm
    obtain ⟨q, hq⟩ := (surjective_iff_surjective_pointsMap B S hS _ (hY j) (C j) (c j)).mp
      (hcs j) y
    refine ⟨j, q, ?_⟩
    simp only [μ, pointsMap_comp_apply, hq]
    exact hy
  -- the compact open, read on points
  set hU := schemePointsHomeomorph B S hS U
  set Vq' : Set (points B S hS (yoneda.obj U)) := hU.symm '' (Vq : Set _)
  have hVq'c : IsCompact Vq' := hVq.image hU.symm.continuous
  -- a neighbourhood of each of its points: the image of an affine open of an atlas
  have hnbhd : ∀ p : Vq', ∃ (j : ι) (A : ((BigFppfOver.toScheme B S hS).obj (C j)).Opens),
      IsCompact (A : Set ((BigFppfOver.toScheme B S hS).obj (C j))) ∧
        p.1 ∈ pointsMap B S hS _ (μ j) ''
          ((schemePointsHomeomorph B S hS (C j)).symm ''
            (A : Set ((BigFppfOver.toScheme B S hS).obj (C j)))) ∧
        pointsMap B S hS _ (μ j) ''
          ((schemePointsHomeomorph B S hS (C j)).symm ''
            (A : Set ((BigFppfOver.toScheme B S hS).obj (C j)))) ⊆ Vq' := by
    rintro ⟨p, hp⟩
    obtain ⟨j, q, hq⟩ := hsurj p
    set hC := schemePointsHomeomorph B S hS (C j)
    have hopen : IsOpen (hC '' (pointsMap B S hS _ (μ j) ⁻¹' Vq')) :=
      hC.isOpenMap _ ((hU.symm.isOpenMap _ Vq.2).preimage (continuous_pointsMap B S hS _))
    obtain ⟨_, ⟨A, hA, rfl⟩, hqA, hAsub⟩ :=
      ((BigFppfOver.toScheme B S hS).obj (C j)).isBasis_affineOpens.exists_subset_of_mem_open
        (⟨q, (by rw [Set.mem_preimage, hq]; exact hp), rfl⟩ :
          hC q ∈ hC '' (pointsMap B S hS _ (μ j) ⁻¹' Vq')) hopen
    refine ⟨j, A, hA.isCompact, ⟨q, ⟨hC q, hqA, hC.symm_apply_apply q⟩, hq⟩, ?_⟩
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨q', hq', hq'a⟩ := hAsub ha
    rw [← hq'a, hC.symm_apply_apply]
    exact hq'
  choose j A hAc hpA hAsub using hnbhd
  set O : Vq' → Set (points B S hS (yoneda.obj U)) := fun p => pointsMap B S hS _ (μ (j p)) ''
    ((schemePointsHomeomorph B S hS (C (j p))).symm ''
      (A p : Set ((BigFppfOver.toScheme B S hS).obj (C (j p)))))
  have hOopen : ∀ p, IsOpen (O p) := fun p =>
    isOpenMap_pointsMap_of_isEtale B S hS _ (isAlgebraicSpace_yoneda B S hS _) hUalg (hμ (j p))
      _ ((schemePointsHomeomorph B S hS (C (j p))).symm.isOpenMap _ (A p).2)
  obtain ⟨t, ht⟩ := hVq'c.elim_finite_subcover O hOopen fun p hp => Set.mem_iUnion.2
    ⟨⟨p, hp⟩, hpA ⟨p, hp⟩⟩
  -- the finitely many neighbourhoods cover `Vq'` and have finitely many components each
  have hfinVq' : (irreducibleComponents Vq').Finite := by
    refine finite_irreducibleComponents_of_isOpen_cover (ι := t)
      (fun p => Subtype.val ⁻¹' O p.1) (fun p => (hOopen p.1).preimage continuous_subtype_val)
      (fun x => ?_) (fun p => ?_)
    · obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (ht x.2)
      exact ⟨⟨p, hp⟩, hxp⟩
    · refine (ncard_irreducibleComponents_le_of_surjective
        (X := (A p.1 : Set ((BigFppfOver.toScheme B S hS).obj (C (j p.1)))))
        (fun a => ⟨⟨pointsMap B S hS _ (μ (j p.1))
            ((schemePointsHomeomorph B S hS (C (j p.1))).symm a.1),
          hAsub p.1 ⟨_, ⟨a.1, a.2, rfl⟩, rfl⟩⟩, ⟨_, ⟨a.1, a.2, rfl⟩, rfl⟩⟩)
        ?_ ?_ (hCfin (j p.1) (A p.1) (hAc p.1))).1
      · exact Continuous.subtype_mk (Continuous.subtype_mk ((continuous_pointsMap B S hS _).comp
          ((schemePointsHomeomorph B S hS _).symm.continuous.comp continuous_subtype_val)) _) _
      · rintro ⟨⟨x, hx⟩, hxO⟩
        obtain ⟨_, ⟨a, ha, rfl⟩, hxa⟩ := hxO
        refine ⟨⟨a, ha⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact hxa
  -- back to the scheme
  have hmem : ∀ x : Vq', hU x.1 ∈ (Vq : Set ((BigFppfOver.toScheme B S hS).obj U)) := by
    rintro ⟨_, y, hy, rfl⟩
    rw [hU.apply_symm_apply]
    exact hy
  exact (ncard_irreducibleComponents_le_of_surjective
    (fun x : Vq' => (⟨hU x.1, hmem x⟩ : (Vq : Set ((BigFppfOver.toScheme B S hS).obj U))))
    (Continuous.subtype_mk (hU.continuous.comp continuous_subtype_val) hmem)
    (fun y => ⟨⟨hU.symm y.1, y.1, y.2, rfl⟩, Subtype.ext (hU.apply_symm_apply _)⟩)
    hfinVq').1

/-- **The conditions of Stacks 0BB1 are étale local**, for two étale morphisms which are jointly
surjective on points. -/
theorem hasLocallyFiniteIrreducibleComponents_of_isEtale_cover_two
    {F V₁ V₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hV₁ : IsAlgebraicSpace B S hS V₁) (hV₂ : IsAlgebraicSpace B S hS V₂)
    (g₁ : V₁ ⟶ F) (g₂ : V₂ ⟶ F) (hg₁ : IsEtale B S hS g₁) (hg₂ : IsEtale B S hS g₂)
    (h₁ : HasLocallyFiniteIrreducibleComponents B S hS V₁)
    (h₂ : HasLocallyFiniteIrreducibleComponents B S hS V₂)
    (hcov : ∀ x : points B S hS F, x ∈ Set.range (pointsMap B S hS V₁ g₁) ∨
      x ∈ Set.range (pointsMap B S hS V₂ g₂)) :
    HasLocallyFiniteIrreducibleComponents B S hS F := by
  refine hasLocallyFiniteIrreducibleComponents_of_isEtale_cover B S hS hF
    (fun b : Bool => Bool.rec V₁ V₂ b) (fun b => by cases b <;> assumption)
    (fun b => Bool.rec (motive := fun b => Bool.rec V₁ V₂ b ⟶ F) g₁ g₂ b)
    (fun b => by cases b <;> assumption) (fun b => by cases b <;> assumption) fun x => ?_
  rcases hcov x with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact ⟨false, v, hv⟩
  · exact ⟨true, v, hv⟩

/-- **An algebraic space satisfying the conditions of Stacks 0BB1 is decent as soon as it has a
decent open subspace with dense point set.** Its points of codimension `0` lie in the open
subspace, where they are represented by monomorphisms from spectra of fields, and those stay
monomorphisms after composition with the inclusion; Stacks 0ENA then gives decency. -/
theorem isDecentSpace_of_dense_isOpenSubspace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS F) {O : Subfunctor F}
    (hO : IsOpenSubspace B S hS O) (hd : DenseRange (pointsMap B S hS O.toFunctor O.ι))
    (hOdec : IsDecentSpace B S hS O.toFunctor) : IsDecentSpace B S hS F := by
  refine isDecentSpace_of_hasLocallyFiniteIrreducibleComponents B S hS hF hfin fun x hx => ?_
  obtain ⟨y, rfl⟩ := mem_range_pointsMap_ι_of_localRingDimension_eq_zero B S hS hF hfin hO hd x hx
  obtain ⟨p, hp, hmono⟩ := (hOdec y).hasMonomorphicFieldRepresentative B S hS O.toFunctor
  refine ⟨FieldValuedPoint.map B S hS _ O.ι p, ?_, ?_⟩
  · rw [← pointsMap_class, hp]
  · rw [fieldMorphism_map]
    exact mono_comp' hmono inferInstance

end Space

end AlgebraicGeometry

end
