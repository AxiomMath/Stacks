module

public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Compact.Image
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.Topology.Spectral.BijectionHomeomorph
public import StacksFrontier.Topology.Spectral.ConstructibleTopology
public import StacksFrontier.Topology.Spectral.LimitGeneralizations

/-!
# Local constructibility on a quasi-separated algebraic space

For a quasi-separated algebraic space `X` over `S` a subset of its point space is étale
locally constructible, in the sense of Tag 0ECU, exactly when it is locally constructible for
the topology of Tag 03BX.

## Main results

* `AlgebraicGeometry.Space.isEtaleLocallyConstructible_iff_isLocallyConstructible`:
  **Stacks 0ECZ**, the two notions of local constructibility agree.

## Implementation notes

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance and is
made a local instance here.

Quasi-separatedness is taken in the absolute sense of Tag 0AHR. The containment of the
terminal scheme in the site that the predicate mentions is not a hypothesis, because
`AlgebraicGeometry.BigFppfSite.contains_terminal` discharges it for every big fppf site.

Both directions reduce to spectral spaces, which is where quasi-separatedness enters: a
quasi-compact open subspace of `X` has spectral point space by Tag 0A4G, and so does an affine
étale chart. On spectral spaces constructibility is a clopen condition for the constructible
topology, and a spectral map is continuous and — between spectral spaces — closed for those
topologies. Hence constructibility passes to preimages along a spectral map and descends along
a surjective one.

Going from étale-local to topological constructibility, a Zariski cover of `X` by open
subspaces with affine étale charts reduces the statement to one open subspace at a time, where
the surjective chart gives descent and Tag 09YD transports the result back to `X`. In the
other direction only affine charts have to be treated, by Tag 0ECT, and such a chart factors
through the open subspace cut out by the image of its point space, which is quasi-compact and
quasi-separated, so the chart becomes a spectral map between spectral spaces.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 0A4G](https://stacks.math.columbia.edu/tag/0A4G)
* [Stacks Project, Tag 0ECT](https://stacks.math.columbia.edu/tag/0ECT)
* [Stacks Project, Tag 0ECU](https://stacks.math.columbia.edu/tag/0ECU)
* [Stacks Project, Tag 0ECZ](https://stacks.math.columbia.edu/tag/0ECZ)
* [Stacks Project, Tag 0EMK](https://stacks.math.columbia.edu/tag/0EMK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

/-- A constructible subset of a spectral space pulls back along a spectral map of spectral
spaces to a constructible subset: constructibility is clopenness for the constructible
topology, and a spectral map is continuous for the constructible topologies. -/
private theorem isConstructible_preimage_of_isSpectralMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [SpectralSpace X] [SpectralSpace Y]
    {f : X → Y} (hf : IsSpectralMap f) {E : Set Y} (hE : IsConstructible E) :
    IsConstructible (f ⁻¹' E) :=
  isConstructible_of_isClopen_constructibleTopology
    ⟨@IsClosed.preimage X Y (constructibleTopology X) (constructibleTopology Y) f
        hf.continuous_constructibleTopology E hE.isClosed_constructibleTopology,
      @IsOpen.preimage X Y (constructibleTopology X) (constructibleTopology Y) f
        hf.continuous_constructibleTopology E hE.isOpen_constructibleTopology⟩

/-- Constructibility descends along a surjective spectral map of spectral spaces: the preimage
is clopen for the constructible topology of the source and a spectral map of spectral spaces is
closed for the constructible topologies, so the set and its complement are both closed in the
target. -/
private theorem isConstructible_of_isSpectralMap_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [SpectralSpace X] [SpectralSpace Y]
    {f : X → Y} (hf : IsSpectralMap f) (hsurj : Function.Surjective f) {E : Set Y}
    (hE : IsConstructible (f ⁻¹' E)) : IsConstructible E := by
  have hclosed : IsClosed[constructibleTopology Y] E := by
    rw [← Set.image_preimage_eq E hsurj]
    exact hf.isClosedMap_constructibleTopology _ hE.isClosed_constructibleTopology
  have hcompl : IsClosed[constructibleTopology Y] Eᶜ := by
    rw [← Set.image_preimage_eq Eᶜ hsurj, Set.preimage_compl]
    exact hf.isClosedMap_constructibleTopology _
      (@IsOpen.isClosed_compl X (constructibleTopology X) _ hE.isOpen_constructibleTopology)
  exact isConstructible_of_isClopen_constructibleTopology
    ⟨hclosed, by simpa using hcompl.isOpen_compl⟩

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An open subspace of a quasi-separated algebraic space over `S` is quasi-separated: the
inclusion of a subfunctor is a monomorphism, hence a quasi-separated morphism. -/
private theorem isAbsolutelyQuasiSeparated_toFunctor_of_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    {A : Subfunctor X} (hA : IsOpenSubspace B S hS A) :
    IsAbsolutelyQuasiSeparated B S hS B.contains_terminal A.toFunctor :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hA.1 hXqs
    (isQuasiSeparated_of_mono B S hS A.ι inferInstance)

/-- The point space of an affine object of the site over `S` is spectral. -/
private theorem spectralSpace_points_yoneda_of_isAffine (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    SpectralSpace (points B S hS (yoneda.obj U)) :=
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  spectralSpace_points_of_isQuasiCompactSpace_isAbsolutelyQuasiSeparated B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) (isQuasiCompactSpace_yoneda_of_isAffine B S hS U hU)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj U)
      B.contains_terminal ⟨U, inferInstance, ⟨Functor.RepresentableBy.yoneda U⟩⟩)

/-- The set of points of a subfunctor is the image of the point space of any chart of it that
is surjective on points. -/
private theorem range_pointsMap_ι_eq_range_comp
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A : Subfunctor X} {U : BigFppfOver B S hS}
    {f : yoneda.obj U ⟶ A.toFunctor}
    (hfsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) f)) :
    Set.range (pointsMap B S hS A.toFunctor A.ι) =
      Set.range (pointsMap B S hS (yoneda.obj U) (f ≫ A.ι)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨a, rfl⟩
    obtain ⟨u, rfl⟩ := hfsurj a
    exact ⟨u, pointsMap_comp_apply B S hS f A.ι u⟩
  · rintro _ ⟨u, rfl⟩
    exact ⟨pointsMap B S hS (yoneda.obj U) f u, (pointsMap_comp_apply B S hS f A.ι u).symm⟩

/-- An open subspace of an algebraic space over `S` admitting a chart from an affine object of
the site which is surjective on points is quasi-compact. -/
private theorem isQuasiCompactSpace_of_affine_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {A : Subfunctor X} (hA : IsOpenSubspace B S hS A) (U : BigFppfOver B S hS)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {f : yoneda.obj U ⟶ A.toFunctor}
    (hfsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) f)) :
    IsQuasiCompactSpace B S hS A.toFunctor := by
  have : CompactSpace (points B S hS (yoneda.obj U)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).mp
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS U hUaff)
  refine isQuasiCompactSpace_of_isCompact_range B S hS hX hA ?_
  rw [range_pointsMap_ι_eq_range_comp B S hS hfsurj, ← Set.image_univ]
  exact isCompact_univ.image (continuous_pointsMap B S hS (f ≫ A.ι))

/-- A morphism from a quasi-compact algebraic space to a quasi-separated algebraic space is
quasi-compact, hence a spectral map on points. -/
private theorem isSpectralMap_pointsMap_of_isQuasiCompactSpace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hXqc : IsQuasiCompactSpace B S hS X) (f : X ⟶ Y) :
    IsSpectralMap (pointsMap B S hS X f) :=
  ⟨continuous_pointsMap B S hS f, isQuasiCompactMap_pointsMap B S hS hX hY f
    (isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal hY hYqs hXqc f)⟩

/-- The point map of the inclusion of an open subspace is an open embedding as soon as its range
is open. -/
private theorem isOpenEmbedding_pointsMap_ι
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {A : Subfunctor X} (hA : IsOpenSubspace B S hS A)
    (hopen : IsOpen (Set.range (pointsMap B S hS A.toFunctor A.ι))) :
    IsOpenEmbedding (pointsMap B S hS A.toFunctor A.ι) :=
  ⟨isEmbedding_pointsMap_of_isImmersion B S hS hX A.ι
    (isImmersion_of_isOpenImmersion B S hS hA.2), hopen⟩

/-- Half of Tag 0ECZ on one open subspace: if `E` is étale locally constructible then its
inverse image on a quasi-compact open subspace `A` with an affine surjective étale chart `U` is
constructible. The chart is a surjective spectral map of spectral spaces and the inverse image
of `E` on `U` is constructible, so constructibility descends to `A`. -/
private theorem isConstructible_preimage_ι_of_isEtaleLocallyConstructible
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    {A : Subfunctor X} (hA : IsOpenSubspace B S hS A) (U : BigFppfOver B S hS)
    (f : yoneda.obj U ⟶ A.toFunctor)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hfsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hfetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    {E : Set (points B S hS X)} (hE : IsEtaleLocallyConstructible B S hS X E) :
    IsConstructible (pointsMap B S hS A.toFunctor A.ι ⁻¹' E) := by
  have hUalg := isAlgebraicSpace_yoneda B S hS U
  have hφsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) f) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS A.toFunctor hA.1 U f).mp hfsurj
  have hAqs := isAbsolutelyQuasiSeparated_toFunctor_of_isOpenSubspace B S hS hXqs hA
  have hAqc := isQuasiCompactSpace_of_affine_chart B S hS hX hA U hUaff hφsurj
  have : SpectralSpace (points B S hS A.toFunctor) :=
    spectralSpace_points_of_isQuasiCompactSpace_isAbsolutelyQuasiSeparated B S hS A.toFunctor
      hA.1 hAqc hAqs
  have : SpectralSpace (points B S hS (yoneda.obj U)) :=
    spectralSpace_points_yoneda_of_isAffine B S hS U hUaff
  -- The chart is quasi-compact by Tag 073B, so a spectral map on points by Tag 0EMK.
  have hφspec : IsSpectralMap (pointsMap B S hS (yoneda.obj U) f) :=
    isSpectralMap_pointsMap_of_isQuasiCompactSpace B S hS hUalg hA.1 hAqs
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS U hUaff) f
  refine isConstructible_of_isSpectralMap_surjective hφspec hφsurj ?_
  have hEq : pointsMap B S hS (yoneda.obj U) f ⁻¹'
      (pointsMap B S hS A.toFunctor A.ι ⁻¹' E) =
        pointsMap B S hS (yoneda.obj U) (f ≫ A.ι) ⁻¹' E := by
    ext x
    simp only [Set.mem_preimage, pointsMap_comp_apply]
  rw [hEq]
  exact (hE U (f ≫ A.ι) (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hfetale)
    (isEtale_ι_of_isOpenSubspace hA))).isConstructible

/-- Half of Tag 0ECZ on one affine chart: if `E` is locally constructible then its inverse
image on an affine étale chart is constructible. The chart factors through the open subspace
cut out by the image of its point space, which is quasi-compact and quasi-separated, so both
point spaces are spectral and the factored chart is a spectral map. -/
private theorem isConstructible_preimage_of_isLocallyConstructible
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    {E : Set (points B S hS X)} (hE : IsLocallyConstructible E)
    (U : BigFppfOver B S hS) (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (f : yoneda.obj U ⟶ X) (hf : IsEtale B S hS f) :
    IsConstructible (pointsMap B S hS (yoneda.obj U) f ⁻¹' E) := by
  classical
  have hUalg := isAlgebraicSpace_yoneda B S hS U
  have : SpectralSpace (points B S hS (yoneda.obj U)) :=
    spectralSpace_points_yoneda_of_isAffine B S hS U hUaff
  set φ := pointsMap B S hS (yoneda.obj U) f with hφ
  have hφcont : Continuous φ := continuous_pointsMap B S hS f
  have hφqc := (isSpectralMap_pointsMap_of_isQuasiCompactSpace B S hS hUalg hX hXqs
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS U hUaff) f).2
  -- The image of the chart is a quasi-compact open subset of the point space of `X`.
  have hCopen : IsOpen (Set.range φ) :=
    (isOpenMap_pointsMap_of_isEtale B S hS f hUalg hX hf).isOpen_range
  have hCcompact : IsCompact (Set.range φ) := isCompact_range hφcont
  set A : Subfunctor X :=
    ((openSubspacesOrderIso B S hS X hX).symm ⟨Set.range φ, hCopen⟩).1 with hA'
  have hA : IsOpenSubspace B S hS A :=
    ((openSubspacesOrderIso B S hS X hX).symm ⟨Set.range φ, hCopen⟩).2
  set e := pointsMap B S hS A.toFunctor A.ι with he
  have hrangeA : Set.range e = Set.range φ := by
    rw [he, ← openSubspacesOrderIso_apply B S hS X hX
      ((openSubspacesOrderIso B S hS X hX).symm ⟨Set.range φ, hCopen⟩)]
    exact congrArg (fun O : Opens _ ↦ O.carrier)
      ((openSubspacesOrderIso B S hS X hX).apply_symm_apply ⟨Set.range φ, hCopen⟩)
  have heOpen : IsOpenEmbedding e := isOpenEmbedding_pointsMap_ι B S hS hX hA (hrangeA ▸ hCopen)
  have hemb : Topology.IsEmbedding e := heOpen.toIsEmbedding
  have : SpectralSpace (points B S hS A.toFunctor) :=
    spectralSpace_points_of_isQuasiCompactSpace_isAbsolutelyQuasiSeparated B S hS A.toFunctor
      hA.1 (isQuasiCompactSpace_of_isCompact_range B S hS hX hA (hrangeA ▸ hCcompact))
      (isAbsolutelyQuasiSeparated_toFunctor_of_isOpenSubspace B S hS hXqs hA)
  -- `φ` factors through the open subspace, and the factoring map is spectral.
  have hφrange (x : points B S hS (yoneda.obj U)) : φ x ∈ Set.range e := hrangeA ▸ ⟨x, rfl⟩
  set ψ : points B S hS (yoneda.obj U) → points B S hS A.toFunctor :=
    fun x ↦ hemb.toHomeomorph.symm ⟨φ x, hφrange x⟩ with hψ
  have hcomm (x : points B S hS (yoneda.obj U)) : e (ψ x) = φ x := by
    rw [hψ]
    exact congrArg Subtype.val (hemb.toHomeomorph.apply_symm_apply ⟨φ x, hφrange x⟩)
  have hψcont : Continuous ψ :=
    hemb.toHomeomorph.symm.continuous.comp (Continuous.subtype_mk hφcont hφrange)
  have hψspec : IsSpectralMap ψ := by
    refine ⟨hψcont, fun {K} hKopen hKcompact ↦ ?_⟩
    have hpre : ψ ⁻¹' K = φ ⁻¹' (e '' K) := by
      refine Set.Subset.antisymm (fun x hx ↦ ⟨ψ x, hx, hcomm x⟩) ?_
      rintro x ⟨y, hy, hxy⟩
      have hyx : ψ x = y := hemb.injective ((hcomm x).trans hxy.symm)
      rw [Set.mem_preimage, hyx]
      exact hy
    rw [hpre]
    exact hφqc (heOpen.isOpenMap _ hKopen) (hKcompact.image heOpen.continuous)
  have hψE := isConstructible_preimage_of_isSpectralMap hψspec
    (hE.preimage_of_isOpenEmbedding heOpen).isConstructible
  have hset : ψ ⁻¹' (e ⁻¹' E) = φ ⁻¹' E := by
    ext x
    rw [Set.mem_preimage, Set.mem_preimage, Set.mem_preimage, hcomm]
  rw [← hset]
  exact hψE

/-- **Stacks 0ECZ.** A subset of the point space of a quasi-separated algebraic space over `S`
is étale locally constructible exactly when it is locally constructible. -/
@[stacks 0ECZ]
theorem isEtaleLocallyConstructible_iff_isLocallyConstructible
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (E : Set (points B S hS X)) :
    IsEtaleLocallyConstructible B S hS X E ↔ IsLocallyConstructible E := by
  classical
  refine ⟨fun hE ↦ ?_, fun hE ↦
    (forall_etale_iff_forall_affine_etale B S hS X E).2 fun V hVaff g hg ↦
      isConstructible_preimage_of_isLocallyConstructible B S hS hX hXqs hE V hVaff g hg⟩
  -- A Zariski cover of `X` by open subspaces with affine surjective étale charts.
  obtain ⟨I, A, hcover, hcharts⟩ := exists_zariski_cover_affine_etale_atlas B S hS X hX
  have hAopen : ∀ i, IsOpenSubspace B S hS (A i) := hcover.1
  have hpointsCover :
      (⋃ i, Set.range (pointsMap B S hS (A i).toFunctor (A i).ι)) = Set.univ :=
    (isZariskiCover_iff_iUnion_points B S hS X hX I A hAopen).mp hcover
  have hRangeOpen (i : I) :
      IsOpen (Set.range (pointsMap B S hS (A i).toFunctor (A i).ι)) := by
    rw [← openSubspacesOrderIso_apply B S hS X hX ⟨A i, hAopen i⟩]
    exact (openSubspacesOrderIso B S hS X hX ⟨A i, hAopen i⟩).2
  have hWcover : IsOpenCover
      (fun i : I ↦ (⟨Set.range (pointsMap B S hS (A i).toFunctor (A i).ι),
        hRangeOpen i⟩ : Opens (points B S hS X))) :=
    IsOpenCover.of_sets hRangeOpen hpointsCover
  refine IsLocallyConstructible.of_isOpenCover' hWcover fun i ↦ ?_
  obtain ⟨U, f, -, hUaff, hfsurj, hfetale, -, -⟩ := hcharts i
  have hφsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) f) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS (A i).toFunctor (hAopen i).1 U f).mp
      hfsurj
  have hEmb := isOpenEmbedding_pointsMap_ι B S hS hX (hAopen i) (hRangeOpen i)
  -- The inclusion of the open subspace is quasi-compact, so its range is retrocompact.
  have hRangeRetro : IsRetrocompact (Set.range (pointsMap B S hS (A i).toFunctor (A i).ι)) :=
    IsSpectralMap.isRetrocompact_range
      (isSpectralMap_pointsMap_of_isQuasiCompactSpace B S hS (hAopen i).1 hX hXqs
        (isQuasiCompactSpace_of_affine_chart B S hS hX (hAopen i) U hUaff hφsurj) (A i).ι)
  have himage := (isConstructible_preimage_ι_of_isEtaleLocallyConstructible B S hS hX hXqs
    (hAopen i) U f hUaff hfsurj hfetale hE).image_of_isOpenEmbedding hEmb hRangeRetro
  rw [Set.image_preimage_eq_inter_range] at himage
  exact himage.isLocallyConstructible

end AlgebraicGeometry.Space

end
