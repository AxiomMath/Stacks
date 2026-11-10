module

public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.SmoothProjectiveCompactificationCurve
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperCoproduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.SigmaMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaDescent
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaFiniteHom
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyConnectedFibres
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.ConnectedComponents

/-!
# The curve diagram over a field

Let `X` be a separated scheme of finite type and of dimension at most one over a field `k`.
[Stacks, Tag 0GK5] provides a finite purely inseparable extension `k'/k` and a dense open
immersion of the normalization `Y` of `X_{k'}` into a finite disjoint union `Ȳ` of smooth
projective geometrically irreducible curves over finite separable extensions `k'ᵢ` of `k'`. This
file repackages that diagram as the input of the descent step of [Stacks, Tag 0GK7]: the finite
étale `k'`-scheme `T = ∐ Spec k'ᵢ`, the smooth proper morphism `Ȳ ⟶ T` with geometrically
connected fibres of dimension at most one, the open immersion `Y ⟶ Ȳ`, the finite surjective
normalization morphism `ν : Y ⟶ X_{k'}`, and a dense open `W ⊆ X_{k'}` over which `ν` is a closed
immersion and whose preimage meets every fibre of `Y ⟶ T`.

## Main results

* `AlgebraicGeometry.exists_dense_isClosedImmersion_normalizationOverField`: the normalization of
  a scheme of finite type over a field is a closed immersion over a dense open.
* `AlgebraicGeometry.exists_curveDiagram_over_field`: the diagram.

## Implementation notes

The open over which the normalization is a closed immersion is found through the reduction: the
normalization factors through the normalization of the reduction ([Stacks, Tag 035O]), which is
birational ([Stacks, Tag 0BXC]) and hence an isomorphism over a dense open
([Stacks, Tag 0BAJ]); this is [Stacks, Tag 0BXR] in the form the source uses it.

## References

* [Stacks Project, Tag 0GK5](https://stacks.math.columbia.edu/tag/0GK5)
* [Stacks Project, Tag 0GK7](https://stacks.math.columbia.edu/tag/0GK7)
* [Stacks Project, Tag 0BXR](https://stacks.math.columbia.edu/tag/0BXR)
* [Stacks Project, Tag 0BAJ](https://stacks.math.columbia.edu/tag/0BAJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A quasi-compact scheme locally of finite type over a field is Noetherian. -/
theorem isNoetherian_of_locallyOfFiniteType_of_quasiCompact (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] :
    IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact ⟨⟩

/-- **[Stacks, Tag 0BXR], as used in [Stacks, Tag 0GK7].** The normalization of a quasi-compact
scheme locally of finite type over a field is a closed immersion over a dense open. -/
theorem exists_dense_isClosedImmersion_normalizationOverField (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] :
    ∃ W : X.Opens, Dense (W : Set X) ∧ IsClosedImmersion (normalizationOverField k p ∣_ W) := by
  classical
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hX
  let ι := X.nilradical.subschemeι
  have : IsReduced X.nilradical.subscheme := isReduced_nilradical_subscheme X
  let hXr := X.finite_irreducibleComponents_reduction hX
  let f := X.nilradical.subscheme.normalization hXr
  have hbir : IsBirational f := Scheme.isBirational_normalization _ hXr
  have : IsFinite f := isFinite_normalizationOverField k (ι ≫ p)
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType_of_quasiCompact k p
  have : IsNoetherian X.nilradical.subscheme :=
    isNoetherian_of_locallyOfFiniteType_of_quasiCompact k (ι ≫ p)
  have : IsNoetherian (X.nilradical.subscheme.normalizationScheme hXr) :=
    isNoetherian_of_locallyOfFiniteType_of_quasiCompact k (f ≫ ι ≫ p)
  have : Finite (irreducibleComponents X.nilradical.subscheme) :=
    Set.finite_coe_iff.mpr finite_irreducibleComponents_of_isNoetherian
  have : Finite (irreducibleComponents (X.nilradical.subscheme.normalizationScheme hXr)) :=
    Set.finite_coe_iff.mpr finite_irreducibleComponents_of_isNoetherian
  obtain ⟨V, hVd, hViso⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational f hbir
    (Or.inl inferInstance) (Or.inl ⟨inferInstance, inferInstance⟩)
  have hsurj : Function.Surjective ι := fun x =>
    Set.mem_range.mp (by rw [X.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)
  let h := ι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective hsurj
  let W : X.Opens := ⟨ι '' V, h.isOpenMap _ V.isOpen⟩
  have hWV : ι ⁻¹ᵁ W = V := by
    ext x
    change ι x ∈ ι '' (V : Set X.nilradical.subscheme) ↔ x ∈ V
    exact ι.isClosedEmbedding.injective.mem_set_image
  refine ⟨W, h.surjective.denseRange.dense_image h.continuous hVd, ?_⟩
  · have hν : normalizationOverField k p = e.hom ≫ (f ≫ ι) := he.symm
    have h₁ : IsClosedImmersion (f ∣_ ι ⁻¹ᵁ W) := by rw [hWV]; infer_instance
    have h₀ : IsClosedImmersion (ι ∣_ W) :=
      IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance W
    have h₃ : IsClosedImmersion (e.hom ∣_ (f ≫ ι) ⁻¹ᵁ W) :=
      have : IsIso (e.hom ∣_ (f ≫ ι) ⁻¹ᵁ W) :=
        IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms _)
          (inferInstanceAs (IsIso e.hom)) _
      inferInstance
    rw [hν, morphismRestrict_comp, morphismRestrict_comp]
    exact @IsClosedImmersion.comp _ _ _ _ _ h₃ (@IsClosedImmersion.comp _ _ _ _ _ h₁ h₀)

/-- Every point of a coproduct of schemes lies in one of the summands. -/
theorem exists_sigmaι_apply_eq {ι : Type u} [Small.{u} ι] (Z : ι → Scheme.{u})
    (s : (∐ Z : Scheme.{u})) :
    ∃ (i : ι) (x : Z i), Sigma.ι Z i x = s := by
  obtain ⟨⟨i, x⟩, hx⟩ := (sigmaMk Z).surjective s
  exact ⟨i, x, by rw [← hx, sigmaMk_mk]⟩

/-- **The curve diagram over a field.** Let `X` be separated, quasi-compact and locally of finite
type of dimension at most one over a field `k`. After a finite purely inseparable extension
`k'/k` there are a finite étale `T ⟶ Spec k'`, a smooth proper `q̄ : Ȳ ⟶ T` with geometrically
connected fibres of dimension at most one, an open immersion `j : Y ⟶ Ȳ` and a finite surjective
`ν : Y ⟶ X_{k'}` over `Spec k'`, together with an open `W ⊆ X_{k'}` over which `ν` is a closed
immersion and whose preimage meets every fibre of `j ≫ q̄`. -/
theorem exists_curveDiagram_over_field (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Module.Finite k k')
      (_ : IsPurelyInseparable k k') (T Ybar Y : Scheme.{u}) (t : T ⟶ Spec (.of k'))
      (qbar : Ybar ⟶ T) (jY : Y ⟶ Ybar) (ν : Y ⟶ pullback (spectrumMap k k') p)
      (W : (pullback (spectrumMap k k') p).Opens),
      ν ≫ pullback.fst (spectrumMap k k') p = jY ≫ qbar ≫ t ∧
      IsFinite t ∧ Etale t ∧ Smooth qbar ∧ IsProper qbar ∧ GeometricallyConnected qbar ∧
      (∀ s, topologicalKrullDim (qbar.fiber s) ≤ 1) ∧ IsOpenImmersion jY ∧ IsFinite ν ∧
      Surjective ν ∧ IsClosedImmersion (ν ∣_ W) ∧
      ∀ s : T, ∃ y : Y, ν y ∈ W ∧ qbar (jY y) = s := by
  classical
  obtain ⟨k', hfield, halg, hfin, hpi, ι, hι, Ybar, sbar, K, fK, aK, finK, sepK, rbar, j, hj,
    hdense, hjfac, hrbar, hprops⟩ :=
    exists_isPurelyInseparable_dense_openImmersion_smooth_projective k p hdim
  let := hfield
  let := halg
  let := hι
  let := fK
  let := aK
  let pk := pullback.fst (spectrumMap k k') p
  have hlftpk : LocallyOfFiniteType pk := inferInstance
  have hqcpk : QuasiCompact pk := inferInstance
  let T := ∐ fun i => Spec (.of (K i))
  let t : T ⟶ Spec (.of k') :=
    Sigma.desc fun i => Spec.map (CommRingCat.ofHom (algebraMap k' (K i)))
  let qbar : (∐ Ybar) ⟶ T := Limits.Sigma.map rbar
  have hsbar : sbar = qbar ≫ t := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_comp_desc]
    exact (hrbar i).symm
  have hιq : ∀ i, Sigma.ι Ybar i ≫ qbar = rbar i ≫ Sigma.ι (fun i => Spec (.of (K i))) i :=
    fun i => Sigma.ι_map _ _
  have hproper : ∀ i, IsProper (rbar i) := fun i =>
    isProper_of_isProjectiveMorphism _ (hprops i).2.1
  have hsmooth : ∀ i, Smooth (rbar i) := fun i => (hprops i).1
  have hgc : ∀ i, GeometricallyConnected (rbar i) := fun i =>
    @geometricallyConnected_of_geometricallyIrreducible _ _ _ (hprops i).2.2.1
  have hqbarsm : Smooth qbar := by
    have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (𝒰 := sigmaOpenCover Ybar)
      fun i ↦ ?_
    rw [show (sigmaOpenCover Ybar).f i ≫ qbar = _ from hιq i]
    exact MorphismProperty.comp_mem _ _ _ (hsmooth i) inferInstance
  have : LocallyOfFiniteType qbar := inferInstance
  have : NoetherianSpace (pullback (spectrumMap k k') p : Scheme.{u}) :=
    have := isNoetherian_of_locallyOfFiniteType_of_quasiCompact k' pk
    inferInstance
  obtain ⟨W, hWd, hWc⟩ := exists_dense_isClosedImmersion_normalizationOverField k' pk
  refine ⟨k', hfield, halg, hfin, hpi, T, ∐ Ybar, _, t, qbar, j, normalizationOverField k' pk, W,
    ?_, ?_, ?_, hqbarsm,
    isProper_sigmaMap rbar, ?_, ?_, hj, isFinite_normalizationOverField k' pk, ?_, hWc, ?_⟩
  · rw [← hjfac, hsbar]
  · have : ∀ i, IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k' (K i)))) := fun i => by
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr (finK i)
    exact isFinite_sigmaDesc_of_locallyFinite _ (locallyFinite_of_finite _)
  · exact etale_sigmaDesc _ fun i => by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      change (algebraMap k' (K i)).Etale
      rw [RingHom.etale_algebraMap]
      exact ⟨Algebra.FormallyEtale.of_isSeparable k' (K i),
        Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  · refine (GeometricallyConnected.iff_geometricallyConnected_fiber _).mpr fun s => ?_
    obtain ⟨i, x, rfl⟩ := exists_sigmaι_apply_eq _ s
    rw [geometricallyConnected_iff_numGeometricConnectedComponents_eq_one]
    have h := congrFun (numGeometricConnectedComponents_eq_of_isPullback (Limits.Sigma.map rbar)
      (rbar i) (Sigma.ι Ybar i) (Sigma.ι (fun i => Spec (.of (K i))) i)
      (isPullback_sigmaMap rbar i)) x
    rw [Function.comp_apply] at h
    rw [← h, ← geometricallyConnected_iff_numGeometricConnectedComponents_eq_one]
    exact (GeometricallyConnected.iff_geometricallyConnected_fiber _).mp (hgc i) x
  · intro s
    obtain ⟨i, x, rfl⟩ := exists_sigmaι_apply_eq _ s
    have h := congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback (isPullback_sigmaMap rbar i)) x
    change qbar.fiberDimension _ ≤ 1
    rw [Function.comp_apply] at h
    rw [← h]
    exact ((IsHomeomorph.topologicalKrullDim_eq _ ((rbar i).fiberHomeo x).isHomeomorph).trans_le
      (topologicalKrullDim_subspace_le _ _)).trans (hprops i).2.2.2
  · refine ⟨fun x => ?_⟩
    have hd : IsDominant (normalizationOverField k' pk) := isDominant_normalizationOverField k' pk
    have hcl : IsClosed (Set.range (normalizationOverField k' pk)) :=
      (normalizationOverField k' pk).isClosedMap.isClosed_range
    have : x ∈ closure (Set.range (normalizationOverField k' pk)) := hd.denseRange x
    rwa [hcl.closure_eq] at this
  · intro s
    obtain ⟨i, x, rfl⟩ := exists_sigmaι_apply_eq _ s
    obtain ⟨y₀, -⟩ := (rbar i).surjective x
    obtain ⟨_, hξ, ⟨ξ, rfl⟩⟩ := hdense.inter_open_nonempty _
      (Sigma.ι Ybar i).isOpenEmbedding.isOpen_range ⟨_, y₀, rfl⟩
    let C : Set (normalizationSchemeOverField k' pk) := irreducibleComponent ξ
    have hC : IsIrreducible C := isIrreducible_irreducibleComponent
    have hgen := hC.isGenericPoint_genericPoint_closure
    rw [isClosed_irreducibleComponent.closure_eq] at hgen
    let η : normalizationSchemeOverField k' pk := hC.genericPoint
    have hηgen : η ∈ genericPoints (normalizationSchemeOverField k' pk) := by
      change closure {η} ∈ irreducibleComponents _
      rw [hgen.def]
      exact irreducibleComponent_mem_irreducibleComponents ξ
    have hηξ : η ⤳ ξ := hgen.specializes mem_irreducibleComponent
    have hηO : j η ∈ Set.range (Sigma.ι Ybar i) :=
      hηξ.mem_open ((Sigma.ι Ybar i).isOpenEmbedding.isOpen_range.preimage j.continuous) hξ
    obtain ⟨y, hy⟩ := hηO
    refine ⟨η, mem_of_mem_genericPoints_of_dense W hWd
      (Scheme.normalization_mem_genericPoints _ _ hηgen), ?_⟩
    rw [← hy]
    change (Sigma.ι Ybar i ≫ qbar) y = _
    rw [hιq, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _

end AlgebraicGeometry

end
