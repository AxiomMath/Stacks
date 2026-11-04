module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromFiniteSurjective
public import StacksFrontier.AlgebraicGeometry.Limits.FibreDimensionEnlargement
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.ExtendImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.LevelSetConstructible
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic
public import StacksFrontier.Topology.Spectral.LimitGeneralizations

/-!
# A finitely presented model of an affine quasi-finite morphism

A quasi-finite morphism of affine schemes need not be of finite presentation, which is what
Tag 0F3R asks for. This file manufactures a finitely presented replacement with the same
weighted fibre sums.

First, `f : X ⟶ Y` with `X`, `Y` affine factors as a closed immersion `X ⟶ Z` followed by a
morphism `Z ⟶ Y` which is affine, of finite presentation and still locally quasi-finite: write
`X` as a closed subscheme of an affine space over `Y` and shrink that affine space to a closed
subscheme of finite presentation over `Y` using Tag 05M6, whose fibre-dimension bound is
preserved.

Second, if `w` is an everywhere positive weighting of `f` then `X` is not merely closed in `Z`
but is cut out there by an ideal whose complement is quasi-compact: the complement of the image
of `X` is the zero level set of the extension of `w` by zero, which is constructible by Tag
0F3G. A quasi-compact complement means the ideal can be replaced by a finitely generated
subideal with the same zero locus, so after one further shrinking the closed immersion
`X ⟶ T` is *surjective* and `T ⟶ Y` is of finite presentation.

## Main results

All in the namespace `AlgebraicGeometry`:

* `exists_isClosedImmersion_locallyQuasiFinite_finitePresentation_factorization`
* `exists_surjective_isClosedImmersion_finitePresentation_of_range_compl_isCompact`
* `isCompact_compl_range_of_isWeighting`

## References

* [Stacks Project, Tag 05M6](https://stacks.math.columbia.edu/tag/05M6)
* [Stacks Project, Tag 0F3G](https://stacks.math.columbia.edu/tag/0F3G)
* [Stacks Project, Tag 0F3R](https://stacks.math.columbia.edu/tag/0F3R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- `Spec` of the structure map of a finitely presented algebra is locally of finite
presentation. -/
private lemma locallyOfFinitePresentation_spec_map_algebraMap (A B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- **A quasi-finite morphism of affine schemes is a closed subscheme of a finitely presented
quasi-finite one.** -/
theorem exists_isClosedImmersion_locallyQuasiFinite_finitePresentation_factorization
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] :
    ∃ (Z : Scheme.{u}) (j : X ⟶ Z) (p : Z ⟶ Y),
      IsAffine Z ∧ IsClosedImmersion j ∧ LocallyOfFinitePresentation p ∧
        LocallyQuasiFinite p ∧ j ≫ p = f := by
  let A := Γ(Y, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra A B := f.appTop.hom.toAlgebra
  have hft : Algebra.FiniteType A B :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let R := MvPolynomial (Fin n) A
  let i : X ⟶ Spec (.of R) := X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom q.toRingHom)
  let p : Spec (.of R) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap A R)) ≫ Y.isoSpec.inv
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom q.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hq
  have : IsClosedImmersion i := inferInstance
  have hp := locallyOfFinitePresentation_spec_map_algebraMap A R
  have : LocallyOfFinitePresentation p := inferInstance
  have hip : i ≫ p = f := by
    have hqC : CommRingCat.ofHom (algebraMap A R) ≫ CommRingCat.ofHom q.toRingHom =
        f.appTop := by
      ext a
      exact q.commutes a
    dsimp only [i, p]
    rw [Category.assoc, ← Spec.map_comp_assoc, hqC, Scheme.isoSpec_hom,
      ← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  obtain ⟨Z, k, j, hk, hj, hij, hkp, hd⟩ :=
    exists_finitePresentation_closedImmersion_of_forall_topologicalKrullDim_fiber_le
      p ⟨inferInstance, inferInstance, inferInstance⟩ i 0 (by
        intro y
        rw [hip]
        exact topologicalKrullDim_zero_of_discreteTopology (f.fiber y))
  have := hk
  have : IsAffine Z := isAffine_of_isAffineHom k
  have : LocallyOfFinitePresentation k := hkp.1
  have : LocallyQuasiFinite (k ≫ p) :=
    locallyQuasiFinite_of_forall_topologicalKrullDim_fiber_le_zero _ hd
  exact ⟨Z, j, k ≫ p, inferInstance, hj, inferInstance, inferInstance,
    by rw [← Category.assoc, ← hij, hip]⟩

/-- An ideal whose zero locus has quasi-compact complement has a finitely generated subideal
with the same zero locus: the complement is covered by finitely many of the basic opens of the
ideal's elements. -/
private lemma exists_fg_le_zeroLocus_eq {R : Type u} [CommRing R] (I : Ideal R)
    (hI : IsCompact (PrimeSpectrum.zeroLocus (I : Set R))ᶜ) :
    ∃ J : Ideal R, J.FG ∧ J ≤ I ∧
      PrimeSpectrum.zeroLocus (J : Set R) = PrimeSpectrum.zeroLocus (I : Set R) := by
  classical
  obtain ⟨s, hs⟩ := hI.elim_finite_subcover
    (fun a : I ↦ (PrimeSpectrum.basicOpen a.1 : Set (PrimeSpectrum R)))
    (fun a ↦ (PrimeSpectrum.basicOpen a.1).isOpen) (by
      intro p hp
      simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
        SetLike.coe_subset_coe] at hp
      obtain ⟨a, haI, hap⟩ := Set.not_subset.mp hp
      exact Set.mem_iUnion.mpr ⟨⟨a, haI⟩, hap⟩)
  let t : Finset R := s.image Subtype.val
  have htI : Ideal.span (t : Set R) ≤ I := Ideal.span_le.mpr fun a ha ↦ by
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact b.property
  refine ⟨Ideal.span (t : Set R), ⟨t, rfl⟩, htI,
    Set.Subset.antisymm ?_ (PrimeSpectrum.zeroLocus_anti_mono htI)⟩
  intro p hp
  by_contra hpI
  obtain ⟨a, ha, hap⟩ := Set.mem_iUnion₂.mp (hs hpI)
  exact hap (hp (Ideal.subset_span (Finset.mem_image.mpr ⟨a, ha, rfl⟩)))

/-- The range of `Spec` of the global sections map of a morphism of affine schemes is the
preimage of the range of the morphism. -/
private lemma range_specMap_appTop {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z] (j : X ⟶ Z) :
    Set.range (Spec.map j.appTop) = Z.isoSpec.inv ⁻¹' Set.range j := by
  have hr : Z.isoSpec.inv '' Set.range (Spec.map j.appTop) = Set.range j := by
    rw [← Set.range_comp]
    show Set.range (Spec.map j.appTop ≫ Z.isoSpec.inv) = Set.range j
    rw [Scheme.isoSpec_inv_naturality]
    show Set.range (j ∘ X.isoSpec.inv) = Set.range j
    rw [Set.range_comp, Set.range_eq_univ.mpr X.isoSpec.inv.surjective, Set.image_univ]
  rw [← hr, Set.preimage_image_eq _ Z.isoSpec.inv.isEmbedding.injective]

/-- The range of `Spec` of a quotient map is the zero locus of the ideal. -/
private lemma range_specMap_quotient_mk {R : Type u} [CommRing R] (J : Ideal R) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
      PrimeSpectrum.zeroLocus (J : Set R) := by
  show Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

/-- **A closed immersion of affine schemes with quasi-compact complement is a surjective closed
immersion into a finitely presented closed subscheme.** -/
theorem exists_surjective_isClosedImmersion_finitePresentation_of_range_compl_isCompact
    {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z] (j : X ⟶ Z) [IsClosedImmersion j]
    (hc : IsCompact (Set.range j)ᶜ) :
    ∃ (T : Scheme.{u}) (i : X ⟶ T) (k : T ⟶ Z),
      IsAffine T ∧ IsClosedImmersion i ∧ Surjective i ∧
        IsClosedImmersion k ∧ LocallyOfFinitePresentation k ∧ i ≫ k = j := by
  classical
  let A := Γ(Z, ⊤)
  let I := RingHom.ker j.appTop.hom
  have hq : Function.Surjective j.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine j).2
  have hzero : Set.range (Spec.map j.appTop) = PrimeSpectrum.zeroLocus (I : Set A) :=
    range_comap_of_surjective _ j.appTop.hom hq
  have hIc : IsCompact (PrimeSpectrum.zeroLocus (I : Set A))ᶜ := by
    have h2 : IsCompact (Z.isoSpec.inv ⁻¹' (Set.range j)ᶜ) :=
      Z.isoSpec.inv.homeomorph.isCompact_preimage.mpr hc
    rwa [Set.preimage_compl, ← range_specMap_appTop, hzero] at h2
  obtain ⟨J, hJ, hJI, hJzero⟩ := exists_fg_le_zeroLocus_eq I hIc
  let T := Spec (.of (A ⧸ J))
  let k : T ⟶ Z := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Z.isoSpec.inv
  let i : X ⟶ T := X.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J j.appTop.hom hJI))
  have hk : IsClosedImmersion k := inferInstance
  have hcomp : i ≫ k = j := by
    have he : CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        CommRingCat.ofHom (Ideal.Quotient.lift J j.appTop.hom hJI) = j.appTop := by
      ext a
      rfl
    dsimp only [i, k]
    rw [Category.assoc, ← Spec.map_comp_assoc, he, Scheme.isoSpec_inv_naturality,
      Iso.hom_inv_id_assoc]
  have hi : IsClosedImmersion i := by
    have : IsClosedImmersion (i ≫ k) := hcomp ▸ inferInstance
    exact IsClosedImmersion.of_comp_isClosedImmersion i k
  have hkRange : Set.range k = Set.range j := by
    show Set.range (Z.isoSpec.inv ∘ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) = _
    rw [Set.range_comp, range_specMap_quotient_mk, hJzero, ← hzero, range_specMap_appTop,
      Set.image_preimage_eq_inter_range, Set.range_eq_univ.mpr Z.isoSpec.inv.surjective,
      Set.inter_univ]
  have his : Surjective i := ⟨fun t ↦ by
    obtain ⟨x, hx⟩ := hkRange.subset ⟨t, rfl⟩
    refine ⟨x, k.isEmbedding.injective ?_⟩
    show (i ≫ k) x = k t
    rw [hcomp]
    exact hx⟩
  have : Algebra.FinitePresentation A (A ⧸ J) := Algebra.FinitePresentation.quotient hJ
  have hmkfp := locallyOfFinitePresentation_spec_map_algebraMap A (A ⧸ J)
  exact ⟨T, i, k, inferInstance, hi, his, hk, inferInstance, hcomp⟩

/-- **The complement of the image of a positively weighted closed subscheme is quasi-compact.**
It is the zero level set of the extension of the weight by zero, which is a weighting of the
ambient morphism, hence constructible by Tag 0F3G; a constructible subset of a spectral space
is quasi-compact. -/
theorem isCompact_compl_range_of_isWeighting
    {X Z Y : Scheme.{u}} [IsAffine X] [IsAffine Z] (j : X ⟶ Z) [IsClosedImmersion j]
    (p : Z ⟶ Y) [LocallyOfFiniteType p] [LocallyQuasiFinite p]
    {w : X → ℤ} (hw : IsWeighting (j ≫ p) w) (hpos : ∀ x, 0 < w x) :
    IsCompact (Set.range j)ᶜ := by
  have hw' : IsWeighting p (Function.extend j w (0 : Z → ℤ)) :=
    IsWeighting.extend_of_isClosedImmersion j hw
  have heq : {z : Z | Function.extend j w (0 : Z → ℤ) z = 0} = (Set.range j)ᶜ := by
    ext z
    by_cases hz : z ∈ Set.range j
    · obtain ⟨x, rfl⟩ := hz
      simp only [Set.mem_setOf_eq, j.isEmbedding.injective.extend_apply,
        Set.mem_compl_iff, Set.mem_range_self, not_true_eq_false, iff_false]
      exact ne_of_gt (hpos x)
    · simp [Function.extend_apply' w (0 : Z → ℤ) z hz, hz]
  have : SpectralSpace Z := Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace Z
  have hz : Topology.IsConstructible ((Set.range j)ᶜ) := by
    rw [← heq]
    exact (isLocallyConstructible_weighting_levelSet hw' 0).isConstructible
  exact hz.isClosed_constructibleTopology.isCompact_of_constructibleTopology

end AlgebraicGeometry

end
