module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.SmoothNormalizationPurelyInseparable
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.SmoothProperConnectedComponent

/-!
# The normalization of a proper curve, after a purely inseparable extension

Let `k` be a field and let `X` be a scheme proper over `k` with `dim(X) ≤ 1`. There is a finite
purely inseparable extension `k'/k` such that the normalization `Y` of `X_{k'}` is a finite
disjoint union of schemes `Yᵢ`, each of which is smooth, H-projective and geometrically
irreducible of dimension at most one over a finite separable extension `k'ᵢ/k'`.

This is the whole of [Stacks, Tag 0GK5] for a *proper* `X`: there the open immersion `j` of
clause (3) is an isomorphism, because a dense open immersion into a scheme whose source is proper
is one, so the compactifications `Ȳᵢ` of the source are the `Yᵢ` themselves.

## Main results

* `AlgebraicGeometry.exists_isPurelyInseparable_normalization_coproduct_smooth_projective`:
  the extension `k'`, the decomposition of the normalization, the fields `k'ᵢ` and the four
  properties of each piece.

## Implementation notes

Clauses (1) and (2) are
`AlgebraicGeometry.exists_isPurelyInseparable_smooth_normalization`, which also gives smoothness
of the normalization `Y` over `k'`. A smooth scheme is normal, and a Noetherian normal scheme is
a finite coproduct of normal integral schemes ([Stacks, Tag 033M]); `Y` is Noetherian because it
is proper over `k'`, the normalization of a proper scheme being proper
([Stacks, Tag 0GK4], `AlgebraicGeometry.isProper_normalizationOverField_comp`). Each summand is
connected, smooth and proper over `k'` of dimension at most one -- the coproduct inclusion is
both an open and a closed immersion -- so
`AlgebraicGeometry.exists_isSeparable_smooth_isProjectiveMorphism_geometricallyIrreducible`
applies to it and supplies `k'ᵢ` together with clauses (4) and (5).

The general case of the tag, where `X` is only separated, needs in addition the compactification
of [Stacks, Tag 0BXW] applied to `X` *before* the extension `k'` is chosen, and the identification
of the normalization of `X_{k'}` with the open part of the normalization of the compactification;
that is not done here.

## References

* [Stacks Project, Tag 0GK5](https://stacks.math.columbia.edu/tag/0GK5)
* [Stacks Project, Tag 033M](https://stacks.math.columbia.edu/tag/033M)
* [Stacks Project, Tag 0GK4](https://stacks.math.columbia.edu/tag/0GK4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A coproduct inclusion of schemes is a closed immersion: its image is the image of the closed
set `Set.range (Sigma.mk i)` under the homeomorphism from the disjoint union. -/
private theorem isClosedImmersion_sigmaι_of_scheme {ι : Type u} (Z : ι → Scheme.{u}) (i : ι) :
    IsClosedImmersion (Sigma.ι Z i) := by
  apply IsClosedImmersion.of_isPreimmersion
  have hr : Set.range (Sigma.ι Z i) = (sigmaMk Z) '' Set.range (Sigma.mk i) := by
    ext z
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨i, x⟩, ⟨x, rfl⟩, sigmaMk_mk Z i x⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, (sigmaMk_mk Z i x).symm⟩
  rw [hr]
  exact (sigmaMk Z).isClosedMap _ (isClosed_range_sigmaMk (i := i))

/-- **[Stacks, Tag 0GK5] for a proper `X`.** Let `k` be a field and let `X` be proper over `k`
with `dim(X) ≤ 1`. There is a finite purely inseparable extension `k'/k` such that the
normalization of `X_{k'}` is a finite coproduct of schemes `Yᵢ`, each smooth, H-projective and
geometrically irreducible of dimension at most one over a finite separable extension `k'ᵢ/k'`,
compatibly with the structure morphisms. -/
@[stacks 0GK5 "clauses (3), (4) and (5) for a PROPER X, where the open immersion j of clause (3) \
is an isomorphism and the compactifications Ybar_i are the components Y_i of the normalization \
themselves. Clauses (1) and (2) -- the finite purely inseparable k'/k and the normalization of \
X_{k'} -- are reproved here as part of the diagram. What the general separated case still needs \
is the compactification of Stacks 0BXW applied to X before k' is chosen, together with the \
identification of the normalization of X_{k'} with the open part of the normalization of that \
compactification.", ega "IV 17.15.14" "Proper case of 17.15.14", sga "4 XIV 1.11" "special case"]
public theorem exists_isPurelyInseparable_normalization_coproduct_smooth_projective
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Module.Finite k k')
      (_ : IsPurelyInseparable k k') (ι : Type u) (_ : Finite ι) (Y : ι → Scheme.{u})
      (e : normalizationSchemeOverField k' (pullback.fst (spectrumMap k k') p) ≅ ∐ Y)
      (K : ι → Type u) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra k' (K i))
      (_ : ∀ i, Module.Finite k' (K i)) (_ : ∀ i, Algebra.IsSeparable k' (K i))
      (r : ∀ i, Y i ⟶ Spec (.of (K i))),
      (∀ i, r i ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (K i))) =
          Sigma.ι Y i ≫ e.inv ≫
            normalizationOverField k' (pullback.fst (spectrumMap k k') p) ≫
              pullback.fst (spectrumMap k k') p) ∧
        ∀ i, Smooth (r i) ∧ IsProjectiveMorphism (r i) ∧ GeometricallyIrreducible (r i) ∧
          topologicalKrullDim (Y i : Type u) ≤ 1 := by
  obtain ⟨k', hfield, halg, hfink, hpi, hsmooth⟩ :=
    exists_isPurelyInseparable_smooth_normalization k p hdim
  set q : pullback (spectrumMap k k') p ⟶ Spec (.of k') := pullback.fst (spectrumMap k k') p
    with hq
  -- `X_{k'}` is proper over `k'`, hence so is its normalization.
  have hqproper : IsProper q := by
    rw [hq]
    infer_instance
  have hnproper : IsProper (normalizationOverField k' q ≫ q) :=
    isProper_normalizationOverField_comp k' q
  -- The normalization has dimension at most one.
  have hdimXk : topologicalKrullDim ((pullback (spectrumMap k k') p : Scheme.{u}) : Type u) ≤ 1 :=
    ((IsHomeomorph.topologicalKrullDim_eq _
      (pullbackSymmetry (spectrumMap k k') p).hom.homeomorph.isHomeomorph).trans
      (IsHomeomorph.topologicalKrullDim_eq _
        (isHomeomorph_pullbackFst_specMap_algebraMap k k' p))).le.trans hdim
  have _ : IsFinite (normalizationOverField k' q) := isFinite_normalizationOverField k' q
  have hdimY : topologicalKrullDim (normalizationSchemeOverField k' q) ≤ 1 :=
    (topologicalKrullDim_le_of_isIntegralHom (normalizationOverField k' q)).trans hdimXk
  -- The normalization is Noetherian and normal, hence a finite coproduct of normal integrals.
  have _ : IsLocallyNoetherian (normalizationSchemeOverField k' q) :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizationOverField k' q ≫ q)
  have _ : CompactSpace (normalizationSchemeOverField k' q) :=
    (quasiCompact_iff_compactSpace (normalizationOverField k' q ≫ q)).mp inferInstance
  have _ : AlgebraicGeometry.IsNoetherian (normalizationSchemeOverField k' q) :=
    AlgebraicGeometry.IsNoetherian.mk
  obtain ⟨ι, hfinι, Y, hYnormal, hYintegral, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_finite_coproduct_integral_normal
      (normalizationSchemeOverField k' q)).mp
      (Scheme.isNormal_normalizationScheme _
        (finite_irreducibleComponents_of_locallyOfFiniteType k' q))
  have hdata : ∀ i : ι, ∃ (K : Type u) (_ : Field K) (_ : Algebra k' K) (_ : Module.Finite k' K)
      (_ : Algebra.IsSeparable k' K) (r : Y i ⟶ Spec (.of K)),
      r ≫ Spec.map (CommRingCat.ofHom (algebraMap k' K)) =
          Sigma.ι Y i ≫ e.inv ≫ normalizationOverField k' q ≫ q ∧
        Smooth r ∧ IsProjectiveMorphism r ∧ GeometricallyIrreducible r ∧
          topologicalKrullDim (Y i : Type u) ≤ 1 := by
    intro i
    -- Each summand is connected, smooth and proper over `k'`, of dimension at most one.
    have _ : IsClosedImmersion (Sigma.ι Y i) := isClosedImmersion_sigmaι_of_scheme Y i
    have _ : IsIntegral (Y i) := hYintegral i
    exact exists_isSeparable_smooth_isProjectiveMorphism_geometricallyIrreducible k'
      (Sigma.ι Y i ≫ e.inv ≫ normalizationOverField k' q ≫ q)
      ((topologicalKrullDim_le_of_isIntegralHom (Sigma.ι Y i ≫ e.inv)).trans hdimY)
  choose K fieldK algK finK sepK r hr hprops using hdata
  exact ⟨k', hfield, halg, hfink, hpi, ι, hfinι, Y, e, K, fieldK, algK, finK, sepK, r,
    hr, hprops⟩

end AlgebraicGeometry

end
