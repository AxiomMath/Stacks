module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSupportUnitLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartIdealSheafData
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPushforwardFibreLength
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints

/-!
# An open subspace whose complement is cut out by a finite type ideal is quasi-compact

Let `X` be a quasi-compact algebraic space over a scheme `S` contained in a big fppf site `B`,
and let `U ⊆ X` be an open subspace whose complement `|X| ∖ |U|` is the zero locus `|V(ℐ)|` of a
quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` of finite type.  This file proves that `U` is then
quasi-compact, which is the implication (3) ⟹ (2) of Tag 0855.

The equivalence of conditions (1) and (2) of that tag is
`AlgebraicGeometry.Space.isQuasiCompact_iff_isQuasiCompactSpace_openSubspace` in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactSupport.lean`, and the converse implication
(2) ⟹ (3) is
`AlgebraicGeometry.Space.hasFiniteTypeQuasicoherentIdealZeroLocus_of_isQuasiCompactSpace` in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeIdealOfQuasiCompactOpen.lean`, condition (3)
being asserted by `AlgebraicGeometry.Space.HasFiniteTypeQuasicoherentIdealZeroLocus`; the
equivalence of all three conditions is
`AlgebraicGeometry.Space.tfae_isQuasiCompact_openSubspace` in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactOpenTfae.lean`.  This file cannot live beside
the first of those: the argument runs through
`AlgebraicGeometry.Space.isQuasiCompactSpace_of_isCompact_range`, which is downstream of
`QuasiCompactSupport.lean` in the import graph.

## Main results

* `AlgebraicGeometry.Space.idealUnitLocus_eq_image_support_compl`: on an étale chart which is
  surjective on points, the unit locus of `ℐ` is the image of the complement of the support of
  the Zariski sheaf of ideals the chart inherits.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_hasFiniteTypeQuasicoherentIdealZeroLocus`:
  **the implication (3) ⟹ (2) of Tag 0855.**

## Implementation notes

The Stacks proof of this implication reads `|U|` on an affine étale chart `φ : W → X` and
appeals to the lemma for schemes, part (4) ⟹ (2) of [Stacks, Tag 01PH], applied to `φ⁻¹ℐ`.  That
is what happens here, with `φ⁻¹ℐ` the chartwise Zariski sheaf of ideals
`AlgebraicGeometry.Space.idealSheafDataOfChart`:

* the chart comes from
  `AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`, which is
  Tag 03H6 and is where quasi-compactness of `X` is used;
* the chartwise sheaf of ideals is of finite type by
  `AlgebraicGeometry.Space.isFiniteType_idealSheafDataOfChart`, cartesianness on affine charts
  coming from quasi-coherence by Descent, Proposition 03DX(2);
* `AlgebraicGeometry.isCompact_of_isFiniteType_of_support_eq_compl` is the scheme statement, the
  chart's scheme being affine and hence quasi-compact;
* and the two complements are identified by
  `AlgebraicGeometry.Space.support_compl_eq_chartUnitLocusPreimage`.

The passage back from the chart to `U` is **not** the surjective étale atlas of Tag 03E3 but the
point set: `|U|` is the continuous image of the quasi-compact complement of the support, so it is
a quasi-compact subset of `|X|`, and
`AlgebraicGeometry.Space.isQuasiCompactSpace_of_isCompact_range` descends that to
quasi-compactness of the open subspace `U` through Tag 03E4.  This is why
`AlgebraicGeometry.Space.continuous_chartSchemeToPoints` is needed and no chart of `U` is formed.

Quasi-separatedness of `X`, which Tag 0855 hypothesises, is not used *here*, and the statement
below is therefore left without it.  It is used by the tag's other two clauses: by the
equivalence of (1) with (2), and by the implication (2) ⟹ (3), which feeds it to Stacks 0853.

## References

* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : IsCartesianOnAffineCharts I.toSheafOfModules)

/-- **The unit locus of `ℐ` is the image of the complement of the support of the chartwise sheaf
of ideals**, for an étale chart which is surjective on points.

One inclusion is `AlgebraicGeometry.Space.support_compl_eq_chartUnitLocusPreimage`, which says
that the complement of the support is exactly the preimage of the unit locus, so its image lands
there; the other is
`AlgebraicGeometry.Space.exists_mem_support_compl_chartSchemeToPoints_eq`, which produces for
every point of the unit locus a point of the chart's scheme off the support lying over it. -/
theorem idealUnitLocus_eq_image_support_compl (A : SmallEtale B S hS X.1)
    (hA : Function.Surjective (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj A)) A.obj.hom)) :
    idealUnitLocus B S hS X I =
      chartSchemeToPoints B S hS X.1 A ''
        (((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens) :
          Set (chartScheme A)) := by
  refine Set.eq_of_subset_of_subset (fun z hz => ?_) ?_
  · obtain ⟨x, hx, hxz⟩ :=
      exists_mem_support_compl_chartSchemeToPoints_eq B S hS X I hI A hA hz
    exact ⟨x, hx, hxz⟩
  · rintro z ⟨x, hx, rfl⟩
    have hmem : x ∈ chartUnitLocusPreimage B S hS X I A := by
      rw [← support_compl_eq_chartUnitLocusPreimage B S hS X I hI A]
      exact hx
    exact (mem_chartUnitLocusPreimage_iff B S hS X I A x).1 hmem

/-- **Stacks 0855, part (3) implies part (2).** Let `X` be a quasi-compact algebraic space over
`S` and let `U ⊆ X` be an open subspace.  If there is a finite type quasi-coherent sheaf of
ideals `ℐ ⊆ 𝒪_X` with `|X| ∖ |U| = |V(ℐ)|`, then `U` is quasi-compact.

An affine étale chart of `X` surjective on points exists by Tag 03H6.  The Zariski sheaf of
ideals which `ℐ` induces on the chart's scheme is of finite type, so the complement of its
support is a quasi-compact open of that affine — and hence quasi-compact — scheme, by part
(4) ⟹ (2) of [Stacks, Tag 01PH].  That complement maps onto `|U| = |X| ∖ |V(ℐ)|`, continuously,
so `|U|` is a quasi-compact subset of `|X|`, and Tag 03E4 turns that into quasi-compactness of
the open subspace `U`. -/
@[stacks 0855 "part (3) implies part (2)"]
theorem isQuasiCompactSpace_of_hasFiniteTypeQuasicoherentIdealZeroLocus
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    {U : Subfunctor X.1} (hU : IsOpenSubspace B S hS U)
    (h : HasFiniteTypeQuasicoherentIdealZeroLocus B S hS X U) :
    IsQuasiCompactSpace B S hS U.toFunctor := by
  obtain ⟨J, ⟨hJq, hJft⟩, hJU⟩ := h
  have hJcart : IsCartesianOnAffineCharts J.toSheafOfModules :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 J.toSheafOfModules hJq
  obtain ⟨W, p, hWaff, hpsurj, hpet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hXqc
  let A : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk p, (isEtale_iff_presheaf_of_yoneda B S hS p).1 hpet⟩
  have hA : Function.Surjective (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj A)) A.obj.hom) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 W p).1 hpsurj
  have _ : IsAffine (chartScheme A) := hWaff
  have hcompact : IsCompact
      (((idealSheafDataOfChart B S hS X J hJcart A).support.compl : (chartScheme A).Opens) :
        Set (chartScheme A)) :=
    isCompact_of_isFiniteType_of_support_eq_compl _ _
      (isFiniteType_idealSheafDataOfChart B S hS X J hJq hJft hJcart A) (by simp)
  refine isQuasiCompactSpace_of_isCompact_range B S hS X.2 hU ?_
  have hrange : Set.range (pointsMap B S hS U.toFunctor U.ι) = idealUnitLocus B S hS X J := by
    rw [← compl_compl (Set.range (pointsMap B S hS U.toFunctor U.ι)), hJU, idealZeroLocus,
      compl_compl]
  rw [hrange, idealUnitLocus_eq_image_support_compl B S hS X J hJcart A hA]
  exact hcompact.image (continuous_chartSchemeToPoints B S hS A)

end AlgebraicGeometry.Space

end
