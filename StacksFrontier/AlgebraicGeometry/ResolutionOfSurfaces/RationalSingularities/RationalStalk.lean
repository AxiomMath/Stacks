module

public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SpreadOutModification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.PuncturedSpectrumModification
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CohomologyModelBridge
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SpreadOutVanishing

/-!
# The local rings of a normal modification of a rational singularity

Let `A` be a two-dimensional Noetherian local normal domain defining a rational singularity and
`f : X ⟶ Spec(A)` a modification with `X` normal. Then the local ring of `X` at every closed point
defines a rational singularity. This is [Stacks, Tag 0BG0] in its local-ring form.

## Main results

* `AlgebraicGeometry.definesRationalSingularity_stalk_of_isModification`: [Stacks, Tag 0BG0],
  local-ring form.

## Implementation notes

The proof follows the source. A normal modification of `Spec 𝒪_{X, x}` is spread out to a
proper `g : X' ⟶ X` which is an isomorphism over `X ∖ {x}` ([Stacks, Tags 0B3X and 0BFN]). Then
`X'` is a normal modification of `Spec(A)` by Step 4 of the source's proof,
`AlgebraicGeometry.isNormal_and_isModification_of_isPullback_fromSpecStalk`. So
`H¹(X', 𝒪_{X'}) = 0`, and the vanishing descends to the given modification of `Spec 𝒪_{X, x}`.

The isomorphism over the punctured spectrum is
`AlgebraicGeometry.modificationIsFinitePresentationAway_of_isLocallyNoetherian` (Tags 0AB7 and
0AB1). Step 4 is the theorem just named; the variant
`AlgebraicGeometry.SpreadOutIsNormalModification`, asking only that `Y` be normal, is false. The
descent of the vanishing, which the source obtains from the first conclusion of
[Stacks, Tag 0AXF] and flat base change ([Stacks, Tag 02KH]), is
`AlgebraicGeometry.isZeroFirstStructureSheafCohomology_of_isPullback_fromSpecStalk`: it uses that
the spread-out morphism is an isomorphism away from `x`, and argues by Mayer–Vietoris.

## References

* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open GlueingNearPoint

/-- **[Stacks, Tag 0BG0], local-ring form.** Let `A` be a two-dimensional Noetherian local normal
domain defining a rational singularity, `f : X ⟶ Spec(A)` a modification with `X` normal, and
`x ∈ X` a closed point other than the generic point. Then the local ring `𝒪_{X, x}` defines a
rational singularity. -/
theorem definesRationalSingularity_stalk_of_isModification (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2)
    (hA : DefinesRationalSingularity A)
    {X : Scheme.{u}} [IsNormal X] (f : X ⟶ Spec (.of A)) (hf : IsModification f) (x : X)
    (hx : IsClosed ({x} : Set X)) (hxη : letI := hf.source_isIntegral; x ≠ genericPoint X) :
    DefinesRationalSingularity ↥(X.presheaf.stalk x) := by
  intro Y hYnormal p hp
  have : IsProper f := hf.isProper
  have : IsIntegral X := hf.source_isIntegral
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  have hemb := (puncturedOpen hx).isOpen.isOpenEmbedding_subtypeVal
  have : NoetherianSpace (puncturedOpen hx).toScheme := hemb.isEmbedding.noetherianSpace
  have hqc : QuasiCompact (puncturedOpen hx).ι := quasiCompact_of_noetherianSpace_source _
  have hdimX : topologicalKrullDim X = ringKrullDim A := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hf.1.topologicalKrullDim_eq_of_isClosedMap f.isClosedMap
  have hdimx : ringKrullDim (X.presheaf.stalk x) ≤ 2 := by
    refine le_trans ?_ (hdimX.trans_le hdim.le)
    rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    exact le_iSup_of_le x le_rfl
  have hfp := modificationIsFinitePresentationAway_of_isLocallyNoetherian x hx hdimx p hYnormal hp
  obtain ⟨X', g, q, hgaway, hgproper, hsq⟩ :=
    exists_isPullback_fromSpecStalk_of_isProper X x hx hqc p hfp hp.isProper
  obtain ⟨hX'normal, hmod⟩ := isNormal_and_isModification_of_isPullback_fromSpecStalk f hf x hx
    hxη g p q hsq hgproper hgaway.2 hYnormal hp
  exact isZeroFirstStructureSheafCohomology_of_isPullback_fromSpecStalk A hdim f hf x hx g p q hsq
    hgproper hgaway.2 (hA X' (g ≫ f) hmod)

end AlgebraicGeometry

end
