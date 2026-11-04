module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpClosedPointDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationIsolatedFibrePoint
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality
public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.Topology.Irreducible.SingletonComponent
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpClosedPointDimension
import all StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk

/-!
# Closed points of a modification of a normal surface singularity, and Tag 0B4Q

Let `A` be a two-dimensional Noetherian local normal domain and `f : X ⟶ Spec A` a
modification. Every closed point of `X` has a two-dimensional local ring: either it is isolated
in the fibre over the closed point, and then `f` is an isomorphism by Zariski's main theorem, or
the generic point of the component of the fibre through it and the generic point of `X` give a
chain of two proper specializations into it.

The file also records [Stacks, Tag 0B4Q] — a Nagata regular local ring of dimension two defines a
rational singularity — in the form used by the assembly of Lipman's theorem
(`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_ringKrullDim_eq_two`),
where the domain structure is given by `letI`. Its proof is the library's
`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_eq_two_of_isModification`
* `AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_ringKrullDim_eq_two`:
  [Stacks, Tag 0B4Q].

## References

* [Stacks Project, Tag 0B4Q](https://stacks.math.columbia.edu/tag/0B4Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A closed point of a modification of a two-dimensional normal local base has a
two-dimensional local ring.** Let `A` be a two-dimensional Noetherian local normal domain and
`f : X ⟶ Spec A` a modification. A closed point `x` of `X` lies over the closed point of `Spec A`;
either it is isolated in that fibre, and then `f` is an isomorphism by Zariski's main theorem, or
the generic point of the component of the fibre through `x` and the generic point of `X` give a
chain of two proper specializations into `x`. -/
theorem ringKrullDim_stalk_eq_two_of_isModification (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNormalDomain A] [IsNoetherianRing A] (hdim : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hmod : IsModification f) (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = 2 := by
  classical
  have : IsIntegral X := hmod.source_isIntegral
  have : IsProper f := hmod.isProper
  have hdimX : topologicalKrullDim X = 2 := by
    have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
    rw [IsBirational.topologicalKrullDim_eq_of_isClosedMap hmod.1 f.isClosedMap]
    show topologicalKrullDim (PrimeSpectrum A) = 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ 2 := by
    rw [← hdimX, topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    exact le_iSup_of_le x le_rfl
  refine le_antisymm hle ?_
  have hfx : f x = IsLocalRing.closedPoint A := by
    have himage : IsClosed ({f x} : Set (Spec (.of A))) := by
      simpa using f.isClosedMap _ hx
    have hmem : (IsLocalRing.closedPoint A : Spec (.of A)) ∈
        ({f x} : Set (Spec (.of A))) := by
      rw [← himage.closure_eq]
      exact specializes_iff_mem_closure.mp (IsLocalRing.specializes_closedPoint (f x))
    exact (Set.mem_singleton_iff.mp hmem).symm
  have : IsClosedImmersion ((Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (IsLocalRing.isClosed_singleton_closedPoint A)
  have : IsClosedImmersion (f.fiberι (IsLocalRing.closedPoint A)) :=
    inferInstanceAs (IsClosedImmersion (Limits.pullback.fst f _))
  have hinj : Function.Injective (f.fiberι (IsLocalRing.closedPoint A)) :=
    (f.fiberι (IsLocalRing.closedPoint A)).isClosedEmbedding.injective
  have hmem : x ∈ f ⁻¹' {IsLocalRing.closedPoint A} :=
    Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hfx)
  obtain ⟨p, hp⟩ : ∃ p : f.fiber (IsLocalRing.closedPoint A),
      f.fiberι (IsLocalRing.closedPoint A) p = x :=
    (f.range_fiberι (IsLocalRing.closedPoint A)).ge hmem
  have hpclosed : IsClosed ({p} : Set (f.fiber (IsLocalRing.closedPoint A))) := by
    have hpre : ({p} : Set (f.fiber (IsLocalRing.closedPoint A))) =
        f.fiberι (IsLocalRing.closedPoint A) ⁻¹' {x} := by
      refine Set.eq_of_subset_of_subset (fun q hq => ?_) (fun q hq => ?_)
      · have hqp : q = p := Set.mem_singleton_iff.mp hq
        exact Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (hqp ▸ hp))
      · have hqx : f.fiberι (IsLocalRing.closedPoint A) q = x :=
          Set.mem_singleton_iff.mp (Set.mem_preimage.mp hq)
        exact Set.mem_singleton_iff.mpr (hinj (hqx.trans hp.symm))
    rw [hpre]
    exact hx.preimage (f.fiberι (IsLocalRing.closedPoint A)).continuous
  have hCmem : irreducibleComponent p ∈
      irreducibleComponents (f.fiber (IsLocalRing.closedPoint A)) :=
    irreducibleComponent_mem_irreducibleComponents p
  have hgen : IsGenericPoint hCmem.1.genericPoint (irreducibleComponent p) :=
    hCmem.1.isGenericPoint_genericPoint isClosed_irreducibleComponent
  by_cases hη : hCmem.1.genericPoint = p
  · have hCsingle : irreducibleComponent p = {p} := by
      rw [← hgen, hη]
      exact hpclosed.closure_eq
    have hfin : (irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))).Finite :=
      have := finite_irreducibleComponents_fiber_closedPoint A f
      Set.toFinite _
    have hopen : IsOpen ({p} : Set (f.fiber (IsLocalRing.closedPoint A))) :=
      Stacks.Topology.Irreducible.isOpen_singleton_of_mem_irreducibleComponents hfin p
        (hCsingle ▸ hCmem)
    have hiso : IsIso f := hmod.isIso_of_isOpen_singleton_fiber p hopen
    have hstalk : IsIso (f.stalkMap x) := ((isIso_iff_isIso_stalkMap f).mp hiso).2 x
    have heq := ringKrullDim_eq_of_ringEquiv
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [hfx, ringKrullDim_stalk_closedPoint, hdim] at heq
    exact le_of_eq heq
  · have hηp : hCmem.1.genericPoint ⤳ p := hgen.specializes mem_irreducibleComponent
    have hmid : f.fiberι (IsLocalRing.closedPoint A) hCmem.1.genericPoint ⤳ x :=
      hp ▸ hηp.map (f.fiberι (IsLocalRing.closedPoint A)).continuous
    have hmidne : f.fiberι (IsLocalRing.closedPoint A) hCmem.1.genericPoint ≠ x := fun he =>
      hη (hinj (he.trans hp.symm))
    have htop : genericPoint X ⤳ f.fiberι (IsLocalRing.closedPoint A) hCmem.1.genericPoint :=
      genericPoint_specializes _
    have htopne : genericPoint X ≠ f.fiberι (IsLocalRing.closedPoint A) hCmem.1.genericPoint := by
      intro he
      have hgenf : f (genericPoint X) = genericPoint (Spec (.of A)) :=
        IsBirational.genericPoint_eq f hmod.isBirational
      have hclosed : genericPoint (Spec (.of A)) = IsLocalRing.closedPoint A := by
        rw [← hgenf, he]
        exact f.apply_fiberι (IsLocalRing.closedPoint A) hCmem.1.genericPoint
      refine maximalIdeal_ne_bot_of_dimension_two A hdim ?_
      have hbot : (IsLocalRing.closedPoint A : PrimeSpectrum A) = (⊥ : PrimeSpectrum A) := by
        rw [← hclosed]
        exact genericPoint_eq_bot_of_affine (.of A)
      simpa [IsLocalRing.closedPoint] using congrArg PrimeSpectrum.asIdeal hbot
    exact two_le_ringKrullDim_stalk_of_specializes_of_specializes htop hmid htopne hmidne


/-- **Stacks Project, Tag 0B4Q.** A Nagata regular local ring of dimension two defines a rational
singularity. -/
@[stacks 0B4Q]
theorem definesRationalSingularity_of_isRegularLocalRing_of_ringKrullDim_eq_two (A : Type u)
    [CommRing A] [IsRegularLocalRing A] [IsNagataRing A] (hdim : ringKrullDim A = 2) :
    letI := IsRegularLocalRing.isDomain A; DefinesRationalSingularity A :=
  definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing A hdim

end AlgebraicGeometry

end
