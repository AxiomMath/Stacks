module

public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertySourceCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagramNoetherian
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.Topology.Algebra.AdicTopology.FlatLocalPropertyRefined

/-!
# Flatness of the formal spectrum of a flat map of Noetherian adic rings

Let `S` be a scheme contained in a big fppf site `B` and let `g : A → C` be a continuous flat
homomorphism of Noetherian adic topological rings over `S`. Then `Spf C ⟶ Spf A` is flat in the
sense of Definition 0GCC. Both formal spectra are locally Noetherian, and the one-member
covering of `Spf C` by its identity, factored through the identity of `Spf A`, witnesses
condition (3) of Stacks 0GCD; the implication (3) ⟹ (1) of Stacks 0ANG for locally Noetherian
formal algebraic spaces (Remark 0ANI), with flatness a local property of `WAdm^{Noeth}` by
Stacks 0GC9, then gives flatness on every affine étale square.

The case used in Stacks 0GDA is an extension `A ⊂ A'` of complete discrete valuation rings: `A'`
is torsion free over the Dedekind domain `A`, hence flat.

## Main results

* `AlgebraicGeometry.FormalSpace.isFlat_formalSpectrumMap_of_flat`: the formal spectrum of a
  flat continuous homomorphism of Noetherian adic rings is flat.
* `AlgebraicGeometry.FormalSpace.isFlat_formalSpectrumMap_of_isExtension`: the formal spectrum
  of an extension of complete discrete valuation rings is flat.

## References

* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0GC9](https://stacks.math.columbia.edu/tag/0GC9)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GCD](https://stacks.math.columbia.edu/tag/0GCD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The formal spectrum of a flat continuous homomorphism `g : A → C` of Noetherian adic
topological rings over `S` is flat: the identity of `Spf C`, factored through the identity of
`Spf A` by `Spf g`, is an affine étale covering witnessing condition (3) of Stacks 0GCD, and the
implication (3) ⟹ (1) of Stacks 0ANG for locally Noetherian formal algebraic spaces gives
flatness on every affine étale square. -/
theorem isFlat_formalSpectrumMap_of_flat {A C : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A] [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C] [IsNoetherianRing C]
    (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (hAw : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (E : QuotientSystem B S hS C) (g : ContinuousHom D E) (hg : g.toRingHom.Flat) :
    IsFlat B S hS (formalSpectrumMap hAw g) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hEaff :=
    isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hC E (Iso.refl _)
  have hDaff :=
    isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hA D (Iso.refl _)
  rw [isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram]
  refine hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocallyNoetherian B S hS
    _ TopologicalRing.flat_isLocalNoetherian (TopologicalRing.flat_isomorphismInvariant _) _
    (isLocallyNoetherian_formalSpectrum B S hS hC E)
    (isLocallyNoetherian_formalSpectrum B S hS hA D)
    ⟨PUnit.{u + 2}, fun _ ↦ formalSpectrum E, fun _ ↦ 𝟙 _,
      ⟨fun _ ↦ hEaff, fun _ ↦ isRepresentableEtale_id B S hS _, ?_⟩,
      fun _ ↦ ⟨formalSpectrum D, 𝟙 _, formalSpectrumMap hAw g, hDaff,
        isRepresentableEtale_id B S hS _, by simp, ?_⟩⟩
  · have : IsSplitEpi (Sigma.desc fun _ : PUnit.{u + 2} ↦ 𝟙 (formalSpectrum E)) :=
      ⟨⟨Sigma.ι (fun _ : PUnit.{u + 2} ↦ formalSpectrum E) PUnit.unit, by simp⟩⟩
    exact (Sheaf.isLocallySurjective_iff_epi _).2 inferInstance
  · refine hasPropertyOnAffineChartMap_of_presentation B S hS TopologicalRing.IsNoetherianAdic
      TopologicalRing.IsFlatHom (fun _ _ _ _ _ hR ↦ hR.1.isWeaklyAdmissible) ?_ ?_ _
      ⟨hA, inferInstance⟩ ⟨hC, inferInstance⟩ D E (Iso.refl _) (Iso.refl _) g (by simp) hg
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ψ e _ _ _ hψ
      exact RingHom.Flat.comp (RingHom.Flat.of_bijective e.bijective) hψ
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ψ e _ _ _ hψ
      exact RingHom.Flat.comp hψ (RingHom.Flat.of_bijective e.bijective)

/-- **Stacks 0GCD** applied to an extension `A ⊂ A'` of complete discrete valuation rings: `A'`
is torsion free over the Dedekind domain `A`, hence flat, so the induced morphism
`Spf A' ⟶ Spf A` of formal spectra is flat in the sense of Definition 0GCC. -/
theorem isFlat_formalSpectrumMap_of_isExtension (A A' : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [TopologicalSpace A']
    [IsTopologicalRing A'] [IsLinearTopology A' A'] [Algebra A A']
    [IsDiscreteValuationRing.IsExtension A A']
    (hA : _root_.IsAdic (IsLocalRing.maximalIdeal A))
    (hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hA' : _root_.IsAdic (IsLocalRing.maximalIdeal A'))
    (hA'c : IsAdicComplete (IsLocalRing.maximalIdeal A') A')
    (hAw : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (D' : QuotientSystem B S hS A') (e : ContinuousHom D D') (he : e.toRingHom = algebraMap A A') :
    IsFlat B S hS (formalSpectrumMap hAw e) := by
  have hw := TopologicalRing.isWeaklyAdmissible_of_isAdic hA hAc
  have hw' := TopologicalRing.isWeaklyAdmissible_of_isAdic hA' hA'c
  have : Module.Flat A A' := inferInstance
  refine isFlat_formalSpectrumMap_of_flat B S hS
    ⟨⟨_, TopologicalRing.isIdealOfDefinition_of_isAdic hA, hA⟩, hw.2.2, hw.2.1⟩
    ⟨⟨_, TopologicalRing.isIdealOfDefinition_of_isAdic hA', hA'⟩, hw'.2.2, hw'.2.1⟩
    hAw D D' e ?_
  rw [he]
  exact RingHom.flat_algebraMap_iff.mpr this

end AlgebraicGeometry.FormalSpace

end
