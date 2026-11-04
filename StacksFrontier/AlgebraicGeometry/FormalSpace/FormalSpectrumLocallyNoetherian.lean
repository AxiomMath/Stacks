module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsIntoMcQuillanAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# The formal spectrum of a Noetherian adic ring is locally Noetherian

Let `S` be a scheme contained in a big fppf site `B` and let `A` be a Noetherian adic
topological ring. Then `Spf A`, formed from a quotient system of `A` over `S`, is a locally
Noetherian formal algebraic space in the sense of **Stacks 0AKY**. The ring `A` is small
enough for the site to contain the coproduct of its quotient spectra, so `Spf A` is an affine
formal algebraic space
(`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic`);
it is presented by `A` itself, which
is Noetherian and adic, so it is a Noetherian affine formal algebraic space (Stacks 0AID), and
the one-member family consisting of its identity is an atlas as in Definition 0AIM.

The case used in Stacks 0GDA is that of a complete discrete valuation ring with its
`𝔪`-adic topology, recorded separately.

## Main results

* `AlgebraicGeometry.FormalSpace.isNoetherian_formalSpectrum`: `Spf A` is a Noetherian affine
  formal algebraic space.
* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_formalSpectrum`: `Spf A` is locally
  Noetherian.
* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_formalSpectrum_of_isAdicComplete`: the
  same for a Noetherian ring complete for the adic topology of an ideal it carries, in
  particular for a complete discrete valuation ring.

## References

* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- **Stacks 0AID (5)** for a formal spectrum: the formal spectrum of a Noetherian adic
topological ring is a Noetherian affine formal algebraic space, presented by the ring itself. -/
theorem isNoetherian_formalSpectrum [IsNoetherianRing A] (hA : TopologicalRing.IsAdic A)
    (D : QuotientSystem B S hS A) : IsNoetherian B S hS (formalSpectrum D) :=
  ⟨hasSomeSurjectivePresentation_formalSpectrum_of_isAffine B S hS
      (Rig.weaklyAdmissible_of_isAdicRing hA) D
      (isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hA D (Iso.refl _)),
    A, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Rig.weaklyAdmissible_of_isAdicRing hA, ⟨D.weakIdealColimitPresentation⟩⟩,
    inferInstance, hA⟩

/-- **Stacks 0AKY** for a formal spectrum: the formal spectrum of a Noetherian adic topological
ring over `S` is a locally Noetherian formal algebraic space, being a Noetherian affine formal
algebraic space and so its own one-member atlas. -/
theorem isLocallyNoetherian_formalSpectrum [IsNoetherianRing A] (hA : TopologicalRing.IsAdic A)
    (D : QuotientSystem B S hS A) : IsLocallyNoetherian B S hS (formalSpectrum D) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have haff :=
    isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hA D (Iso.refl _)
  refine ⟨isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS haff,
    PUnit.{u + 2}, fun _ ↦ formalSpectrum D, fun _ ↦ 𝟙 _, fun _ ↦ haff,
    fun _ ↦ isRepresentableEtale_id B S hS _, ?_,
    fun _ ↦ isNoetherian_formalSpectrum B S hS hA D⟩
  have : IsSplitEpi (Sigma.desc fun _ : PUnit.{u + 2} ↦ 𝟙 (formalSpectrum D)) :=
    ⟨⟨Sigma.ι (fun _ : PUnit.{u + 2} ↦ formalSpectrum D) PUnit.unit, by simp⟩⟩
  exact (Sheaf.isLocallySurjective_iff_epi _).2 inferInstance

/-- **Stacks 0AKY** for the formal spectrum of a Noetherian ring complete for the adic topology
of an ideal `I` it carries — for instance a complete discrete valuation ring with its
`𝔪`-adic topology: such a ring is an adic topological ring, so its formal spectrum is locally
Noetherian. -/
theorem isLocallyNoetherian_formalSpectrum_of_isAdicComplete [IsNoetherianRing A] {I : Ideal A}
    (hI : _root_.IsAdic I) (hc : IsAdicComplete I A) (D : QuotientSystem B S hS A) :
    IsLocallyNoetherian B S hS (formalSpectrum D) :=
  have hw := TopologicalRing.isWeaklyAdmissible_of_isAdic hI hc
  isLocallyNoetherian_formalSpectrum B S hS
    ⟨⟨I, TopologicalRing.isIdealOfDefinition_of_isAdic hI, hI⟩, hw.2.2, hw.2.1⟩ D

end AlgebraicGeometry.FormalSpace

end
