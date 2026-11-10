module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineEtaleChartTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeChartConditionDirections
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocallyOfFiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertyClassClosure

/-!
# A rig-étale morphism of locally Noetherian formal algebraic spaces is locally of finite type

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0AQN** says that a rig-étale
morphism of locally Noetherian formal algebraic spaces over `S` is locally of finite type.

The source's proof: the property "rig-étale" of arrows of `WAdm^{Noeth}` (Lemma 0AQL) implies
the equivalent conditions (a)–(d) of Stacks 0ANU, so the statement follows from Stacks 0ANW.
This file runs that proof with nothing assumed beyond the source's hypotheses.

## Main results

* `RingHom.IsRigEtale.isTautTopologicallyOfFiniteTypeHom`: a rig-étale continuous homomorphism
  of Noetherian adic topological rings (Definition 0GCV) is taut and topologically of finite
  type, i.e. satisfies condition (c) of Stacks 0ANU.
* `AlgebraicGeometry.FormalSpace.isNoetherianAdic_of_isNoetherian_of_iso_formalSpectrum`: a
  weakly admissible topological ring whose formal spectrum is a Noetherian affine formal
  algebraic space is Noetherian and adic.
* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_of_isRigEtale_of_isLocallyNoetherian`:
  **Stacks 0AQN**.

## Implementation notes

Definition 0GCV asks a rig-étale map to satisfy the equivalent conditions of Stacks 0GBW, which
`RingHom.IsRigEtale` carries in the form of condition (6) of that lemma. Condition (2) of
Stacks 0GBW is tautness together with topological finite type, which is condition (c) of
Stacks 0ANU; the passage is `Rig.adicFiniteType_tfae`, whose finite generation hypotheses on
ideals of definition hold because both rings are Noetherian.

Stacks 0ANW tests its chart condition on presentations by rings of `WAdm^{count}`, whereas
Definition 0AQM tests rig-étaleness on presentations by rings of `WAdm^{Noeth}`. The two are
reconciled by the charts themselves: an affine formal algebraic space representable étale over
a locally Noetherian formal algebraic space is Noetherian (Stacks 0AKX with Stacks 0AKW), so it
has a Noetherian adic presenting ring, and any other weakly admissible ring presenting it is
isomorphic to that one as a topological ring (Stacks 0AIC), hence Noetherian and adic too.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AKW](https://stacks.math.columbia.edu/tag/0AKW)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
* [Stacks Project, Tag 0ANW](https://stacks.math.columbia.edu/tag/0ANW)
* [Stacks Project, Tag 0AQL](https://stacks.math.columbia.edu/tag/0AQL)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
* [Stacks Project, Tag 0AQN](https://stacks.math.columbia.edu/tag/0AQN)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace RingHom.IsRigEtale

variable {A : Type u} {C : Type v}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [IsNoetherianRing A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
  [IsNoetherianRing C]

/-- A rig-étale continuous homomorphism of Noetherian adic topological rings (Definition 0GCV)
is taut and topologically of finite type: condition (6) of Stacks 0GBW, which rig-étaleness
includes, gives condition (2) of that lemma, which is condition (c) of Stacks 0ANU. -/
theorem isTautTopologicallyOfFiniteTypeHom {φ : A →+* C} (hφ : RingHom.IsRigEtale φ)
    (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C) :
    RingHom.IsTaut φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ := by
  obtain ⟨I, hI, -⟩ := hA.1
  obtain ⟨J, hJ, -⟩ := hC.1
  exact ((Rig.adicFiniteType_tfae φ hA hC ⟨I, hI, IsNoetherian.noetherian I⟩
    ⟨J, hJ, IsNoetherian.noetherian J⟩).out 6 2).mp hφ.1

end RingHom.IsRigEtale

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A weakly admissible topological ring over `S` whose formal spectrum is isomorphic to a
Noetherian affine formal algebraic space is Noetherian and adic: it presents that space, and so
does the Noetherian adic ring of Definition 0AKY, so the two are isomorphic as topological rings
by the uniqueness of the presenting ring (Stacks 0AIC). -/
theorem isNoetherianAdic_of_isNoetherian_of_iso_formalSpectrum {U : FppfSheaf B S hS}
    (hU : IsNoetherian B S hS U) {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (E : QuotientSystem B S hS A) (e : U ≅ formalSpectrum E) :
    TopologicalRing.IsNoetherianAdic A := by
  obtain ⟨-, A', _, _, _, _, hA'U, hnoeth, hadic⟩ := hU
  have hAU : IsPresentingRing B S hS A U := ⟨hA, ⟨E.weakIdealColimitPresentation.ofIso e⟩⟩
  obtain ⟨φ, hφ, hφ'⟩ := exists_continuous_ringEquiv_of_isPresentingRing hA'U hAU
  exact TopologicalRing.isNoetherianAdic_of_ringEquiv φ hφ hφ' ⟨hadic, hnoeth⟩

/-- **Stacks 0AQN.** A rig-étale morphism of locally Noetherian formal algebraic spaces over
`S` is locally of finite type.

By the implication (1) ⟹ (4) of Stacks 0ANW it suffices that every affine representable étale
square over `f` has its upper map given by a taut, topologically of finite type morphism of
`WAdm^{count}`. The two charts of such a square are Noetherian (Stacks 0AKX), so every weakly
admissible ring presenting them is Noetherian and adic (Stacks 0AIC); rig-étaleness of `f` then
says that the presenting homomorphism is rig-étale, hence taut and topologically of finite type
(Stacks 0GBW). -/
@[stacks 0AQN]
theorem isLocallyOfFiniteType_of_isRigEtale_of_isLocallyNoetherian {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hf : IsRigEtale B S hS f) :
    IsLocallyOfFiniteType B S hS f := by
  refine
    isLocallyOfFiniteType_of_hasPropertyOnEveryAffineEtaleDiagram_tautTopologicallyOfFiniteType
    f (isLocallyCountablyIndexed_of_isLocallyNoetherian' hX)
    (isLocallyCountablyIndexed_of_isLocallyNoetherian' hY) ?_
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ _ hR hA D E eU eV g hg
  obtain ⟨hAadic, hAnoeth⟩ := isNoetherianAdic_of_isNoetherian_of_iso_formalSpectrum
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hY b hV hb) hA D eV
  obtain ⟨hRadic, hRnoeth⟩ := isNoetherianAdic_of_isNoetherian_of_iso_formalSpectrum
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hX a hU ha) hR.1 E eU
  exact (hf U V hU hV a b t ha.1 hb.1 ha.2 hb.2 hsq A R hAadic hRadic hA D E eU eV g
    hg).isTautTopologicallyOfFiniteTypeHom hAadic hRadic

end AlgebraicGeometry.FormalSpace

end
