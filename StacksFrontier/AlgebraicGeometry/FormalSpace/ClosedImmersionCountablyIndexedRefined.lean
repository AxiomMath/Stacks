module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionMcQuillanRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrumRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful

/-!
# Closed immersions into countably indexed affine formal algebraic spaces: the quotient

Let `A` be a weakly admissible topological ring over `S` with a countable fundamental system of
neighbourhoods of `0`, and let `g : A ⟶ C` be a continuous homomorphism over `S` to a weakly
admissible ring whose formal spectrum is a closed immersion. Then `ker g` is a closed ideal of `A`
and `g` identifies `A ⧸ ker g` with `C` topologically.

## Main results

* `AlgebraicGeometry.FormalSpace.isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion'`: the
  kernel of such a `g` is closed and `g` induces a ring isomorphism and homeomorphism
  `A ⧸ ker g ≃ C`.

## References

* [Stacks Project, Tag 0AQI](https://stacks.math.columbia.edu/tag/0AQI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section CountablyIndexed

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end CountablyIndexed

section Correspondence

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] sheaf_hasColimits

end Correspondence

section Quotient

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- Let `A` be an object of `WAdm^count`, that is, a weakly admissible topological ring over `S`
with a countable fundamental system of neighbourhoods of `0`, let `C` be weakly admissible, and let
`g : A ⟶ C` be a continuous homomorphism over `S` whose formal spectrum is a closed immersion.
Then `K = ker g` is a closed ideal of `A` and `g` identifies `A/K` with `C` topologically, so the
closed immersion is `Spf` of `A ⟶ A/K`. -/
@[stacks 0AQI "the quotient by a closed ideal"]
theorem isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion'
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hC : TopologicalRing.IsWeaklyAdmissible C)
    (hcount : (nhds (0 : A)).IsCountablyGenerated)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C} (g : ContinuousHom D E)
    (hg : IsClosedImmersion B S hS (formalSpectrumMap hA g)) :
    IsClosed (RingHom.ker g.toRingHom : Set A) ∧
      ∃ e : (A ⧸ RingHom.ker g.toRingHom) ≃+* C,
        (∀ a : A, e (Ideal.Quotient.mk (RingHom.ker g.toRingHom) a) = g.toRingHom a) ∧
          IsHomeomorph e := by
  have : T2Space A := hA.2.2
  have : T2Space C := hC.2.2
  refine ⟨RingHom.isClosed_ker_of_continuous g.toRingHom g.continuous, ?_⟩
  exact RingHom.quotientKerEquiv_of_isTaut_of_denseRange g.toRingHom g.continuous hA.2.1
    hcount (isTaut_of_isClosedImmersion_formalSpectrumMap hA hC g hg)
    (denseRange_of_isClosedImmersion_formalSpectrumMap hA hC g hg)

end Quotient

end AlgebraicGeometry.FormalSpace

end
