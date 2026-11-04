module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut

/-!
# Closed immersions into a countably indexed affine formal algebraic space

Let `X` be a countably indexed affine formal algebraic space over `S` and let `f : Y ⟶ X` be a
closed immersion. Then `Y` is countably indexed affine, and `f` is `Spf` of a continuous
homomorphism `A ⟶ C` of objects of `WAdm^count` which identifies `C` topologically with the
quotient of `A` by a closed ideal (Stacks 0AQI). The homomorphism is taut by Stacks 0AN5,
implication (1) ⟹ (3).

## Main results

* `IsClosedImmersion.isCountablyIndexedAffine_and_exists_closedIdealQuotient`: a closed immersion
  `f : Y ⟶ X` into a countably indexed affine formal algebraic space has countably indexed affine
  source and is `Spf` of the quotient map of an object of `WAdm^count` by a closed ideal.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AQI](https://stacks.math.columbia.edu/tag/0AQI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `X` be a countably indexed affine formal algebraic space over `S` and let `f : Y ⟶ X` be a
closed immersion of fppf sheaves over `S`. Then `Y` is a countably indexed affine formal algebraic
space, and `f` is `Spf` of a continuous homomorphism `g : A ⟶ C` of objects of `WAdm^count` whose
kernel `K` is a closed ideal of `A` and which identifies `A/K` with `C` topologically; that is, `f`
corresponds to `A ⟶ A/K`. -/
@[stacks 0AQI]
theorem IsClosedImmersion.isCountablyIndexedAffine_and_exists_closedIdealQuotient
    {X Y : FppfSheaf B S hS} (hX : IsCountablyIndexedAffine B S hS X) (f : Y ⟶ X)
    (hf : IsClosedImmersion B S hS f) :
    IsCountablyIndexedAffine B S hS Y ∧
      ∃ (P : SpfPresentation B S hS X) (Q : SpfPresentation B S hS Y)
        (hA : TopologicalRing.IsWeaklyAdmissible P.ring),
        (nhds (0 : P.ring)).IsCountablyGenerated ∧
        TopologicalRing.IsWeaklyAdmissible Q.ring ∧
        ∃ (eX : X ≅ formalSpectrum P.system) (eY : Y ≅ formalSpectrum Q.system)
          (g : ContinuousHom P.system Q.system),
          IsClosed (RingHom.ker g.toRingHom : Set P.ring) ∧
          (∃ e : (P.ring ⧸ RingHom.ker g.toRingHom) ≃+* Q.ring,
            (∀ a : P.ring,
              e (Ideal.Quotient.mk (RingHom.ker g.toRingHom) a) = g.toRingHom a) ∧
            IsHomeomorph e) ∧
          f = eY.hom ≫ formalSpectrumMap hA g ≫ eX.inv := by
  obtain ⟨P, Q, hA, hcountA, hC, hcountC, eX, eY, g, hgci, hfg⟩ :=
    exists_spfPresentation_continuousHom_of_isClosedImmersion hX f hf
  obtain ⟨hker, hquot⟩ :=
    isClosed_ker_and_quotientKerEquiv_of_isClosedImmersion hA hC hcountA g hgci
      (isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap B S hS hA hC _ _
        (QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS P.system hA hcountA)
        (QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS Q.system hC hcountC) g hgci.1)
  exact ⟨isCountablyIndexedAffine_of_isClosedImmersion B S hS hX f hf,
    P, Q, hA, hcountA, hC, eX, eY, g, hker, hquot, hfg⟩

end AlgebraicGeometry.FormalSpace

end
