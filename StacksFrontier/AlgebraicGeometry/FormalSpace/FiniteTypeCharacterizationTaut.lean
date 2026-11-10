module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful

/-!
# Stacks 0ANV with tautness derived

Let `S` be a scheme contained in a big fppf site `B`, and let `φ : A ⟶ C` be a continuous
homomorphism of weakly admissible topological rings over `S` whose neighbourhood filters of
zero are countably generated.

`AlgebraicGeometry.FormalSpace.formalSpectrumMap_finiteType_tfae` (Stacks 0ANV) takes the
tautness of `φ` as the hypothesis `htaut`. This file removes it: being of finite type contains
representability by algebraic spaces, and
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`,
the implication (1) ⟹ (3) of Stacks 0AN5, turns that into tautness. Its two set-theoretic
hypotheses come from the countable generation of the two neighbourhood filters of zero through
`AlgebraicGeometry.FormalSpace.QuotientSystem.hasLargeSite_of_isCountablyGenerated`.

## Main results

* `AlgebraicGeometry.FormalSpace.formalSpectrumMap_finiteType_tfae_deriving_taut`: the
  equivalences of Stacks 0ANV without the tautness hypothesis.

## Implementation notes

The two inputs `hqc` and `h0ANT` of
`AlgebraicGeometry.FormalSpace.formalSpectrumMap_finiteType_tfae` remain, for the reasons
recorded there.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
* [Stacks Project, Tag 0ANV](https://stacks.math.columbia.edu/tag/0ANV)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The equivalences of **Stacks 0ANV** with tautness of the homomorphism derived instead of
assumed. Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings
over `S` whose neighbourhood filters of zero are countably generated. Then `Spf (φ)` being
locally of finite type, `Spf (φ)` being of finite type, `φ` being of finite type modulo every
weak ideal of definition, and `φ` being taut and topologically of finite type are all
equivalent.

Compared with `AlgebraicGeometry.FormalSpace.formalSpectrumMap_finiteType_tfae`, tautness is
deduced from being of finite type by the implication (1) ⟹ (3) of Stacks 0AN5. -/
theorem formalSpectrumMap_finiteType_tfae_deriving_taut {A C : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (hAcount : (nhds (0 : A)).IsCountablyGenerated)
    (hCcount : (nhds (0 : C)).IsCountablyGenerated)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (g : ContinuousHom D E)
    (hsrc : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E))
    (htgt : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
    (hqc : IsFiniteTypeOfIsLocallyOfFiniteTypeOnAffine B S hS)
    (h0ANT : IsLocallyOfFiniteTypeFormalSpectrumMapOfFiniteTypeModulo B S hS) :
    List.TFAE
      [IsLocallyOfFiniteType B S hS (formalSpectrumMap hA g),
        IsFiniteType B S hS (formalSpectrumMap hA g),
        TopologicalRing.FiniteTypeModuloEveryWeakIdeal g.toRingHom,
        RingHom.IsTaut g.toRingHom ∧
          TopologicalRing.IsTopologicallyOfFiniteType g.toRingHom] := by
  have h0ANU :=
    TopologicalRing.finiteType_tfae g.toRingHom hA hC hAcount
  tfae_have 1 → 2 := fun h ↦ hqc _ hsrc htgt h
  tfae_have 2 → 3 := fun h ↦
    have htaut : RingHom.IsTaut g.toRingHom :=
      isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap B S hS hA hC _ _
        (QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS D hA hAcount)
        (QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS E hC hCcount) g h.1
    ⟨htaut, fun J hJ ↦
      finiteType_quotientMap_of_isFiniteType_formalSpectrumMap hA hC D E g htaut h J hJ⟩
  tfae_have 3 → 4 := fun h ↦ (h0ANU.out 1 3).mp h
  tfae_have 4 → 3 := fun h ↦ (h0ANU.out 3 1).mp h
  tfae_have 3 → 1 := fun h ↦ h0ANT hA D E g h
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
