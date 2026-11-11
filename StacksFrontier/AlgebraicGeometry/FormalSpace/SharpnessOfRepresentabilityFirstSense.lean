module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SharpnessOfRepresentability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful

/-!
# The first sense of Stacks 0AN7, with no hypothesis

**Stacks 0AN7**, in its first sense, says that the formal spectrum of a continuous homomorphism
of weakly admissible topological rings need not be representable by algebraic spaces; the
example is the inclusion of constants `k → k⟦t⟧`, for `k` a discrete field and `k⟦t⟧` carrying
the `t`-adic topology, which is not taut,
`TopologicalRing.not_isTaut_constantsToTAdicPowerSeries`. That a non-taut homomorphism has a
non-representable formal spectrum is the implication (1) ⟹ (3) of **Stacks 0AN5**, which
`AlgebraicGeometry.FormalSpace.not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants`
of `StacksFrontier/AlgebraicGeometry/FormalSpace/SharpnessOfRepresentability.lean` takes as the
hypothesis `h0AN5`, at every pair of weakly admissible rings.

This file discharges it at the example. The implication (1) ⟹ (3) is
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`,
which asks for the set-theoretic condition of Stacks 0AIS on both quotient systems. Both rings
of the example carry a countable fundamental system of neighbourhoods of `0` — the discrete one
trivially, the `t`-adic one by the powers of `(t)` — and that condition follows from it by
`AlgebraicGeometry.FormalSpace.QuotientSystem.hasLargeSite_of_isCountablyGenerated`.

## Main results

* `TopologicalRing.isCountablyGenerated_nhds_zero_tAdicPowerSeries`: the powers of `(t)` are a
  countable fundamental system of neighbourhoods of `0` in `k⟦t⟧`.
* `FormalSpace.not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants'`: the formal
  spectrum of the homomorphism of the example is not representable by algebraic spaces. It is
  the non-representability by algebraic spaces in
  `AlgebraicGeometry.FormalSpace.exists_formalSpectrumMap_constants_not_representable`,
  **Stacks 0AN7 (1)**.

## References

* [Stacks Project, Tag 0AN7](https://stacks.math.columbia.edu/tag/0AN7)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
-/

@[expose] public section

namespace TopologicalRing

universe u

/-- The powers of `(t)` are a countable fundamental system of neighbourhoods of `0` in `k⟦t⟧`
with the `t`-adic topology. -/
theorem isCountablyGenerated_nhds_zero_tAdicPowerSeries (k : Type u) [CommRing k] :
    (nhds (0 : TAdicPowerSeries k)).IsCountablyGenerated :=
  (WithIdeal.i : Ideal (TAdicPowerSeries k)).hasBasis_nhds_zero_adic.isCountablyGenerated

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

open CategoryTheory

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The non-representability of the first sense of **Stacks 0AN7**. Let `k` be a field with the discrete topology, let `k⟦t⟧`
carry the `t`-adic topology, and let `Spf (φ) : Spf k⟦t⟧ ⟶ Spf k` be the formal spectrum of the
inclusion of constants, taken over any base and any quotient systems presenting the two formal
spectra. Then `Spf (φ)` is not representable by algebraic spaces: by the implication (1) ⟹ (3)
of Stacks 0AN5 it would be taut, and the inclusion of constants is not. Both rings are weakly
admissible, by `TopologicalRing.isWeaklyAdmissible_discreteTopology` and
`TopologicalRing.isWeaklyAdmissible_tAdicPowerSeries`, and both carry a countable fundamental
system of neighbourhoods of `0` — the discrete one trivially, the `t`-adic one by the powers of
`(t)` — which is what gives the two quotient systems the set-theoretic condition that the
implication (1) ⟹ (3) asks for. This is
`AlgebraicGeometry.FormalSpace.not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants`
with its hypothesis `h0AN5` discharged at the two quotient systems of the example. -/
theorem not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants'
    (k : Type u) [Field k] [TopologicalSpace k] [DiscreteTopology k]
    (D : QuotientSystem B S hS k)
    (E : QuotientSystem B S hS (TopologicalRing.TAdicPowerSeries k))
    (f : ContinuousHom D E)
    (hf : f.toRingHom = TopologicalRing.constantsToTAdicPowerSeries k) :
    ¬ Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap (TopologicalRing.isWeaklyAdmissible_discreteTopology k) f).hom := by
  intro hrep
  refine TopologicalRing.not_isTaut_constantsToTAdicPowerSeries k (hf ▸ ?_)
  exact isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap B S hS
    (TopologicalRing.isWeaklyAdmissible_discreteTopology k)
    (TopologicalRing.isWeaklyAdmissible_tAdicPowerSeries k) D E
    (QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS D
      (TopologicalRing.isWeaklyAdmissible_discreteTopology k) (by
        rw [nhds_discrete]
        exact Filter.isCountablyGenerated_pure 0))
    (QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS E
      (TopologicalRing.isWeaklyAdmissible_tAdicPowerSeries k)
      (TopologicalRing.isCountablyGenerated_nhds_zero_tAdicPowerSeries k)) f hrep

end AlgebraicGeometry.FormalSpace

end
