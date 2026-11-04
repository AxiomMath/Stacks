module

public import StacksFrontier.AlgebraicGeometry.Chow.Codimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.CohenMacaulayBase
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Dimension.DimensionFunctionDifference

/-!
# Cohen--Macaulay schemes are locally equidimensional over a Chow base

Let `X` be locally of finite type over the base scheme of a Chow situation and let `δ_{X/S}` be
the propagated dimension function. If `X` is Cohen--Macaulay then `δ_{X/S}` satisfies the three
equivalent conditions of Stacks 0FE3.

The reason is that a Cohen--Macaulay scheme carries a second dimension function, the negative of
the dimension of the local ring, which vanishes at the generic point of every irreducible
component. The difference of two dimension functions on a locally Noetherian sober space is
locally constant, so on a neighbourhood of any point the value of `δ_{X/S}` at a generic point of
a component through that point is determined, independently of the component.

## Main results

* `Stacks.Chow.IsLocallyEquidimensional.of_isCohenMacaulay`,
  `Stacks.Chow.HasDimensionDecomposition.of_isCohenMacaulay`,
  `Stacks.Chow.IsLocallyPureDimensional.of_isCohenMacaulay` — the three conditions of
  Stacks 0FE3 for the relative dimension function of a Cohen--Macaulay scheme.

## References

* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Stacks 0FE3.** The relative dimension function of a Cohen--Macaulay scheme locally of
finite type over the base of a Chow situation is locally equidimensional: at each point, all
irreducible components through it have the same relative dimension at their generic points. -/
@[stacks 0FE3 "cohen_macaulay_case"]
theorem IsLocallyEquidimensional.of_isCohenMacaulay (B : ChowSituation.{u}) (X : Scheme.{u})
    (f : X ⟶ B.S) [LocallyOfFiniteType f] (hX : IsCohenMacaulay X) :
    IsLocallyEquidimensional (relativeDimension B.dimensionFunction f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction B.isUniversallyCatenary B.dimensionFunction f
  obtain ⟨d', hd'⟩ := IsCohenMacaulay.negativeLocalRingDimension_isDimensionFunction hX
  intro x
  obtain ⟨U, hU, hxU, hconst⟩ :=
    (DimensionFunction.isLocallyConstant_sub
      (isLocallyNoetherianSpace_of_isLocallyNoetherian X) d d').exists_open x
  refine ⟨d x - d' x, fun C hC hxC ξ hξ ↦ ?_⟩
  have hξU : ξ ∈ U := (hξ.mem_open_set_iff hU).2 ⟨x, hxC, hxU⟩
  have hgen : ξ ∈ genericPoints X := by
    change closure ({ξ} : Set X) ∈ irreducibleComponents X
    rw [hξ.def]
    exact hC
  have hnegξ : negativeLocalRingDimension X ξ = 0 := by
    simp [negativeLocalRingDimension, ringKrullDim_stalk_eq_zero_of_mem_genericPoints X ξ hgen]
  simpa only [hd ξ, hd' ξ, hnegξ, sub_zero] using hconst ξ hξU

/-- **Stacks 0FE3.** A Cohen--Macaulay scheme locally of finite type over the base of a Chow
situation decomposes into open and closed subschemes of constant relative dimension. -/
@[stacks 0FE3 "cohen_macaulay_case"]
theorem HasDimensionDecomposition.of_isCohenMacaulay (B : ChowSituation.{u}) (X : Scheme.{u})
    (f : X ⟶ B.S) [LocallyOfFiniteType f] (hX : IsCohenMacaulay X) :
    HasDimensionDecomposition (relativeDimension B.dimensionFunction f) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  .of_isLocallyEquidimensional (.of_isCohenMacaulay B X f hX)

/-- **Stacks 0FE3.** The relative dimension function of a Cohen--Macaulay scheme locally of
finite type over the base of a Chow situation is locally pure dimensional. -/
@[stacks 0FE3 "cohen_macaulay_case"]
theorem IsLocallyPureDimensional.of_isCohenMacaulay (B : ChowSituation.{u}) (X : Scheme.{u})
    (f : X ⟶ B.S) [LocallyOfFiniteType f] (hX : IsCohenMacaulay X) :
    IsLocallyPureDimensional (relativeDimension B.dimensionFunction f) :=
  .of_hasDimensionDecomposition (.of_isCohenMacaulay B X f hX)

end Stacks.Chow

end
