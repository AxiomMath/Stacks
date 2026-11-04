module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Setup
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IntegralClosedSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableImpliesFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms

/-!
# Integral good algebraic spaces

A good algebraic space over the fixed base of the theory of cycles is decent. Consequently it
is integral exactly when it is reduced and its space of points is irreducible — decency, the
third condition in the definition of an integral algebraic space, is automatic — and every
point of it is the generic point of the set of points of exactly one integral closed subspace.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isDecentSpace_of_isGood`: a good algebraic space over the fixed
  base is decent.
* `AlgebraicGeometry.Space.isIntegralSpace_iff_isReduced_and_irreducibleSpace_of_isGood`:
  **Stacks 0EDV**, integrality of a good algebraic space is reducedness together with
  irreducibility of its space of points.
* `AlgebraicGeometry.Space.existsUnique_integralClosedSubspace_isGenericPoint_of_isGood`:
  **Stacks 0EDV**, each point of a good algebraic space is the generic point of the set of
  points of a unique integral closed subspace.

## Implementation notes

Decency is reached along the implications of Stacks 03JX. The structure morphism of a good
space is quasi-separated and the base of the situation is quasi-separated, so the space itself
is quasi-separated by Stacks 04ZH part (2); that is condition `(η)`, and `(η) ⇒ (ζ) ⇒ (ε) ⇒
(δ) ⇒ (γ)` passes through Zariski local quasi-separatedness, very reasonableness and
reasonableness. Condition `(γ)` is condition (1) of Stacks 03JV, which is equivalent to
condition (4), the definition of decency used in this repository.

The second assertion needs no soberness of the space of points. Taking the set of points is a
bijection from the integral closed subspaces of a decent algebraic space onto the irreducible
closed subsets of its space of points, which is Stacks 0ENF and is proved there
unconditionally; the closure of a point is such an irreducible closed subset, and the subspace
the bijection returns for it is the asserted one, since `IsGenericPoint ξ T` is the equality
`closure {ξ} = T`.

## References

* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDV](https://stacks.math.columbia.edu/tag/0EDV)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A good algebraic space over the fixed base is decent: it is quasi-separated, hence Zariski
locally quasi-separated, very reasonable, reasonable, and finally has finite chart and relation
fibres above every point, which is decency. -/
theorem isDecentSpace_of_isGood (f : X ⟶ D.space) (hf : D.IsGood f) :
    IsDecentSpace D.site D.base D.base_mem X :=
  (isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint D.site D.base D.base_mem X
    hf.1).2
    (hasFiniteChartAndRelationFibersAtEveryPoint_of_isReasonableSpace D.site D.base D.base_mem X
      hf.1
      (isReasonableSpace_of_isVeryReasonableSpace D.site D.base D.base_mem X hf.1
        (isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated D.site D.base
          D.base_mem D.terminal_mem X hf.1
          (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated D.site D.base
            D.base_mem X D.terminal_mem hf.1
            (isAbsolutelyQuasiSeparated_of_isQuasiSeparated D.site D.base D.base_mem
              D.terminal_mem hf.1 D.quasiSeparated hf.2.1)))))

/-- **Stacks 0EDV.** A good algebraic space over the fixed base is integral exactly when it is
reduced and its space of points is irreducible: the third condition of integrality, decency,
holds for every good algebraic space. -/
@[stacks 0EDV "integral iff reduced and irreducible"]
theorem isIntegralSpace_iff_isReduced_and_irreducibleSpace_of_isGood (f : X ⟶ D.space)
    (hf : D.IsGood f) :
    IsIntegralSpace D.site D.base D.base_mem X ↔
      HasEtaleLocalProperty D.site D.base D.base_mem X (fun Y : Scheme.{u} => IsReduced Y) ∧
        IrreducibleSpace (points D.site D.base D.base_mem X) :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, isDecentSpace_of_isGood D f hf, h.2⟩⟩

/-- **Stacks 0EDV.** Every point of a good algebraic space over the fixed base is the generic
point of the set of points of exactly one integral closed subspace. -/
@[stacks 0EDV "unique integral closed subspace with a given generic point"]
theorem existsUnique_integralClosedSubspace_isGenericPoint_of_isGood (f : X ⟶ D.space)
    (hf : D.IsGood f) (ξ : points D.site D.base D.base_mem X) :
    ∃! Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      IsGenericPoint ξ
        (Set.range (pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι)) := by
  have hbij := bijective_integralClosedSubspaceSupport D.site D.base D.base_mem (X := X) hf.1
    (isDecentSpace_of_isGood D f hf)
  obtain ⟨Z, hZ⟩ := hbij.2 (IrreducibleCloseds.closureSingleton ξ)
  have hZset := congrArg IrreducibleCloseds.carrier hZ
  change Set.range (pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι) =
    closure ({ξ} : Set (points D.site D.base D.base_mem X)) at hZset
  exact ⟨Z, hZset.symm, fun W hW => hbij.1 (IrreducibleCloseds.ext (hW.def.symm.trans hZset.symm))⟩

end AlgebraicGeometry.Space

end
