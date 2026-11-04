module

public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization

/-!
# A normal surface has a dualizing module as soon as it has a dualizing complex

On an integral Noetherian normal scheme of dimension at most two, a dualizing complex is
automatically a coherent module placed in a single degree. Such a scheme is Cohen--Macaulay
([Stacks, Tag 0B3D]) and connected, so the final assertion of [Stacks, Tag 0AWT] concentrates its
dualizing complex; the converse is immediate from the definition of a dualizing module. The two
conditions (1) and (2) of [Stacks, Remark 0B4R] are therefore equivalent.

## Main results

* `Stacks.Duality.exists_isDualizingComplex_iff_exists_isDualizingModule` —
  **[Stacks, Remark 0B4R], the equivalence of (1) and (2)**: an integral Noetherian normal scheme
  of dimension at most two has a dualizing complex if and only if it has a dualizing module.

## Implementation notes

`Stacks.Duality.IsDualizingModule` pins the derived category to `HasDerivedCategory.standard`, so
the existence statement about dualizing complexes is read at that same model, by the local
instance below.

Connectedness comes from integrality through `AlgebraicGeometry.irreducibleSpace_of_isIntegral`
and `IrreducibleSpace.connectedSpace`, so it is not a hypothesis. The dimension hypothesis is
`TopologicalSpace.topologicalKrullDim`, which bounds the Krull dimension of every local ring; it
is an inequality, which covers the dimension-two case of the source.

The remark's two remaining assertions are not here. That a normal modification of `Spec(A)`
inherits a dualizing module needs [Stacks, Tag 0AWI], that `f^!ω_Y^•` is a dualizing complex for
a finite-type separated `f`, which this development does not have; the normalization of `ω_X`
relative to `ω_A` is
`AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization`.

## References

* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0AWT](https://stacks.math.columbia.edu/tag/0AWT)
* [Stacks Project, Tag 0B3D](https://stacks.math.columbia.edu/tag/0B3D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- **Stacks Project, Remark 0B4R, the equivalence of (1) and (2).** An integral Noetherian
normal scheme of dimension at most two carries a dualizing complex if and only if it carries a
dualizing module, that is a coherent module which is a dualizing complex in some degree. -/
@[stacks 0B4R "the equivalence of (1) and (2)"]
public theorem exists_isDualizingComplex_iff_exists_isDualizingModule (X : Scheme.{u})
    [IsIntegral X] [IsNoetherian X] [IsNormal X] (hX : topologicalKrullDim X ≤ 2) :
    (∃ K : DerivedCategory X.Modules, IsDualizingComplex K) ↔
      ∃ ω : X.Modules, IsDualizingModule ω := by
  constructor
  · rintro ⟨K, hK⟩
    obtain ⟨n, hcoh, -, ⟨e⟩⟩ := exists_coherent_cohenMacaulay_iso_single_of_connected K hK
      (isCohenMacaulay_of_isNormal_of_topologicalKrullDim_le_two X hX)
    exact ⟨_, hcoh, n, isDualizingComplex_of_iso e hK⟩
  · rintro ⟨ω, -, n, hn⟩
    exact ⟨_, hn⟩

end Stacks.Duality

end
