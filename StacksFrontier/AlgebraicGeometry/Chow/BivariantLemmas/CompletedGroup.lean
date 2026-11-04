module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents
public import Mathlib.Algebra.DirectSum.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The completed bivariant Chow group

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`. Both `X` and `Y` are then locally
Noetherian, so they decompose into their connected components, `X = ∐_{i ∈ I} X_i` and
`Y = ∐_{j ∈ J} Y_j`, and `f` carries `X_i` into a single `Y_{a(i)}`. The decomposition theorem
of Stacks 0FDZ gives `A^p(X ⟶ Y) = ∏_i A^p(X_i ⟶ Y_{a(i)})`, and the Stacks Project uses that
to define the *completed* bivariant group

  `A^*(X ⟶ Y)^∧ = ∏_i A^*(X_i ⟶ Y_{a(i)})`,

the elements of which are the families `c = (c_0, c_1, c_2, …)` whose image in
`A^p(X_i ⟶ Y_{a(i)})` vanishes for almost all `p`, *for each connected component separately*.
It is in general strictly larger than the direct sum `⊕_p A^p(X ⟶ Y)`, because no bound on the
degree is required uniformly over the components.

## Main definitions

* `Stacks.Chow.completedBivariantGroup` — the group `A^*(X ⟶ Y)^∧`, Stacks 0FE0.

## Implementation notes

The "almost all `p`" condition on each component is exactly what `DirectSum ℤ` records, so the
group is the product over `i : ConnectedComponents X` of `DirectSum ℤ` of the bivariant groups
of the restricted morphism `AlgebraicGeometry.Scheme.Hom.resConnectedComponent`. Written this
way it is an abbreviation, so the pointwise abelian group structure on
`Stacks.Chow.BivariantClass` propagates to it through the `DirectSum` and `Pi` instances with
no further declaration.

Local Noetherianity of the source and target — which is what makes the connected components
open, Stacks 01OZ and Stacks 04MF — is not assumed: it follows from local finite type over the
base, and is supplied by `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`.

The development is stated against a `Stacks.Chow.GysinSystem`, the parameter
`Stacks.Chow.BivariantClass` carries; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic`.

## References

* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 01OZ](https://stacks.math.columbia.edu/tag/01OZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Stacks 0FE0.** The completed bivariant group `A^*(X ⟶ Y)^∧` of a morphism `f : X ⟶ Y` of
schemes locally of finite type over the base: the product, over the connected components `X_i`
of `X`, of the graded groups `A^*(X_i ⟶ Y_{a(i)})` of bivariant classes for the restriction of
`f` to `X_i` and the connected component of `Y` it lands in. The degree support is finite on
each component but need not be bounded across components. -/
@[stacks 0FE0 "completed_bivariant_group"]
abbrev completedBivariantGroup (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) : Type (u + 1) :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  ∀ i : ConnectedComponents X,
    DirectSum ℤ fun p ↦
      BivariantClass C G ((X.connectedComponentOpens i).ι ≫ sX)
        ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap i)).ι ≫ sY)
        (f.resConnectedComponent i) (f.resConnectedComponent_comp_ι_comp hf i) p

end Stacks.Chow

end
