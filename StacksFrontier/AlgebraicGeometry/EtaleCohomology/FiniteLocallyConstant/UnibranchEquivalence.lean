module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.EtaleLocalRepresentability
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.UnibranchContinuousModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.RingTheory.Branches.Defs

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists

/-!
# Stacks Tag 0GIY: locally constant module sheaves on a geometrically unibranch scheme

Let `X` be an irreducible, geometrically unibranch scheme, let `x` be a geometric point of `X` and
let `Λ` be a ring. The finite type locally constant sheaves of `Λ`-modules on `X_étale` are
equivalent to the finite `Λ`-modules endowed with a continuous `π₁(X, x)`-action.

## Main results

* `AlgebraicGeometry.finiteTypeLocallyConstantEquivContinuousModuleUniv` — **Tag 0GIY**.

## Implementation notes

The source reduces to an integral normal scheme along the normalization and argues at the generic
point. The proof here is direct and avoids the normalization, the topological invariance of the
étale site and the comparison of fundamental groups along universal homeomorphisms.

* Every étale `X`-scheme is locally irreducible, `X` being irreducible and geometrically unibranch
  (`AlgebraicGeometry.exists_isOpen_isPreirreducible_of_etale_of_isGeometricallyUnibranch`).
* A finite type locally constant sheaf `F` is trivialized by a pointed Galois cover of `X`
  (`AlgebraicGeometry.trivializedByPointedGaloisCovers`). The trivializations of `F` that agree,
  over irreducible objects, with a fixed trivialization over an affine étale `U₀` up to the finite
  set of monodromy automorphisms of `U₀ ×_X U₀` form a finite locally constant sheaf of sets.
  Tag 03RV represents it by a finite étale cover, and a Galois object dominating that cover
  trivializes `F`.
* On sheaves trivialized by pointed Galois covers, the functor sending `F` to the colimit of
  `F(A)` over the pointed Galois covers `(A, a)`, with `π₁` acting through the automorphisms
  `τ_A(σ)` (`AlgebraicGeometry.monodromyModule`), is fully faithful, by Galois descent along the
  covers. Every finite continuous module is reached, through the descent sheaf of equivariant
  locally constant maps (`AlgebraicGeometry.EtaleGaloisCovering.descentSheaf`) along a pointed
  Galois cover whose stabilizer acts trivially on it
  (`AlgebraicGeometry.monodromyFTLCEquivalence`).

The small étale site is Mathlib's, `X.smallEtaleTopology`, and the sheaves take values in
`ModuleCat.{max (u + 1) r} Λ`. The geometric point is arbitrary and `Λ` is an arbitrary ring; no
Noetherian or finiteness hypothesis on `X` is made.

## References

* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u r

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0GIY.** Let `X` be an irreducible, geometrically unibranch scheme, let
`x` be a geometric point of `X` and let `Λ` be a ring. The finite type locally constant sheaves of
`Λ`-modules on `X_étale` are equivalent to the finite `Λ`-modules endowed with a continuous
`π₁(X, x)`-action.

The functor sends a sheaf `F` to its monodromy module `colim_{(A, a)} F(A)` over the pointed
Galois covers of `X`. -/
@[stacks 0GIY]
public def finiteTypeLocallyConstantEquivContinuousModuleUniv (X : Scheme.{u}) [IrreducibleSpace X]
    (hX : IsGeometricallyUnibranch X) (x : GeometricPoint X) (Λ : Type r) [Ring Λ] :
    Stacks.ConstantSheaf.FiniteTypeLocallyConstantModuleCategory.{max (u + 1) r, u + 1, u, r} Λ
        X.smallEtaleTopology ≌
      Stacks.GroupCohomology.FiniteTypeContinuousModule.{r, u + 1, max (u + 1) r} Λ
        (EtaleFundamentalGroup X x) :=
  monodromyFTLCEquivalence hX (trivializedByPointedGaloisCovers hX x Λ)

end AlgebraicGeometry

end
