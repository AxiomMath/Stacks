module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProduct

/-!
# The intersection product formed with the Gysin class of a virtual normal bundle of the diagonal

The intersection product `α · β = Δ^!(α × β)` of Stacks 0FC0 (`Stacks.Chow.intersectionProduct`)
is formed with a bivariant class `Δ^! ∈ A^d(X ⟶ X ×_k X)` of the diagonal. For a separated `X`
and a virtual normal bundle `𝒩` of constant rank `r` for the diagonal, Stacks 0FBK gives the class
`c(X ⟶ X ×_k X, 𝒩) ∈ A^r(X ⟶ X ×_k X)` (`Stacks.Chow.virtualNormalBundleClass`), and the
intersection product formed with it has degree `r`. For `X` smooth over the base the diagonal is a
regular immersion (`Stacks.Chow.isRegularImmersion_diagonal_of_smooth`), and its virtual normal
bundle is the conormal bundle, of rank the relative dimension.

## Main definitions

* `Stacks.Chow.diagonalVirtualNormalBundleClass`: the class
  `c(X ⟶ X ×_k X, 𝒩) ∈ A^r(X ⟶ X ×_k X)`.
* `Stacks.Chow.intersectionProductOfVirtualNormalBundleClass`: the intersection product
  `α · β = Δ^!(α × β)` of Stacks 0FC0 formed with it.

## References

* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section VirtualNormalBundle

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsSeparated sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]
  (𝒩 : VirtualNormalBundle (pullback.diagonal sX)) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- The Gysin class `c(X ⟶ X ×_k X, 𝒩) ∈ A^r(X ⟶ X ×_k X)` of the diagonal of a separated `X`
attached by Stacks 0FBK to a virtual normal bundle `𝒩` of constant rank `r` for the diagonal.
For `X` smooth over the base the diagonal is a regular immersion by
`Stacks.Chow.isRegularImmersion_diagonal_of_smooth`, and its virtual normal bundle is the
conormal bundle, of rank the relative dimension. -/
def diagonalVirtualNormalBundleClass :
    BivariantClass C (gysinSystemOfInvertible C) sX (selfProductStructure C sX)
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) (r : ℤ) :=
  virtualNormalBundleClass C sX (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) 𝒩 r

/-- The product `α · β = c(X ⟶ X ×_k X, 𝒩)(α × β)` formed with the class of Stacks 0FBK of a
virtual normal bundle `𝒩` of the diagonal, given as an argument; its degree is the rank `r` of
`𝒩`. The intersection product of Stacks 0FC0, formed with the Gysin map of the diagonal of a
smooth `X` of Stacks 0FBR and with no bundle as an argument, is
`Stacks.Chow.smoothIntersectionProduct`. -/
def intersectionProductOfVirtualNormalBundleClass (n m : ℤ) :
    TensorProduct ℤ (chowGroup C (a ≫ sX) n) (chowGroup C (b ≫ sX) m) →+
      chowGroup C (pullback.fst a b ≫ (a ≫ sX)) (n + m - (r : ℤ)) :=
  intersectionProduct C hδ (gysinSystemOfInvertible C) sX a b (r : ℤ)
    (diagonalVirtualNormalBundleClass C sX 𝒩 r) n m

end VirtualNormalBundle

end Stacks.Chow

end
