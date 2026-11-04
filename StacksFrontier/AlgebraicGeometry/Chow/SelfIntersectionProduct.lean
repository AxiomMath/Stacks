module

public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport

/-!
# The intersection product on the Chow groups of a single scheme

Let `W` be a scheme locally of finite type over the base whose diagonal `Δ : W ⟶ W ×_k W` carries
a Gysin class `Δ^!` of degree `D`; for `W` smooth of dimension `D` over a field this is the class
of Stacks 0FBR. Taking `Y = Z = W` over `X = W` in the intersection product of Stacks 0FC0 gives a
product `CH_n(W) × CH_m(W) ⟶ CH_{n+m-D}(W ×_W W)`, and `W ×_W W ≅ W` through the first
projection. This file records that product as a `ℤ`-bilinear map on the Chow groups of `W`
itself.

## Main definitions

* `Stacks.Chow.selfIntersectionProduct`: the product `α · β ∈ CH_{n+m-D}(W)` of
  `α ∈ CH_n(W)` and `β ∈ CH_m(W)`.

## Implementation notes

The Gysin class of the diagonal is an argument, exactly as in `Stacks.Chow.intersectionProduct`:
the product is defined for whichever class is supplied. The identification `W ×_W W ≅ W` is
pushforward along the isomorphism `pullback.fst (𝟙 W) (𝟙 W)`, which needs no instance of
Stacks 02S2 (`Stacks.Chow.chowPushforwardOfIso`).

## References

* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section SelfIntersection

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (D : ℤ)
  (Dc : BivariantClass C G sW (selfProductStructure C sW) (pullback.diagonal sW)
    (diagonal_comp_selfProductStructure C sW) D)

omit [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S] [LocallyOfFiniteType sW] in
/-- The composites of the first projection `W ×_W W ⟶ W` with `sW` and with `𝟙 W ≫ sW`
agree. -/
theorem pullback_fst_id_comp_base :
    pullback.fst (𝟙 W) (𝟙 W) ≫ sW = pullback.fst (𝟙 W) (𝟙 W) ≫ (𝟙 W ≫ sW) := by
  rw [Category.id_comp]

/-- The intersection product `CH_n(W) × CH_m(W) ⟶ CH_{n+m-D}(W)` on a single scheme `W` whose
diagonal carries the Gysin class `Dc` of degree `D`: the product of Stacks 0FC0 for `Y = Z = W`
over `X = W`, read on `W` through the identification `W ×_W W ≅ W`. -/
def selfIntersectionProduct (n m : ℤ) :
    chowGroup C sW n →ₗ[ℤ] chowGroup C sW m →ₗ[ℤ] chowGroup C sW (n + m - D) :=
  ((intersectionProductBilin C hδ G sW (𝟙 W) (𝟙 W) D Dc n m).compl₁₂
      (chowGroupCongr C (Category.id_comp sW).symm n).toIntLinearEquiv.toLinearMap
      (chowGroupCongr C (Category.id_comp sW).symm m).toIntLinearEquiv.toLinearMap).compr₂
    (chowPushforwardOfIso C (pullback.fst (𝟙 W) (𝟙 W) ≫ (𝟙 W ≫ sW)) sW
      (pullback.fst (𝟙 W) (𝟙 W)) (pullback_fst_id_comp_base C sW).symm
      (n + m - D)).toIntLinearMap

end SelfIntersection

end Stacks.Chow

end
