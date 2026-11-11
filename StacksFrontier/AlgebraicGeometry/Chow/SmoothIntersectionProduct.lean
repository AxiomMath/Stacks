module

public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionPart
public import StacksCore.Tactic.StacksAttribute

/-!
# The intersection product on the Chow groups of schemes over a smooth scheme

Let `X` be smooth over a field `k` and let `Y ⟶ X`, `Z ⟶ X` be locally of finite type. The
diagonal `Δ : X ⟶ X ×_k X` is a regular immersion, so it has the Gysin map `Δ^!` of Stacks 0FBR,
and Stacks 0FC0 defines the intersection product

`α · β = Δ^!(α × β) ∈ CH_*(Y ×_X Z)`   for `α ∈ CH_n(Y)`, `β ∈ CH_m(Z)`,

through `Y ×_X Z = (Y ×_k Z) ×_{X ×_k X, Δ} X`. If `X` is equidimensional of dimension `d` the
product lands in `CH_{n+m-d}(Y ×_X Z)`; in general it decomposes into the parts lying over the
open and closed subschemes of `X` on which `X` has a given dimension.

This file forms that product with the Gysin class of the diagonal itself,
`Stacks.Chow.diagonalGysinClass` of Stacks 0FBR (the class `c(X ⟶ X ×_k X, 𝒩)` of the normal
bundle of the diagonal, Stacks 0FEZ and 0FBK), so that, unlike `Stacks.Chow.intersectionProduct`,
no bivariant class is a parameter.

## Main definitions

* `Stacks.Chow.smoothDiagonalGysinClass`: `Δ^! ∈ A^d(X ⟶ X ×_k X)` for `X` smooth of relative
  dimension `d`, with its source over the base through the structure morphism of `X`.
* `Stacks.Chow.smoothIntersectionProduct`: the product
  `CH_n(Y) ⊗ CH_m(Z) ⟶ CH_{n+m-d}(Y ×_X Z)` for `X` smooth of relative dimension `d`.
* `Stacks.Chow.smoothIntersectionProductBilin`: the same product as a bilinear map.
* `Stacks.Chow.smoothIntersectionProductParts`: the product for `X` smooth of arbitrary,
  not necessarily constant, dimension, as the family over `d` of its parts
  `CH_{n+m-d}(Y_d ×_{X_d} Z_d)` over the open and closed parts `X_d` of `X` of dimension `d`.

## Implementation notes

The base is the `Stacks.Chow.ChowSituation` of `Stacks.Chow.intersectionProduct`, with the side
conditions its exterior product asks for (`Subsingleton`, `IsIntegral` and `JacobsonSpace` on the
base and `hδ`), all of which hold for `Spec k` with `δ = 0`, the situation of the source.

## References

* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase)

section Equidimensional

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Smooth sX] {d : ℕ}
  (hd : RelativeDimension sX d)
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]

/-- **The Gysin class `Δ^! ∈ A^d(X ⟶ X ×_k X)` of the diagonal** of `X` smooth over the base of
relative dimension `d` (Stacks 0FBR, `Stacks.Chow.diagonalGysinClass`), read with its source over
the base through the structure morphism of `X`, which is the form the intersection product
`Stacks.Chow.intersectionProduct` consumes. -/
abbrev smoothDiagonalGysinClass :
    BivariantClass C (gysinSystemOfInvertible C) sX (selfProductStructure C sX)
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) (d : ℤ) :=
  bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) rfl (d : ℤ) (diagonalGysinClass C sX sX hd)

/-- **Stacks Project, Tag 0FC0.** The intersection product

`· : CH_n(Y) ⊗_ℤ CH_m(Z) ⟶ CH_{n+m-d}(Y ×_X Z)`,   `α · β = Δ^!(α × β)`,

for `X` smooth over the base of relative dimension `d` (equidimensional of dimension `d`) and
`Y ⟶ X`, `Z ⟶ X` locally of finite type: the exterior product of Stacks 0FBV followed by the
Gysin map `Δ^!` of the diagonal of Stacks 0FBR (`Stacks.Chow.diagonalGysinClass`), read on
`Y ×_X Z = (Y ×_k Z) ×_{X ×_k X} X`. No bivariant class is a parameter. -/
@[stacks 0FC0 "X equidimensional of dimension d: α · β = Δ^!(α × β) in CH_{n+m-d}(Y ×_X Z), with \
Δ^! the Gysin map of the diagonal of Stacks 0FBR, Stacks.Chow.diagonalGysinClass, and × the \
exterior product of Stacks 0FBV"]
def smoothIntersectionProduct (n m : ℤ) :
    TensorProduct ℤ (chowGroup C (a ≫ sX) n) (chowGroup C (b ≫ sX) m) →+
      chowGroup C (pullback.fst a b ≫ (a ≫ sX)) (n + m - d) :=
  intersectionProduct C hδ (gysinSystemOfInvertible C) sX a b (d : ℤ)
    (smoothDiagonalGysinClass C sX hd) n m

/-- **Stacks Project, Tag 0FC0.** The defining formula `α · β = Δ^!(α × β)` of
`Stacks.Chow.smoothIntersectionProduct`: it is `Stacks.Chow.intersectionProduct` at the Gysin
class of the diagonal. -/
@[stacks 0FC0 "the defining formula α · β = Δ^!(α × β), with Δ^! the Gysin map of the diagonal"]
theorem smoothIntersectionProduct_apply (n m : ℤ)
    (t : TensorProduct ℤ (chowGroup C (a ≫ sX) n) (chowGroup C (b ≫ sX) m)) :
    smoothIntersectionProduct C hδ sX hd a b n m t =
      intersectionProduct C hδ (gysinSystemOfInvertible C) sX a b (d : ℤ)
        (smoothDiagonalGysinClass C sX hd) n m t :=
  rfl

/-- **Stacks Project, Tag 0FC0.** The intersection product as a `ℤ`-bilinear map
`CH_n(Y) → CH_m(Z) → CH_{n+m-d}(Y ×_X Z)`, `α ↦ β ↦ α · β`, for `X` smooth of relative
dimension `d`. -/
@[stacks 0FC0 "the product α ↦ β ↦ α · β as a bilinear map, X equidimensional of dimension d"]
def smoothIntersectionProductBilin (n m : ℤ) :
    chowGroup C (a ≫ sX) n →ₗ[ℤ] chowGroup C (b ≫ sX) m →ₗ[ℤ]
      chowGroup C (pullback.fst a b ≫ (a ≫ sX)) (n + m - d) :=
  TensorProduct.curry (smoothIntersectionProduct C hδ sX hd a b n m).toIntLinearMap

/-- The bilinear form of the product evaluates to the product on a pure tensor. -/
theorem smoothIntersectionProductBilin_apply (n m : ℤ) (α : chowGroup C (a ≫ sX) n)
    (β : chowGroup C (b ≫ sX) m) :
    smoothIntersectionProductBilin C hδ sX hd a b n m α β =
      smoothIntersectionProduct C hδ sX hd a b n m (TensorProduct.tmul ℤ α β) :=
  rfl

end Equidimensional

section Parts

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Smooth sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]

/-- **Stacks Project, Tag 0FC0, for `X` of arbitrary dimension.** Let `X` be smooth over the base,
not necessarily equidimensional, with open and closed parts `X_d` of relative dimension `d`
(`Stacks.WeilCohomology.dimPart`, Stacks 02NM), and let `Y_d = a⁻¹(X_d)`, `Z_d = b⁻¹(X_d)` be the
parts of `Y` and `Z` over `X_d`. The intersection product `α · β = Δ^!(α × β)` "decomposes into
the parts lying over the open and closed subschemes of `X` where `X` has a given dimension": its
part over `X_d` is

`α|_{Y_d} · β|_{Z_d} = Δ_d^!(α|_{Y_d} × β|_{Z_d}) ∈ CH_{n+m-d}(Y_d ×_{X_d} Z_d)`,

`Stacks.Chow.smoothIntersectionProduct` over `X_d` with the Gysin map of the diagonal of `X_d`
(Stacks 0FBR). The product is the family of these parts. No bivariant class is a parameter. -/
@[stacks 0FC0 "X smooth of arbitrary dimension: α · β = Δ^!(α × β) in CH_*(Y ×_X Z), as the \
family over d of its parts in CH_{n+m-d}(Y_d ×_{X_d} Z_d) over the open and closed parts X_d of X \
of dimension d, each formed with the Gysin map of the diagonal of Stacks 0FBR"]
def smoothIntersectionProductParts (n m : ℤ) :
    TensorProduct ℤ (chowGroup C (a ≫ sX) n) (chowGroup C (b ≫ sX) m) →+
      ∀ d : ℕ, chowGroup C
        (pullback.fst (dimPartOverHom sX a d) (dimPartOverHom sX b d) ≫
          (dimPartOverHom sX a d ≫ partBase sX d)) (n + m - d) :=
  AddMonoidHom.pi fun d ↦
    (smoothIntersectionProduct C hδ (partBase sX d) (relativeDimension_partBase sX d)
        (dimPartOverHom sX a d) (dimPartOverHom sX b d) n m).comp
      (TensorProduct.map (chowGroupDimPartOver C sX a d n).toIntLinearMap
        (chowGroupDimPartOver C sX b d m).toIntLinearMap).toAddMonoidHom

/-- The part over `X_d` of the product of `α` and `β` is the product of their restrictions to the
parts over `X_d`. -/
theorem smoothIntersectionProductParts_tmul (n m : ℤ) (α : chowGroup C (a ≫ sX) n)
    (β : chowGroup C (b ≫ sX) m) (d : ℕ) :
    smoothIntersectionProductParts C hδ sX a b n m (TensorProduct.tmul ℤ α β) d =
      smoothIntersectionProduct C hδ (partBase sX d) (relativeDimension_partBase sX d)
        (dimPartOverHom sX a d) (dimPartOverHom sX b d) n m
        (TensorProduct.tmul ℤ (chowGroupDimPartOver C sX a d n α)
          (chowGroupDimPartOver C sX b d m β)) :=
  rfl

end Parts

end Stacks.Chow

end
