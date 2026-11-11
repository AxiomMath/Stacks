module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClass
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksCore.Tactic.StacksAttribute

/-!
# The intersection product on the Chow groups of a smooth scheme

Let `X` be smooth over a field and let `Y` and `Z` be locally of finite type over `X`. The
diagonal `Δ : X ⟶ X ×_k X` is then a regular immersion, so it has a Gysin map
`Δ^! ∈ A^d(X ⟶ X ×_k X)`, and Stacks 0FC0 defines the intersection product

`α · β = Δ^!(α × β) ∈ CH_{n + m - d}(Y ×_X Z)` for `α ∈ CH_n(Y)` and `β ∈ CH_m(Z)`,

where `×` is the exterior product of Stacks 0FBV and the Gysin map is applied using the
identification `Y ×_X Z = (Y ×_k Z) ×_{X ×_k X} X` that the source itself uses.

That identification is `CategoryTheory.Limits.pullbackDiagonalMapIdIso`, and the product is
therefore built in two steps: `Stacks.Chow.diagonalGysinProduct` caps the exterior product with
the diagonal class, landing in the Chow group of `(Y ×_k Z) ×_{X ×_k X} X`, and
`Stacks.Chow.intersectionProduct` pushes that forward along the identification to land in the
Chow group of `Y ×_X Z`, which is where the source puts it.

## Main definitions

* `Stacks.Chow.selfProductStructure`: the structure morphism of `X ×_k X` over the base.
* `Stacks.Chow.exteriorToSelfProduct`: the morphism `Y ×_k Z ⟶ X ×_k X` along which the
  diagonal is pulled back, i.e. the test scheme the diagonal class is capped against.
* `Stacks.Chow.diagonalGysinProduct`: `Δ^!(α × β)`, in the Chow group of
  `(Y ×_k Z) ×_{X ×_k X} X`.
* `Stacks.Chow.intersectionProduct`: the intersection product `α · β` of Stacks 0FC0, in the
  Chow group of `Y ×_X Z`.
* `Stacks.Chow.intersectionProductBilin`: the same product as a `ℤ`-bilinear map
  `CH_n(Y) → CH_m(Z) → CH_{n+m-d}(Y ×_X Z)`, which is the shape the product is used in.
* `Stacks.Chow.diagonalVirtualNormalGysinClass`: the class of the diagonal produced by the
  construction of Stacks 0FBK from a virtual normal bundle datum and the construction's inputs.
* `Stacks.Chow.intersectionProductOfVirtualNormalBundle`: the intersection product formed with
  that class; it still takes the inputs of that construction as arguments.

The definitions here take the class `Δ^!` as an argument `c`. The intersection product of Stacks
0FC0 itself, formed with the Gysin map of the diagonal of Stacks 0FBR
(`Stacks.Chow.diagonalGysinClass`) and with no class as an argument, is
`Stacks.Chow.smoothIntersectionProduct` (for `X` equidimensional) and
`Stacks.Chow.smoothIntersectionProductParts` (for `X` of arbitrary dimension), in
`StacksFrontier.AlgebraicGeometry.Chow.SmoothIntersectionProduct`; this file cannot import
`StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinClass`, which depends on it.

## Main results

* `Stacks.Chow.diagonal_comp_selfProductStructure`: the diagonal is a morphism over the base.
* `Stacks.Chow.exteriorToSelfProduct_comp_selfProductStructure`: the test scheme of the product
  is `Y ×_k Z` with its own structure morphism, which is what makes capping the exterior product
  with the diagonal class type-check.
* `Stacks.Chow.pullbackDiagonalMapIdIso_hom_comp_structure`: the identification
  `(Y ×_k Z) ×_{X ×_k X} X ≅ Y ×_X Z` is a morphism over the base.
* `Stacks.Chow.intersectionProduct_apply` and
  `Stacks.Chow.intersectionProductBilin_apply`: the defining formula `α · β = Δ^!(α × β)`.

## Implementation notes

The base is kept a general `Stacks.Chow.ChowSituation` with the side conditions that the
exterior product of Stacks 0FBV already asks for — `Subsingleton`, `IsIntegral` and
`JacobsonSpace` on the base scheme, and the vanishing `hδ` of the dimension function on closed
points — rather than substituting `Spec k`, following
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree`. Smoothness of `X` over the base is
not itself a hypothesis of the definitions below: it enters only through the existence of the
Gysin class of the diagonal, which is the class that is carried, and
`Stacks.Chow.isRegularImmersion_diagonal_of_smooth` of
`StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysin` is what produces it from smoothness. Keeping
it out means the product is available in exactly the generality in which its defining class is.

Only the *definition* of the product is formalized here, together with the defining formula and
its bilinearity, which is free: the product is an additive map out of a tensor product by
construction. None of its properties is proved. The reason is that each of them needs a property
of the diagonal class that this repository does not have: associativity (Stacks 0FC1) needs the
base-change compatibility of Gysin maps of Stacks 0FBJ and the commutativity of composition of
bivariant classes of Stacks 0B77, and commutativity needs the symmetry of the exterior product
together with the compatibility of `Δ^!` with the swap of `X ×_k X`.

The degree `d` of the diagonal class is carried as an argument rather than computed from the
relative dimension of `X` over the base; for `X` smooth of constant relative dimension `d` the
class lives in `A^d(X ⟶ X ×_k X)`, which is Stacks 0FBR, but the dimension is not needed to
state the product and the completed class of Stacks 0FE0 would otherwise have to be truncated
first.

The class is carried as a `Stacks.Chow.BivariantClass` in the degree-`d` group
`A^d(X ⟶ X ×_k X)`. This is a single bivariant class attached to `X` alone: it does not mention
`Y`, `Z`, or any product operation, and the content of Stacks 0FC0 is precisely that capping it
against the exterior product is a product on Chow groups.
`Stacks.Chow.smoothIntersectionProduct` instantiates it at the Gysin class of the diagonal of
Stacks 0FBR, `Stacks.Chow.diagonalGysinClass`, which is the product of the source.

The instance of Stacks 02S2 that the pushforward of the product needs — proper pushforward
descending to Chow groups, bundled as `Stacks.Chow.ProperPushforwardDescends` — is *not* a
hypothesis of the definitions below: it is supplied by
`Stacks.Chow.properPushforwardDescends` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent`, which proves
that statement outright. Neither are the instances of Stacks 02S1 that the exterior product of
Stacks 0FBV asks for: they are supplied by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds` of
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence`, which deduces them from
the general case of Stacks 02S1,
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` of
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence`. This module
therefore carries only the Gysin class `c` of the diagonal.

## References

* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Diagonal

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]

/-- The structure morphism of `X ×_k X` over the base of the situation, the first projection
followed by the structure morphism of `X`. The diagonal is a morphism of schemes over the base
from `X` to this. -/
abbrev selfProductStructure : (pullback sX sX : Scheme.{u}) ⟶ C.S := pullback.fst sX sX ≫ sX

omit [LocallyOfFiniteType sX] in
/-- The diagonal `Δ : X ⟶ X ×_k X` is a morphism over the base: it is a section of the first
projection. -/
theorem diagonal_comp_selfProductStructure :
    pullback.diagonal sX ≫ selfProductStructure C sX = sX := by
  rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]

/-- The morphism `Y ×_k Z ⟶ X ×_k X` induced by `a : Y ⟶ X` and `b : Z ⟶ X`. This is the test
scheme the Gysin class of the diagonal is capped against to form the intersection product: its
pullback of the diagonal is `Y ×_X Z`, by
`CategoryTheory.Limits.pullbackDiagonalMapIdIso`. -/
abbrev exteriorToSelfProduct :
    (pullback (a ≫ sX) (b ≫ sX) : Scheme.{u}) ⟶ (pullback sX sX : Scheme.{u}) :=
  exteriorToSelfProductMap sX a b

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType a] [LocallyOfFiniteType b] in
/-- Over the base, `Y ×_k Z ⟶ X ×_k X` composed with the structure morphism of `X ×_k X` is the
structure morphism of `Y ×_k Z` that the exterior product of Stacks 0FBV lands at. -/
theorem exteriorToSelfProduct_comp_selfProductStructure :
    exteriorToSelfProduct C sX a b ≫ selfProductStructure C sX =
      pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX) := by
  rw [← Category.assoc, pullback.lift_fst, Category.assoc]

/-- The morphism `Y ×_k Z ⟶ X ×_k X` induced by `a` and `b` is locally of finite type. -/
instance locallyOfFiniteType_exteriorToSelfProduct :
    LocallyOfFiniteType (exteriorToSelfProduct C sX a b) := by
  have : LocallyOfFiniteType (exteriorToSelfProduct C sX a b ≫ selfProductStructure C sX) := by
    rw [exteriorToSelfProduct_comp_selfProductStructure]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (selfProductStructure C sX)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType a] [LocallyOfFiniteType b] in
/-- The identification `(Y ×_k Z) ×_{X ×_k X} X ≅ Y ×_X Z` of
`CategoryTheory.Limits.pullbackDiagonalMapIdIso` is a morphism of schemes over the base. This is
what lets the Gysin pullback of the exterior product be read as a class on `Y ×_X Z`, which is
where Stacks 0FC0 puts the product. -/
theorem pullbackDiagonalMapIdIso_hom_comp_structure :
    (pullbackDiagonalMapIdIso a b sX).hom ≫ (pullback.fst a b ≫ (a ≫ sX)) =
      pullback.fst (pullback.diagonal sX) (exteriorToSelfProduct C sX a b) ≫ sX := by
  calc (pullbackDiagonalMapIdIso a b sX).hom ≫ (pullback.fst a b ≫ (a ≫ sX))
      = ((pullbackDiagonalMapIdIso a b sX).hom ≫ pullback.fst a b) ≫ (a ≫ sX) := by
        rw [Category.assoc]
    _ = (pullback.snd (pullback.diagonal sX) (exteriorToSelfProduct C sX a b) ≫
          pullback.fst (a ≫ sX) (b ≫ sX)) ≫ (a ≫ sX) := by
        rw [pullbackDiagonalMapIdIso_hom_fst]
    _ = pullback.snd (pullback.diagonal sX) (exteriorToSelfProduct C sX a b) ≫
          (exteriorToSelfProduct C sX a b ≫ selfProductStructure C sX) := by
        rw [exteriorToSelfProduct_comp_selfProductStructure, Category.assoc]
    _ = (pullback.fst (pullback.diagonal sX) (exteriorToSelfProduct C sX a b) ≫
          pullback.diagonal sX) ≫ selfProductStructure C sX := by
        rw [← Category.assoc, pullback.condition]
    _ = pullback.fst (pullback.diagonal sX) (exteriorToSelfProduct C sX a b) ≫ sX := by
        rw [Category.assoc, diagonal_comp_selfProductStructure]

end Diagonal

/-! ### Stacks 02S1 at the projections the exterior product uses -/

section Product

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b] (d : ℤ)
  (c : BivariantClass C G sX (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) d)
  (n m : ℤ)

/-- The Gysin pullback `Δ^!(α × β)` of the exterior product along a bivariant class `c` of
the diagonal of `X`, read on the pullback `(Y ×_k Z) ×_{X ×_k X} X` of the diagonal. This is the
intersection product of Stacks 0FC0 before the identification of that pullback with `Y ×_X Z`;
`Stacks.Chow.intersectionProduct` performs the identification.

It is an additive map out of `CH_n(Y) ⊗_ℤ CH_m(Z)`, so the product it defines is `ℤ`-bilinear by
construction; `Stacks.Chow.intersectionProductBilin` is that bilinear form.

The class `c` of the diagonal is an argument, an arbitrary element of `A^d(X ⟶ X ×_k X)`. The
product of Stacks 0FC0, with `c` the Gysin map of the diagonal of Stacks 0FBR, is
`Stacks.Chow.smoothIntersectionProduct`. The instances of Stacks
02S1 that the exterior product needs are not hypotheses: they are supplied by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds`, hence
ultimately by the general case of Stacks 02S1. -/
def diagonalGysinProduct :
    TensorProduct ℤ (chowGroup C (a ≫ sX) n) (chowGroup C (b ≫ sX) m) →+
      chowGroup C (pullback.fst (pullback.diagonal sX) (exteriorToSelfProduct C sX a b) ≫ sX)
        (n + m - d) :=
  (c.cap (exteriorToSelfProduct C sX a b) (n + m)).comp
    (((chowGroupCongr C (exteriorToSelfProduct_comp_selfProductStructure C sX a b).symm
        (n + m)).toAddMonoidHom).comp
      (chowExteriorProduct C hδ (a ≫ sX) (b ≫ sX) n m))

/-- The product

`· : CH_n(Y) ⊗_ℤ CH_m(Z) ⟶ CH_{n+m-d}(Y ×_X Z)`,   `α · β = c(α × β)`,

for `Y` and `Z` locally of finite type over `X`, formed with an arbitrary bivariant class
`c ∈ A^d(X ⟶ X ×_k X)` of the diagonal, given as an argument. The intersection product of Stacks
0FC0 is this at the Gysin map of the diagonal of Stacks 0FBR, with `X` smooth:
`Stacks.Chow.smoothIntersectionProduct`. It is the cap of the exterior product with `c`,
`Stacks.Chow.diagonalGysinProduct`, pushed forward along the identification
`(Y ×_k Z) ×_{X ×_k X} X ≅ Y ×_X Z` the source uses.

The pushforward is along an isomorphism, so the only instance of Stacks 02S2 it needs is the one
that lets proper pushforward descend to Chow groups, and that is supplied here by
`Stacks.Chow.properPushforwardDescends` rather than assumed. The instances of Stacks 02S1 the
exterior product needs are likewise supplied, by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds`. The only
argument of the product beyond the schemes and degrees is therefore the class `c`. -/
def intersectionProduct :
    TensorProduct ℤ (chowGroup C (a ≫ sX) n) (chowGroup C (b ≫ sX) m) →+
      chowGroup C (pullback.fst a b ≫ (a ≫ sX)) (n + m - d) :=
  (properChowPushforward C
      (pullback.fst (pullback.diagonal sX) (exteriorToSelfProduct C sX a b) ≫ sX)
      (pullback.fst a b ≫ (a ≫ sX)) (pullbackDiagonalMapIdIso a b sX).hom
      (pullbackDiagonalMapIdIso_hom_comp_structure C sX a b) (n + m - d)
      (properPushforwardDescends C _ _ _ _ _)).comp
    (diagonalGysinProduct C hδ G sX a b d c n m)

/-- The defining formula of `Stacks.Chow.intersectionProduct`: it is the cap of the exterior
product with the class `c` of the diagonal, carried to `Y ×_X Z`. -/
theorem intersectionProduct_apply
    (t : TensorProduct ℤ (chowGroup C (a ≫ sX) n) (chowGroup C (b ≫ sX) m)) :
    intersectionProduct C hδ G sX a b d c n m t =
      properChowPushforward C
        (pullback.fst (pullback.diagonal sX) (exteriorToSelfProduct C sX a b) ≫ sX)
        (pullback.fst a b ≫ (a ≫ sX)) (pullbackDiagonalMapIdIso a b sX).hom
        (pullbackDiagonalMapIdIso_hom_comp_structure C sX a b) (n + m - d)
        (properPushforwardDescends C _ _ _ _ _)
        (c.cap (exteriorToSelfProduct C sX a b) (n + m)
          (chowGroupCongr C (exteriorToSelfProduct_comp_selfProductStructure C sX a b).symm
            (n + m) (chowExteriorProduct C hδ (a ≫ sX) (b ≫ sX) n m t))) :=
  rfl

/-- The product `Stacks.Chow.intersectionProduct`, formed with a class `c` of the diagonal given
as an argument, as a `ℤ`-bilinear map

`CH_n(Y) → CH_m(Z) → CH_{n+m-d}(Y ×_X Z)`,

which is the shape `α · β` is used in. Bilinearity is free: the product is an additive map out
of the tensor product by construction. -/
def intersectionProductBilin :
    chowGroup C (a ≫ sX) n →ₗ[ℤ] chowGroup C (b ≫ sX) m →ₗ[ℤ]
      chowGroup C (pullback.fst a b ≫ (a ≫ sX)) (n + m - d) :=
  TensorProduct.curry
    (intersectionProduct C hδ G sX a b d c n m).toIntLinearMap

/-- The bilinear form of the product agrees with the product. -/
theorem intersectionProductBilin_apply
    (α : chowGroup C (a ≫ sX) n) (β : chowGroup C (b ≫ sX) m) :
    intersectionProductBilin C hδ G sX a b d c n m α β =
      intersectionProduct C hδ G sX a b d c n m (TensorProduct.tmul ℤ α β) :=
  rfl

end Product

section VirtualNormalBundle

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {X Y Z N : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sN : N ⟶ C.S)
  [LocallyOfFiniteType sN] (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X)
  [LocallyOfFiniteType b] (q : N ⟶ X) [LocallyOfFiniteType q] (hq : q ≫ sX = sN) (r : ℕ) (e : ℤ)
  (E : BivariantClass C G sN (selfProductStructure C sX) (q ≫ pullback.diagonal sX)
    (comp_comp_structureMorphism_eq hq (diagonal_comp_selfProductStructure C sX)) e)
  (π : ∀ {T : Scheme.{u}} (g : T ⟶ (pullback sX sX : Scheme.{u}))
    [LocallyOfFiniteType g] (k : ℤ),
    chowGroup C (pullback.fst (pullback.diagonal sX) g ≫ sX) (k - (r : ℤ)) →+
      chowGroup C (pullback.fst (q ≫ pullback.diagonal sX) g ≫ sN) (k - e))

/-- The Gysin class `c(X ⟶ X ×_k X, 𝒩) ∈ A^r(X ⟶ X ×_k X)` of the diagonal, assembled by
`Stacks.Chow.virtualNormalGysinClass` (the abstract form of the construction of Stacks 0FBK) for a
virtual normal bundle of constant rank `r` for the diagonal, from the flat and Gysin laws `hflat`
and `hgysin` of its prescribed cap operation. For `X` smooth over the base the diagonal is a
regular immersion by
`Stacks.Chow.isRegularImmersion_diagonal_of_smooth`, and its virtual normal bundle is the
conormal bundle, of rank the relative dimension.

This is the class the definitions of `Stacks.Chow.intersectionProduct` carry, so feeding it in
discharges that hypothesis; `Stacks.Chow.intersectionProductOfVirtualNormalBundle` does so.

The instance of Stacks 02S2 that the construction of Stacks 0FBK needs is not a hypothesis here:
it is supplied by `Stacks.Chow.properPushforwardDescends`, which proves that statement
outright. -/
def diagonalVirtualNormalGysinClass (P : VirtualNormalBundleProjection (pullback.diagonal sX) q r)
    (hπ : ∀ {T : Scheme.{u}} (g : T ⟶ (pullback sX sX : Scheme.{u})) [LocallyOfFiniteType g]
      (k : ℤ), Function.Bijective (π g k))
    (hproper : PiProperNaturality C sX sN (pullback.diagonal sX) q r e π)
    (hflat : TransportFlatNaturality C G sX (selfProductStructure C sX) sN
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) q hq r e E π hπ)
    (hgysin : TransportGysinNaturality C G sX (selfProductStructure C sX) sN
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) q hq r e E π hπ) :
    BivariantClass C G sX (selfProductStructure C sX) (pullback.diagonal sX)
      (diagonal_comp_selfProductStructure C sX) (r : ℤ) :=
  virtualNormalGysinClass C G sX (selfProductStructure C sX) sN (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) q hq r e E π P (properPushforwardDescends C) hπ
    hproper hflat hgysin

/-- The product `Stacks.Chow.intersectionProduct` formed with the class of the diagonal that the
construction of Stacks 0FBK produces from the arguments of
`Stacks.Chow.diagonalVirtualNormalGysinClass` (a virtual normal bundle datum, the bijectivity of
Stacks 02TY and the transport laws), which remain arguments here; the degree of the product is
the rank `r`. The intersection product of Stacks 0FC0 with none of these arguments, formed with
the Gysin map of the diagonal of Stacks 0FBR, is `Stacks.Chow.smoothIntersectionProduct`. -/
def intersectionProductOfVirtualNormalBundle
    (P : VirtualNormalBundleProjection (pullback.diagonal sX) q r)
    (hπ : ∀ {T : Scheme.{u}} (g : T ⟶ (pullback sX sX : Scheme.{u})) [LocallyOfFiniteType g]
      (k : ℤ), Function.Bijective (π g k))
    (hproper : PiProperNaturality C sX sN (pullback.diagonal sX) q r e π)
    (hflat : TransportFlatNaturality C G sX (selfProductStructure C sX) sN
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) q hq r e E π hπ)
    (hgysin : TransportGysinNaturality C G sX (selfProductStructure C sX) sN
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) q hq r e E π hπ)
    (n m : ℤ) :
    TensorProduct ℤ (chowGroup C (a ≫ sX) n) (chowGroup C (b ≫ sX) m) →+
      chowGroup C (pullback.fst a b ≫ (a ≫ sX)) (n + m - (r : ℤ)) :=
  intersectionProduct C hδ G sX a b (r : ℤ)
    (diagonalVirtualNormalGysinClass C G sX sN q hq r e E π P hπ hproper hflat hgysin) n m

end VirtualNormalBundle

end Stacks.Chow

end
