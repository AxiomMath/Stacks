module

public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Conditions
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberDimension
public import StacksFrontier.RingTheory.RelativeDimension.Basic

/-!
# The fibre dimension of Tag 01V9 is a relative dimension of rings

Conditions (3) and (4) of Stacks Tag 01V9 bound the number of generators of the relative
differentials by `topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)`, the dimension at `x` of
the scheme-theoretic fibre of `f` through `x`.  The commutative algebra of the source — Tag 00TT
through `Algebra.relativeDimensionAt` — reads that dimension as the relative dimension of a ring
map at a prime.  **This file is the dictionary between them.**

## Main results

* `Stacks.Tag01V9NumericalCriterion.fiberDimensionAt_specMap`: for a morphism of affine schemes,
  the dimension at a point of the scheme-theoretic fibre is the relative dimension of the ring
  map at the corresponding prime.
* `Stacks.Tag01V9NumericalCriterion.fiberDimensionAt_eq_relativeDimensionAt`: on affine
  neighbourhoods `U ∋ x` of the source and `V ⊇ f(U)` of the target, the dimension at `x` of the
  scheme-theoretic fibre of `f` is `Algebra.relativeDimensionAt Γ(S, V) 𝔮` for `𝔮` the prime
  of `x`.

## Implementation notes

There is no new mathematics here.  The affine case holds because the scheme-theoretic fibre of a
`Spec.map` is homeomorphic to the subspace `comap ⁻¹' {𝔭}` of the prime spectrum by
`AlgebraicGeometry.Scheme.Hom.fiberHomeo`, and `Algebra.relativeDimensionAt` is by definition
`topologicalKrullDimAt` of exactly that subspace.  The general case follows because the square
`U.fromSpec ≫ f = Spec.map (f.appLE V U) ≫ V.fromSpec` has open immersions down both sides, so
`AlgebraicGeometry.fiberDimensionAt_eq_of_open_square` moves the fibre dimension from `f` at `x`
to `Spec.map (f.appLE V U)` at the prime of `x`.

The statements fix the algebra structure with a `letI` of
`AlgebraicGeometry.Scheme.Hom.appLE` rather than taking an `[Algebra Γ(S, V) Γ(X, U)]` instance
together with an equation identifying its `algebraMap`.  The second shape is the more flexible
one, and it is unusable here: rewriting the identification underneath
`Algebra.relativeDimensionAt`, whose body is a subspace of a prime spectrum cut out by
`PrimeSpectrum.comap (algebraMap _ _)`, exhausts the heartbeat budget at `whnf`.  With the
structure fixed, no `isDefEq` comparison of two spellings of the same ring map is demanded and
the proof is three rewrites.

## References

* [Stacks Project, Tag 00QD](https://stacks.math.columbia.edu/tag/00QD)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Tag01V9NumericalCriterion

/-- **For a morphism of affine schemes the fibre dimension at a point is the relative dimension
of the ring map at the corresponding prime.**  The scheme-theoretic fibre of `Spec.map φ` through
a point is homeomorphic to the fibre subspace of `PrimeSpectrum B` that
`Algebra.relativeDimensionAt` is defined as the local dimension of. -/
public theorem fiberDimensionAt_specMap {R B : CommRingCat.{u}} (φ : R ⟶ B) (y : Spec B)
    [y.asIdeal.IsPrime] :
    topologicalKrullDimAt ((Spec.map φ).fiber ((Spec.map φ) y)) ((Spec.map φ).asFiber y) =
      (letI := φ.hom.toAlgebra
       Algebra.relativeDimensionAt R y.asIdeal) := by
  let _ := φ.hom.toAlgebra
  rw [topologicalKrullDimAt_eq_of_homeomorph ((Spec.map φ).fiberHomeo _) _,
    Algebra.relativeDimensionAt]
  congr 1
  exact Subtype.ext ((Spec.map φ).fiberι_asFiber y)

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- **The fibre dimension of conditions (3) and (4) of Tag 01V9 is the relative dimension of the
ring map on affine charts.**  For affine opens `U ∋ x` of the source and `V` of the target with
`U ≤ f⁻¹ V`, the dimension at `x` of the scheme-theoretic fibre of `f` through `x` equals
`dim_𝔮(Γ(X, U)/Γ(S, V))`, where `𝔮` is the prime of `Γ(X, U)` corresponding to `x`. -/
public theorem fiberDimensionAt_eq_relativeDimensionAt
    (U : X.affineOpens) (V : S.affineOpens) (hxU : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      (letI := (f.appLE V.1 U.1 hUV).hom.toAlgebra
       Algebra.relativeDimensionAt Γ(S, V.1) (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) := by
  have _ : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have _ : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have hopen := fiberDimensionAt_eq_of_open_square
    U.2.fromSpec f (Spec.map (f.appLE V.1 U.1 hUV)) V.2.fromSpec
    (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 U.2 hUV).symm (U.2.primeIdealOf ⟨x, hxU⟩)
  rw [U.2.fromSpec_primeIdealOf ⟨x, hxU⟩] at hopen
  exact hopen.symm.trans (fiberDimensionAt_specMap
    (φ := CommRingCat.ofHom (f.appLE V.1 U.1 hUV).hom) (U.2.primeIdealOf ⟨x, hxU⟩))

end Stacks.Tag01V9NumericalCriterion

end
