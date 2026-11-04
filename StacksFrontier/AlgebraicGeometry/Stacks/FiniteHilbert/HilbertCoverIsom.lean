module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsSiteSize
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram

/-!
# The isomorphism functor of two degree-`d` covers is an algebraic space

Let `S` be a scheme contained in a big fppf site, let `V` be an object of the big fppf site of
`S`, and let `z : Z ⟶ V` and `x : X ⟶ V` be two morphisms of the site which are finite locally
free of degree `d` — that is, two objects of the fibre of the category `ℋ_d` of
`AlgebraicGeometry.Stack.finiteCoverCategory` over `V`. This file proves that the isomorphism
functor `Isom_V(Z, X)` of Stacks 0D1F
(`AlgebraicGeometry.Space.relativeIsom`) is an algebraic space over `S`, with nothing carried.

This is the input that criterion (2) of **Stacks 045G**
(`AlgebraicGeometry.Stack.IsAlgebraicSpaceIsomPresheaf`) asks for at `ℋ_d`, and it is the one
place where that criterion's input is unconditional. The analogous statement for the stack of
proper flat spaces, `AlgebraicGeometry.Space.hasAlgebraicIsomFunctors`, carries Stacks 0D01
through `AlgebraicGeometry.Space.HasHilbertModels`, because there the four relative morphism
functors of the square are only known to be algebraic spaces from the Hilbert-model hypothesis.
For a degree-`d` cover they are algebraic spaces outright: the source of each of the four is
finite locally free of rank `d` over `V`, so
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank'`
applies to each, its condition on the site being discharged by
`AlgebraicGeometry.Space.relativeHomRepresentingContained`.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicSpace_relativeIsom_of_isFiniteLocallyFreeOfRank`: the
  isomorphism functor of two morphisms of the site which are finite locally free of rank `d` is
  an algebraic space over `S`.
* `AlgebraicGeometry.Stack.isAlgebraicSpace_relativeIsom_finiteCover`: the same, stated for two
  objects of the fibre of `ℋ_d` over `V`.

## Implementation notes

The four relative morphism functors of the square are `Mor_V(Z, X)`, `Mor_V(X, Z)`,
`Mor_V(Z, Z)` and `Mor_V(X, X)`. Each has a source which is one of `Z` and `X`, and both of
those are finite locally free of rank `d` over `V`; the *target* is unconstrained in
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank'`,
which is what lets all four be discharged by the same lemma.

The two degrees are the same number `d` in the statement. Nothing in the argument needs that:
two covers of different degrees would do just as well, each ordered pair being handled by the
rank of its own source. The common degree is kept because that is the shape the fibre of `ℋ_d`
has, and because the consumer — criterion (2) of Stacks 045G at `ℋ_d` — only ever presents two
objects of one and the same fibre.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 0D1F](https://stacks.math.columbia.edu/tag/0D1F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The isomorphism functor of two finite locally free morphisms of rank `d` is an algebraic
space.** For `z : Z ⟶ V` and `x : X ⟶ V` morphisms of the big fppf site of `S` whose underlying
morphisms of schemes are finite locally free of rank `d`, the isomorphism functor
`Isom_{yoneda V}(yoneda Z, yoneda X)` of Stacks 0D1F is an algebraic space over `S`. -/
theorem isAlgebraicSpace_relativeIsom_of_isFiniteLocallyFreeOfRank
    {V Zs Xs : BigFppfOver B S hS} (z : Zs ⟶ V) (x : Xs ⟶ V) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map z) d]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map x) d] :
    IsAlgebraicSpace B S hS
      (Space.relativeIsom B S hS (yoneda.obj Zs) (yoneda.obj Xs) (yoneda.obj V)
        (yoneda.map z) (yoneda.map x) (isAlgebraicSpace_yoneda B S hS Zs)
        (isAlgebraicSpace_yoneda B S hS Xs) (isAlgebraicSpace_yoneda B S hS V)) :=
  Space.isAlgebraicSpace_relativeIsom B S hS _ _ _ _ _ _ _ _
    (Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank' z
      (yoneda.map x) d)
    (Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank' x
      (yoneda.map z) d)
    (Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank' z
      (yoneda.map z) d)
    (Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank' x
      (yoneda.map x) d)

/-- The structure morphism of a degree-`d` cover, composed with an equality of its base, is finite
locally free of rank `d`. -/
private theorem isFiniteLocallyFreeOfRank_map_q_eqToHom {d : ℕ} {V : BigFppfOver B S hS}
    (P : FiniteCover B S hS d) (hP : P.U = V) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map (P.q ≫ eqToHom hP)) d := by
  subst hP
  simpa using P.finiteLocallyFree

/-- **The isomorphism functor of two objects of the fibre of `ℋ_d` is an algebraic space.** Two
objects of the category `ℋ_d` of degree-`d` finite locally free covers lying over one and the
same object `V` of the big fppf site of `S` have an isomorphism functor which is an algebraic
space over `S`. -/
theorem isAlgebraicSpace_relativeIsom_finiteCover {d : ℕ} {V : BigFppfOver B S hS}
    (P Q : FiniteCover B S hS d) (hP : P.U = V) (hQ : Q.U = V) :
    IsAlgebraicSpace B S hS
      (Space.relativeIsom B S hS (yoneda.obj P.Z) (yoneda.obj Q.Z) (yoneda.obj V)
        (yoneda.map (P.q ≫ eqToHom hP)) (yoneda.map (Q.q ≫ eqToHom hQ))
        (isAlgebraicSpace_yoneda B S hS P.Z) (isAlgebraicSpace_yoneda B S hS Q.Z)
        (isAlgebraicSpace_yoneda B S hS V)) :=
  have := isFiniteLocallyFreeOfRank_map_q_eqToHom P hP
  have := isFiniteLocallyFreeOfRank_map_q_eqToHom Q hQ
  isAlgebraicSpace_relativeIsom_of_isFiniteLocallyFreeOfRank _ _ d

end AlgebraicGeometry.Stack

end
