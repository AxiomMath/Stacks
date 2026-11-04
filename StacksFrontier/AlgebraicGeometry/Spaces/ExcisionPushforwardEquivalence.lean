module

public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionPushforwardAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionPushforwardEssSurj

/-!
# Essential surjectivity of the base-change functor of Stacks 0BGY

Let `f : V ⟶ W` be a separated étale morphism of algebraic spaces over a scheme `S` and let `T`
be a closed subspace of `W` whose preimage is carried isomorphically onto it. Let `W₀` be a
subfunctor of `W` containing the open complement of `T`.

The base-change functor of Stacks 0BGY from the modifications of `W` outside `W₀` to the
modifications of `V` outside `f^{-1}W₀` is essentially surjective.

`StacksFrontier/AlgebraicGeometry/Spaces/ExcisionPushforwardEssSurj.lean` proves this from the
algebraicity of the presheaf of pairs, and
`StacksFrontier/AlgebraicGeometry/Spaces/ExcisionPushforwardAlgebraic.lean` proves that
algebraicity. This file puts the two together.

## Main results

* `AlgebraicGeometry.Space.essSurj_baseChangeFunctor_of_openComplement_le`: **the base-change
  functor of Stacks 0BGY is essentially surjective.**

## Implementation notes

The quantified hypothesis of
`AlgebraicGeometry.Space.essSurj_baseChangeFunctor_of_isAlgebraicSpace` ranges over every
algebraic space over `V` which is unchanged over `f^{-1}W₀`, and
`AlgebraicGeometry.Space.isAlgebraicSpace_excisionSpace` is stated at exactly that data, so the
substitution is immediate. Closedness of `T` is the one hypothesis the algebraicity needs and
the essential surjectivity does not: it is what makes the open complement of `T` an open
subspace, so that it and the open image of `f` are a Zariski covering of `W`.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **The base-change functor of Stacks 0BGY is essentially surjective.** Every algebraic space
over `V` which is unchanged over `f^{-1}W₀` is the base change of an algebraic space over `W`
which is unchanged over `W₀`, namely of the presheaf of pairs; that presheaf is an algebraic
space by `AlgebraicGeometry.Space.isAlgebraicSpace_excisionSpace`. -/
theorem essSurj_baseChangeFunctor_of_openComplement_le (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    {V W : AlgebraicSpaces B S hS} (f : V ⟶ W) (T W₀ : Subfunctor W.obj)
    (hTcl : IsClosedSubspace B S hS T) (hT : IsIso (T.fromPreimage f.hom))
    (hcompl : openComplement B S hS T ≤ W₀) (hf : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) :
    (baseChangeFunctor B S hS f W₀).1.EssSurj :=
  essSurj_baseChangeFunctor_of_isAlgebraicSpace B S hS f T W₀ hT hcompl hf hsep
    fun _ h hY hiso =>
      isAlgebraicSpace_excisionSpace B S hS f h hY T W₀ hT hcompl hf hsep hiso hTcl

end AlgebraicGeometry.Space

end
