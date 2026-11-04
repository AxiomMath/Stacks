module

public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenLocus

/-!
# An open locus makes a 1-morphism of categories fibred in groupoids an open immersion

A fully faithful 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf
site of a scheme `S` which has an open locus is representable by algebraic spaces and is an open
immersion.

## Main results

* `AlgebraicGeometry.Stack.isOpenImmersion_and_isRepresentableByAlgebraicSpaces_of_hasOpenLocus`:
  a fully faithful 1-morphism of categories fibred in groupoids with an open locus is
  representable by algebraic spaces and is an open immersion.
* `AlgebraicGeometry.Stack.isOpenImmersion_of_hasOpenLocus'` and
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_hasOpenLocus'`: the two conjuncts
  separately.

## References

* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A fully faithful 1-morphism of categories fibred in groupoids with an open locus is an open
immersion. -/
theorem isOpenImmersion_of_hasOpenLocus' (f : 𝒳 ⟶ 𝒴)
    (hfull : (CatFiberedInGroupoids.homFunctor f).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor f).Faithful)
    (hopen : HasOpenLocus B S hS f.hom) :
    IsOpenImmersion B S hS f :=
  isOpenImmersion_of_hasOpenLocus B S hS f.hom hfull hfaithful hopen

/-- A fully faithful 1-morphism of categories fibred in groupoids with an open locus is
representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_of_hasOpenLocus' (f : 𝒳 ⟶ 𝒴)
    (hfull : (CatFiberedInGroupoids.homFunctor f).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor f).Faithful)
    (hopen : HasOpenLocus B S hS f.hom) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom :=
  isRepresentableByAlgebraicSpaces_of_hasOpenLocus B S hS f.hom hfull hfaithful hopen

/-- A fully faithful 1-morphism of categories fibred in groupoids over the big fppf site of `S`
whose image is cut out, on the base of every scheme-valued point of the target, by an open
subscheme is representable by algebraic spaces and an open immersion. -/
theorem isOpenImmersion_and_isRepresentableByAlgebraicSpaces_of_hasOpenLocus (f : 𝒳 ⟶ 𝒴)
    (hfull : (CatFiberedInGroupoids.homFunctor f).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor f).Faithful)
    (hopen : HasOpenLocus B S hS f.hom) :
    IsOpenImmersion B S hS f ∧ IsRepresentableByAlgebraicSpaces B S hS f.hom :=
  ⟨isOpenImmersion_of_hasOpenLocus' B S hS f hfull hfaithful hopen,
    isRepresentableByAlgebraicSpaces_of_hasOpenLocus' B S hS f hfull hfaithful hopen⟩

end AlgebraicGeometry.Stack

end
