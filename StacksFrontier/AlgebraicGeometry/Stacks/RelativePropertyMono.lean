module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty

/-!
# Relative properties of representable 1-morphisms are monotone (Stacks 045F)

Let `S` be a scheme contained in a big fppf site and let `P`, `P'` be properties of morphisms of
algebraic spaces over `S` as in Stacks 03YK. **Stacks 045F** says that if `P` implies `P'` for
every morphism of algebraic spaces, then a 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in
groupoids over `(Sch/S)_fppf` which is representable by algebraic spaces and has the relative
property `P` also has the relative property `P'`.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_mono`: **Stacks 045F**.

## Implementation notes

The implication hypothesis is the order relation `P ≤ P'` of
`CategoryTheory.MorphismProperty`, which is exactly "`P a → P' a` for every morphism `a` of
algebraic spaces over `S`".

The proof is that `AlgebraicGeometry.Stack.HasRelativeProperty` is a universally quantified
statement whose only occurrence of the property is its conclusion, so the implication may be
applied under the quantifiers. The same observation for the étale-smooth local properties of
Stacks 0CIG is `AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_mono` (**Stacks 0CIJ**).

Both properties carry the base-change and fppf-target-locality instances that Stacks 03YK
requires of a property for the relative notion to be defined at all; neither is used in the
proof.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045F](https://stacks.math.columbia.edu/tag/045F)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 045F.** If a property `P` of morphisms of algebraic spaces over `S` implies a
property `P'`, then a 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` which is
representable by algebraic spaces and has the relative property `P` of Stacks 03YK also has the
relative property `P'`.

The relative property is a universally quantified statement in which the property occurs only in
the conclusion, so the implication applies under the quantifiers. -/
@[stacks 045F]
theorem hasRelativeProperty_mono
    {P P' : MorphismProperty (AlgebraicSpaces B S hS)}
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    [P'.IsStableUnderBaseChange] [P'.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (hPP' : P ≤ P')
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {f : 𝒳 ⟶ 𝒴}
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hP : HasRelativeProperty B S hS P f hf) :
    HasRelativeProperty B S hS P' f hf :=
  fun U y hy F hF hEquiv => hPP' _ (hP U y hy F hF hEquiv)

end AlgebraicGeometry.Stack

end
