module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Nodal
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# Prestable families of curves (Stacks 0E6T)

A family of curves `f : X ⟶ S` is *prestable* when `f` is at-worst-nodal of relative
dimension one and `f_*𝒪_X = 𝒪_S` universally, that is, after every base change. These are the
families whose geometric fibres are connected, reduced, one-dimensional and smooth away from
finitely many nodes, so that the category of prestable families is the stack of prestable
curves.

## Main definitions

* `AlgebraicGeometry.HasUniversallyBijectiveGlobalFunctions` is the condition
  `f_*𝒪_X = 𝒪_S` together with its stability under base change.
* `AlgebraicGeometry.IsPrestableCurveFamily`: **Stacks 0E6T**, prestability of a family of
  curves.

## Main results

There are no propositional results. The definition is an abbreviation, so its nodality and
direct-image conditions are directly available to statements about prestable families.

## Implementation notes

The equality `f_*𝒪_X = 𝒪_S` of sheaves on the base, and its persistence under base change,
are expressed in the single universally quantified form that the source's footnote tests: for
every algebraic space `Y` over the base and every morphism `Y ⟶ S`, pullback of global
regular functions along the projection `X ×_S Y ⟶ Y` is bijective. Letting `Y` range over all
algebraic spaces over `S` recovers the sheaf equality, since the sections of `f_*𝒪_X` over
`Y ⟶ S` are the global functions on `X ×_S Y`, and simultaneously records that the equality is
preserved by arbitrary base change. The source's equivalent reformulations — étaleness of the
Stein factorization, or connectedness of the geometric fibres — are not available here, so the
universal form is the definition, exactly as in the source.

Nodality is the every-étale-chart condition for algebraic spaces,
`AlgebraicGeometry.Space.IsAtWorstNodalOfRelativeDimensionOne`, since the total space of a
family of curves is an algebraic space and need not be a scheme.

## References

* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0DSE](https://stacks.math.columbia.edu/tag/0DSE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The direct image of the structure sheaf of a family of curves is the structure sheaf of
the base, universally: after every base change along an algebraic space over the base, the
projection induces a bijection on global regular functions. -/
abbrev HasUniversallyBijectiveGlobalFunctions (X : CurveFamily B hZ) : Prop :=
  ∀ (Y : AlgebraicSpaces B integerBase hZ) (g : Y ⟶ schemeSpace X.base),
    Function.Bijective (Space.globalFunctionsMap B integerBase hZ
      (ObjectProperty.homMk (pullback.snd X.toBase.hom g.hom) :
        AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase g ⟶ Y))

/-- **Stacks 0E6T.** A family of curves is *prestable* when its structure morphism is
at-worst-nodal of relative dimension one and the direct image of its structure sheaf is the
structure sheaf of the base, universally. -/
@[stacks 0E6T]
abbrev IsPrestableCurveFamily (X : CurveFamily B hZ) : Prop :=
  Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ X.toBase.hom ∧
    HasUniversallyBijectiveGlobalFunctions B hZ X

end AlgebraicGeometry

end
