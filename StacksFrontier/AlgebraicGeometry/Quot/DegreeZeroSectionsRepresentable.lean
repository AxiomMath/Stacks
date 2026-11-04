module

public import StacksFrontier.AlgebraicGeometry.Quot.DegreeZeroSectionsSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08JX, part (1)

Let `K` be a pseudo-coherent object of `D(𝒪_X)` on an algebraic space `X` such that
`H⁻¹(Lg^*K) = 0` for every scheme `g : T → X`.  Then the functor
`(g : T → X) ↦ H⁰(T, H⁰(Lg^*K))` is an algebraic space affine and of finite presentation over `X`.

The functor is `AlgebraicGeometry.Space.degreeZeroSectionsFunctor` of a K-flat complex `P₀` with
flat terms representing `K` (Stacks 06YS): on such a complex `Lg^*K` is computed by `g^*P₀`
(Stacks 06YY), and the value of the functor at `g` is `H⁰(T, H⁰(Lg^*K))` by
`AlgebraicGeometry.Space.degreeZeroSectionsEquiv`.

The proof is the source's.  The functor is an fpqc sheaf
(`AlgebraicGeometry.Space.isSheaf_degreeZeroSectionsFunctor`), and every scheme over `X` is
covered, in the fppf topology, by schemes over which it is the scheme of solutions of a system of
linear equations (`AlgebraicGeometry.Space.exists_covering_representedOverLift`); such a functor
is an algebraic space affine and of finite presentation over `X`
(`AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_of_sieveLocal`).

## Main results

* `AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_degreeZeroSectionsFunctor`:
  **Stacks 08JX, part (1).**

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **Stacks 08JX, part (1), for any choice of the derived pullbacks.**  The statement of
`AlgebraicGeometry.Space.isAffineFinitePresentationAlgebraicSpaceOver_degreeZeroSectionsFunctor`
with the vanishing hypothesis read through an arbitrary witness `hL` of the existence of the
derived pullbacks (`AlgebraicGeometry.Space.hasDerivedModulePullbacks` is one). -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_degreeZeroSectionsFunctor_of_hasDerived
    (K : derivedModules B S hS X) (hK : IsPseudoCoherentObject K)
    (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
    (hvan : HasVanishingDegreeNegOneDerivedPullback hL K)
    (P₀ : CochainComplex (toposModules B S hS X) ℤ)
    (hP₀ : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀))
    (e : DerivedCategory.Q.obj P₀ ≅ K) :
    IsAffineFinitePresentationAlgebraicSpaceOver X
      (degreeZeroSectionsFunctor (schemesOverCone X) P₀) :=
  isAffineFinitePresentationAlgebraicSpaceOver_of_sieveLocal _
    (isSheaf_degreeZeroSectionsFunctor P₀ hP₀ hK e)
    fun Z _ => exists_covering_representedOverLift P₀ hP₀ hK hL hvan e Z

/-- **Stacks 08JX, part (1).**  Let `K` be a pseudo-coherent object of `D(𝒪_X)` on an algebraic
space `X` such that `H⁻¹(Lg^*K) = 0` for every scheme `g : T → X`.  Then the functor
`(g : T → X) ↦ H⁰(T, H⁰(Lg^*K))` on the schemes over `X` is an algebraic space affine and of
finite presentation over `X`.

The functor is the degree-zero sections functor of any K-flat complex `P₀` with flat terms
representing `K`; its value at `g` is `H⁰(T, H⁰(Lg^*K))` by
`AlgebraicGeometry.Space.degreeZeroSectionsEquiv`. -/
@[stacks 08JX "part (1)"]
theorem isAffineFinitePresentationAlgebraicSpaceOver_degreeZeroSectionsFunctor
    (K : derivedModules B S hS X) (hK : IsPseudoCoherentObject K)
    (hvan : HasVanishingDegreeNegOneDerivedPullback (hasDerivedModulePullbacks B S hS) K)
    (P₀ : CochainComplex (toposModules B S hS X) ℤ)
    (hP₀ : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀))
    (e : DerivedCategory.Q.obj P₀ ≅ K) :
    IsAffineFinitePresentationAlgebraicSpaceOver X
      (degreeZeroSectionsFunctor (schemesOverCone X) P₀) :=
  isAffineFinitePresentationAlgebraicSpaceOver_degreeZeroSectionsFunctor_of_hasDerived K hK _ hvan
    P₀ hP₀ e

end AlgebraicGeometry.Space

end
