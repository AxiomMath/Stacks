module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedTensorPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedDualPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.EssentiallySmallDerivedDualAdjunction

/-!
# The two derived duals on an algebraic space agree, and commute with derived pullback

Let `X` be an algebraic space. There are two constructions of the derived dual
`E^∨ = R𝓗om(E, 𝒪_X)` of an object `E` of `D(𝒪_X)`: `AlgebraicGeometry.Space.derivedDual`,
computed on a small model of the small étale site through restriction of sheaves of modules, and
`AlgebraicGeometry.Space.smallEtaleDerivedDual`, computed on the model of the small étale ringed
topos. Both are the value at `𝒪_X` of a right adjoint of `- ⊗^𝐋 E` (Stacks 08J8), so they are
canonically isomorphic. Consequently `AlgebraicGeometry.Space.derivedDual` commutes with derived
pullback along any morphism of algebraic spaces when `E` is perfect: `Lf^*(E^∨) ≅ (Lf^*E)^∨`.

## Main definitions

* `AlgebraicGeometry.Space.derivedDualIsoSmallEtaleDerivedDual`: the canonical isomorphism
  between the two derived duals.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackDerivedDualIso`: `Lf^*(E^∨) ≅ (Lf^*E)^∨`
  for `E` perfect, for the dual `AlgebraicGeometry.Space.derivedDual`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] hasMapBifunctor_sheafTensor_smallEtale

/-- **The two derived duals on an algebraic space agree**: `derivedDual E`, computed on a small
model of the small étale site, is canonically isomorphic to `smallEtaleDerivedDual E`, computed
on the model of the small étale ringed topos.  Both are the value at `𝒪_X` of a right adjoint of
`- ⊗^𝐋 E`, and right adjoints are unique up to unique isomorphism. -/
def derivedDualIsoSmallEtaleDerivedDual (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    derivedDual B S hS X.1 X.2 E ≅ smallEtaleDerivedDual B S hS X E :=
  RingedSite.essentiallySmallDerivedDualIso _ E ≪≫
    ((RingedSite.essentiallySmallDerivedTensorSheafHomAdjunction _ E).rightAdjointUniq
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS X E)).app _

/-- **The derived dual of a perfect object commutes with derived pullback**, for the dual
`AlgebraicGeometry.Space.derivedDual`: for `f : X ⟶ Y` and `E ∈ D(𝒪_Y)` perfect,
`Lf^*(E^∨) ≅ (Lf^*E)^∨`. -/
def smallEtaleDerivedModulePullbackDerivedDualIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hE : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect E) :
    (smallEtaleDerivedModulePullback B S hS f).obj (derivedDual B S hS Y.1 Y.2 E) ≅
      derivedDual B S hS X.1 X.2 ((smallEtaleDerivedModulePullback B S hS f).obj E) :=
  (smallEtaleDerivedModulePullback B S hS f).mapIso (derivedDualIsoSmallEtaleDerivedDual Y E) ≪≫
    smallEtaleDerivedModulePullbackDualIso f E hE ≪≫
    (derivedDualIsoSmallEtaleDerivedDual X _).symm

end AlgebraicGeometry.Space

end
