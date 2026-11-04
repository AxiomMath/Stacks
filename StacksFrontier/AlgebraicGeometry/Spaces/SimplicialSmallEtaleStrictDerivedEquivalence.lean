module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictDegree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfEquivalence

/-!
# The strict components of a simplicial algebraic space have the same derived categories

The comparisons of ringed topoi `(Sh((X_n)_{spaces,étale}), 𝒪_{X_n}) ⟶ (Sh(C_n), 𝒪_n)` of the
strict components and `(Sh(X_{spaces,étale}), 𝒪_X) ⟶ (Sh(total), 𝒪)` of the total sites are
equivalences of ringed topoi, so their derived pullbacks are equivalences of derived
categories of modules.

## Main results

* `isEquivalence_derivedPullback_strictComponentRingedToposHom`: the derived pullback along the
  comparison of each strict component is an equivalence.
* `isEquivalence_derivedPullback_strictRingedToposHom`: the derived pullback along the comparison
  of the total sites is an equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Cohomology.DerivedPullbackOfToposHom

universe u

-- no global `HasDerivedCategory` instance at this universe
attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

/-- **The derived pullback along the comparison of a strict component is an equivalence**
`D(𝒪_n) ≌ D(𝒪_{X_n})`. -/
instance isEquivalence_derivedPullback_strictComponentRingedToposHom (n : SimplexCategory) :
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
      (strictComponentRingedToposHom X n)).IsEquivalence := by
  have := isEquivalence_derivedPullback_of_isEquivalence_derivedPullbackOfEquivalence
    (strictComponentRingedToposHom X n)
  exact this

/-- **The derived pullback along the comparison of the total sites is an equivalence**
`D(𝒪) ≌ D(𝒪_X)`. -/
instance isEquivalence_derivedPullback_strictRingedToposHom :
    (derivedPullback (X := ringedTopos X) (Y := strictRingedTopos X)
      (strictRingedToposHom X)).IsEquivalence := by
  have := isEquivalence_derivedPullback_of_isEquivalence_derivedPullbackOfEquivalence
    (strictRingedToposHom X)
  exact this

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
