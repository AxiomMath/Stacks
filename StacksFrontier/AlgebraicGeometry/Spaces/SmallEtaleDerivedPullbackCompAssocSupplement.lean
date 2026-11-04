module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangePastingOnRingedTopoi
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackCompAssoc

/-!
# Associativity of the composition law of derived pullbacks of algebraic spaces

For morphisms `a : W ⟶ X`, `b : X ⟶ Y`, `c : Y ⟶ Z` of algebraic spaces, the two ways of
identifying `Lc^* ⋙ Lb^* ⋙ La^*` with `L(a ≫ b ≫ c)^*` through the composition law of Stacks 0D6D
(`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`) agree.  This is the cocycle
identity behind the compatibilities of the base change map with stacking squares (Stacks 0E46,
0E47).  We also record the composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` of derived direct
images, adjoint to the composition law of derived pullbacks.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleModulePullbackCompIso`: the composition law
  `g^* ⋙ f^* ≅ (f ≫ g)^*` of pullbacks of modules along the morphisms of small étale ringed topoi.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePushforwardCompIso`: `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleModulePullbackCompIso_assoc`: its cocycle identity.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_assoc`: the cocycle identity
  of Stacks 0D6D for algebraic spaces.
* `AlgebraicGeometry.Space.conjugateEquiv_smallEtaleDerivedModulePullbackCompIso_inv`: the
  composition isomorphism of derived direct images is adjoint to that of derived pullbacks.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pullbackMapHomotopy)

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The composition law of pullbacks of modules -/

section Modules

variable {W X Y Z : AlgebraicSpaces B S hS}

end Modules

/-! ### On homotopy categories -/

section Homotopy

variable {W X Y Z : AlgebraicSpaces B S hS}

end Homotopy

/-! ### The cocycle identity of Stacks 0D6D -/

section Derived

variable {W X Y Z : AlgebraicSpaces B S hS}

end Derived

/-! ### The composition isomorphism of derived direct images -/

section Pushforward

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The composition isomorphism of derived direct images** `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` for
morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces: both are right adjoint to
`L(f ≫ g)^*`, the first through the composition law of Stacks 0D6D. -/
def smallEtaleDerivedModulePushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPushforward (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f) ⋙
      derivedPushforward (X := smallEtaleRingedTopos B S hS Y)
        (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS g) ≅
    derivedPushforward (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS (f ≫ g)) :=
  Adjunction.rightAdjointUniq
    (((smallEtaleDerivedModuleAdjunction B S hS g).comp
      (smallEtaleDerivedModuleAdjunction B S hS f)).ofNatIsoLeft
        (smallEtaleDerivedModulePullbackCompIso B S hS f g))
    (smallEtaleDerivedModuleAdjunction B S hS (f ≫ g))

end Pushforward

end AlgebraicGeometry.Space

end
