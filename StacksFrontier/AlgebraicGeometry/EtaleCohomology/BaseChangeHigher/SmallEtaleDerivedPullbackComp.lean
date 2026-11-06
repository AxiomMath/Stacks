module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward

/-!
# The composition comparison for the derived inverse image of abelian étale sheaves

For morphisms of schemes `a : X ⟶ Y` and `b : Y ⟶ Z` this file constructs the comparison
$$
R(b^{-1}) \circ R(a^{-1}) \;\cong\; R((a \circ b)^{-1})
$$
of functors `D⁺(Z_{ét}) ⥤ D⁺(X_{ét})` on bounded below derived categories of abelian sheaves
on the small étale sites, together with the identity that characterizes it on the
derived-functor units.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbPlusCompIso`: **the comparison
  `R(b^{-1}) R(a^{-1}) ≅ R((a b)^{-1})`.**

## Main results

* `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbPlusCompIso_fac`: **the characterizing
  factorization** through the derived-functor units of the three derived inverse images.
* `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbPlusCompIso_inv_app`: the same identity
  solved for the inverse of the comparison.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section PullbackComp

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **The composition comparison `R(b^{-1}) R(a^{-1}) ≅ R((a b)^{-1})`** for the derived
inverse image of abelian sheaves on the small étale sites. -/
def smallEtaleDerivedPullbackAbPlusCompIso :
    (smallEtalePullbackAb b).rightDerivedFunctorPlus ⋙
        (smallEtalePullbackAb a).rightDerivedFunctorPlus ≅
      (smallEtalePullbackAb (a ≫ b)).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompIsoOfExact (smallEtalePullbackAb b)
    (smallEtalePullbackAb a) (smallEtalePullbackAb (a ≫ b))
    (smallEtalePullbackAbCompIso a b)

/-- **The characterizing factorization of `smallEtaleDerivedPullbackAbPlusCompIso`**: on a bounded
below complex `N`, the derived-functor units of `R(a^{-1})` and `R(b^{-1})` followed by the
comparison give the degreewise composition isomorphism followed by the derived-functor unit of
`R((a b)^{-1})`. -/
theorem smallEtaleDerivedPullbackAbPlusCompIso_fac
    (N : HomotopyCategory.Plus (Sheaf (smallEtaleTopology Z) Ab.{u + 1})) :
    (smallEtalePullbackAb a).rightDerivedFunctorPlusUnith.app
          ((smallEtalePullbackAb b).mapHomotopyCategoryPlus.obj N) ≫
        (smallEtalePullbackAb a).rightDerivedFunctorPlus.map
            ((smallEtalePullbackAb b).rightDerivedFunctorPlusUnith.app N) ≫
          (smallEtaleDerivedPullbackAbPlusCompIso a b).hom.app
            (DerivedCategory.Plus.Qh.obj N) =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso
            (smallEtalePullbackAbCompIso a b)).hom.app N) ≫
        (smallEtalePullbackAb (a ≫ b)).rightDerivedFunctorPlusUnith.app N :=
  Functor.rightDerivedFunctorPlusCompIsoOfExact_fac (smallEtalePullbackAb b)
    (smallEtalePullbackAb a) (smallEtalePullbackAb (a ≫ b))
    (smallEtalePullbackAbCompIso a b) N

/-- **The characterizing factorization of `smallEtaleDerivedPullbackAbPlusCompIso`, solved for the
inverse of the comparison.** All three inverse images are exact, so all three
derived-functor units are invertible. -/
theorem smallEtaleDerivedPullbackAbPlusCompIso_inv_app
    (N : HomotopyCategory.Plus (Sheaf (smallEtaleTopology Z) Ab.{u + 1})) :
    letI : IsIso (smallEtalePullbackAb a).rightDerivedFunctorPlusUnith :=
      Stacks.Cohomology.BaseChange.exactUnit_isIso (smallEtalePullbackAb a)
    letI : IsIso (smallEtalePullbackAb b).rightDerivedFunctorPlusUnith :=
      Stacks.Cohomology.BaseChange.exactUnit_isIso (smallEtalePullbackAb b)
    letI : IsIso (smallEtalePullbackAb (a ≫ b)).rightDerivedFunctorPlusUnith :=
      Stacks.Cohomology.BaseChange.exactUnit_isIso (smallEtalePullbackAb (a ≫ b))
    (smallEtaleDerivedPullbackAbPlusCompIso a b).inv.app
          (DerivedCategory.Plus.Qh.obj N) ≫
        (smallEtalePullbackAb a).rightDerivedFunctorPlus.map
            ((asIso (smallEtalePullbackAb b).rightDerivedFunctorPlusUnith).inv.app N) ≫
          (asIso (smallEtalePullbackAb a).rightDerivedFunctorPlusUnith).inv.app
            ((smallEtalePullbackAb b).mapHomotopyCategoryPlus.obj N) =
      (asIso (smallEtalePullbackAb (a ≫ b)).rightDerivedFunctorPlusUnith).inv.app N ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso
            (smallEtalePullbackAbCompIso a b)).inv.app N) :=
  have (U V : Scheme.{u}) (f : U ⟶ V) :
      IsIso (smallEtalePullbackAb f).rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso _
  Functor.rightDerivedFunctorPlusCompIsoOfExact_inv_app (smallEtalePullbackAb b)
    (smallEtalePullbackAb a) (smallEtalePullbackAb (a ≫ b))
    (smallEtalePullbackAbCompIso a b) N

end PullbackComp

end Stacks.EtaleCohomology

end
