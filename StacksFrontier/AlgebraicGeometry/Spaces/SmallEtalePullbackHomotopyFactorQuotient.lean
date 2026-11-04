module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroUnderivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived
public import StacksFrontier.CategoryTheory.Functor.Derived.ComparisonSquareChaseHomotopy

/-!
# The degreewise contraction of pullbacks on homotopy categories is the one on complexes

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces and a factorisation `f ≫ g = k`,
`AlgebraicGeometry.Space.smallEtalePullbackMapHomotopyFactorIso` identifies `g^* ⋙ f^*` with `k^*`
on the unbounded homotopy categories of complexes of modules.  At the image of a complex it is
the image under `CategoryTheory.HomotopyCategory.quotient` of the degreewise contraction
`AlgebraicGeometry.Space.smallEtaleToposPullbackFactorIso` of the inverse images of modules.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleToposPullbackFactorIso`: the contraction
  `g^* ⋙ f^* ≅ k^*` of inverse images of modules attached to a factorisation `f ≫ g = k`.

## Main results

* `AlgebraicGeometry.Space.smallEtalePullbackMapHomotopyFactorIso_eq`: the identification on
  homotopy categories is the comparison of induced functors of the degreewise contraction.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS}

/-- Inverse image of modules along a composite of morphisms of small étale ringed topoi is
additive. -/
local instance additive_pullbackModules_comp_toposPullback (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS g)
      (smallEtaleRingedToposHom B S hS f)).toModulesHom.pullbackModules).Additive :=
  RingedToposHom.pullbackModules_additive
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f))

/-- **The contraction `g^* ⋙ f^* ≅ k^*` of inverse images of modules** attached to a
factorisation `f ≫ g = k` of morphisms of algebraic spaces:
`AlgebraicGeometry.Space.smallEtaleToposPullbackCompIso`, followed by the renaming of the inverse
image along the factorisation. -/
def smallEtaleToposPullbackFactorIso (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) :
    (smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules ⋙
        (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules ≅
      (smallEtaleRingedToposHom B S hS k).toModulesHom.pullbackModules :=
  smallEtaleToposPullbackCompIso f g ≪≫
    eqToIso (congrArg (fun m : X ⟶ Z ↦
      (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules) hk)

/-- `AlgebraicGeometry.Space.smallEtaleToposPullbackCompIso` is, by definition, the comparison of
the inverse image of a composite of morphisms of ringed topoi with the composite of the inverse
images, followed by the inverse-image comparison of the 2-isomorphism of Stacks 03G8. -/
theorem smallEtaleToposPullbackCompIso_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g)).symm ≪≫
      (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso =
      smallEtaleToposPullbackCompIso f g :=
  rfl

/-- **The identification `g^* ⋙ f^* ≅ k^*` on homotopy categories is the comparison of induced
functors of the degreewise contraction.**  This is
`StacksDraft.ComparisonSquare.factorIso_three_eq` at the family of inverse images of modules. -/
theorem smallEtalePullbackMapHomotopyFactorIso_eq (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (hk : f ≫ g = k) :
    smallEtalePullbackMapHomotopyFactorIso f g k hk =
      Functor.mapHomotopyCategoryCompIso (smallEtaleToposPullbackFactorIso f g k hk)
        (ComplexShape.up ℤ) :=
  StacksDraft.ComparisonSquare.factorIso_three_eq
    (fun m : X ⟶ Z => (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules)
    (ComplexShape.up ℤ)
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g)).symm
    (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso
    (smallEtaleToposPullbackCompIso f g) (smallEtaleToposPullbackCompIso_eq f g) hk

end AlgebraicGeometry.Space

end
