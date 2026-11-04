module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackCupProductDerived

/-!
# Pullback in de Rham cohomology is semilinear

For a commutative square `g' ≫ f = f' ≫ g` of schemes the pullback
`H^m_{dR}(X/S) ⟶ H^m_{dR}(X'/S')` of Section 0FL6 is semilinear along the map
`Γ(X, f^{-1}𝒪_S) ⟶ Γ(X', f'^{-1}𝒪_{S'})` of global sections of the base ring sheaves.

## References

* [Stacks Project, Section 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)

universe u

namespace Stacks.DeRhamBaseChange

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- **Pullback is semilinear**: `g'^*(a • z) = a' • g'^*z` for `a` a global section of
`f^{-1}𝒪_S` and `a'` its image in `Γ(X', f'^{-1}𝒪_{S'})`. -/
theorem deRhamPullbackSquare_smul (m : ℤ)
    (a : (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj.obj (op ⊤))
    (z : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m) :
    deRhamPullbackSquare g' f' f g w m (a • z) =
      (show (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf)).obj.obj (op ⊤) from
        (Stacks.Cohomology.LerayCupPairing.globalRingHom
          (inverseImageBaseMap g' f' f g w)).hom a) • deRhamPullbackSquare g' f' f g w m z := by
  rw [deRhamPullbackSquare_eq_lerayMap, deRhamPullbackSquare_eq_lerayMap]
  refine (congrArg (Stacks.Cohomology.LerayCupPairing.lerayMap (inverseImageBaseMap g' f' f g w)
    (DerivedCategory.Q.obj (deRhamComplexModules f')) m)
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) m).map
      ((baseSections (inverseImageBase f)).map
        (deRhamComparisonQ g' f' f g w))).hom.map_smul
          (a : baseRing (inverseImageBase f)) z)).trans ?_
  exact (Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso (inverseImageBaseMap g' f' f g w)
    (DerivedCategory.Q.obj (deRhamComplexModules f')) m).hom.hom.map_smul a _

end Stacks.DeRhamBaseChange
