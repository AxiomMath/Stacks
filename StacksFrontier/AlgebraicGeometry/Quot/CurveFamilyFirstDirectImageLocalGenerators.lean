module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFreeOfTerminal
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# Finite local freeness of `R¹f_*𝒪_X` from a covering family

The small étale site of a scheme `U`, read as an algebraic space, has a final object: the
identity chart `AlgebraicGeometry.Space.selfChart`. So a module on it which is finite locally free
in the covering-family sense of Stacks 03DL(2) is finite locally free in the local-generators
sense of Stacks 01C6(2). For a family of curves this turns the étale-local statement of part (2)
of Stacks 0E1J into `AlgebraicGeometry.CurveFamily.HasFiniteLocallyFreeFirstHigherDirectImage`.

## Main results

* `AlgebraicGeometry.Space.isTerminal_selfChart`: the identity chart is a final object.
* `CurveFamily.hasFiniteLocallyFreeFirstHigherDirectImage_of_isFiniteLocallyFreeOnSite`:
  part (2) of Stacks 0E1J from its covering-family form.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The identity chart of a represented presheaf is a final object of its small étale site.**
A chart of `yoneda.obj U` is a morphism to `yoneda.obj U`, so it has exactly one morphism to the
identity chart. -/
noncomputable def Space.isTerminal_selfChart (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : BigFppfOver B S hS) :
    IsTerminal (Space.selfChart B S hS U) :=
  IsTerminal.isTerminalOfObj (ObjectProperty.ι _) _ CostructuredArrow.mkIdTerminal

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Part (2) of Stacks 0E1J from its étale-local form.** If `R¹f_*𝒪_X` is finite locally free
on the small étale site of the base in the covering-family sense of Stacks 03DL(2), then it is
finite locally free in the sense of Stacks 01C6(2). -/
theorem CurveFamily.hasFiniteLocallyFreeFirstHigherDirectImage_of_isFiniteLocallyFreeOnSite
    (X : CurveFamily B hZ)
    (h : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite (X.firstDirectImage B hZ)) :
    X.HasFiniteLocallyFreeFirstHigherDirectImage :=
  have hsh : ∀ Y : (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace X.base).1
        (schemeSpace X.base).2).C,
      HasWeakSheafify ((Space.smallEtaleRingedSite B integerBase hZ (schemeSpace X.base).1
        (schemeSpace X.base).2).J.over Y) AddCommGrpCat.{u} := fun Y =>
    inferInstanceAs (HasWeakSheafify ((Space.SmallEtale.topology B integerBase hZ
      (schemeSpace X.base).1).over
        (show Space.SmallEtale B integerBase hZ (schemeSpace X.base).1 from Y)) AddCommGrpCat.{u})
  have hlb : ∀ Y : (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace X.base).1
        (schemeSpace X.base).2).C,
      ((Space.smallEtaleRingedSite B integerBase hZ (schemeSpace X.base).1
        (schemeSpace X.base).2).J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u} := fun Y =>
    inferInstanceAs (GrothendieckTopology.WEqualsLocallyBijective
      ((Space.SmallEtale.topology B integerBase hZ (schemeSpace X.base).1).over
        (show Space.SmallEtale B integerBase hZ (schemeSpace X.base).1 from Y)) AddCommGrpCat.{u})
  Stacks.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite (hsh := hsh) (hlb := hlb)
    (Space.isTerminal_selfChart B integerBase hZ X.base) (X.firstDirectImage B hZ) h

end AlgebraicGeometry

end
