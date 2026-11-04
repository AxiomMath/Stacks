module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquare
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules

/-!
# The derived transformation of a square is compatible with the shift

For a natural transformation `c : F ⋙ E' ⟶ E ⋙ F'` with `E`, `E'` exact, the derived
transformation `Stacks.Homology.DerivedSquare.derivedSquare c :
RF ⋙ E'.mapDerivedCategory ⟶ E.mapDerivedCategory ⋙ RF'` commutes with the shift, for the
canonical commutation of the two composite functors with the shift. It is the descent, along the
right derived functor `RF ⋙ E'.mapDerivedCategory` whose unit commutes with the shift, of a
transformation commuting with the shift, and such a descent inherits the compatibility
(`Stacks.Triangulated.natTransCommShift_rightDerivedDesc`).

This is what the passage from sheaves to bounded below complexes
(`CategoryTheory.NatTrans.isIso_app_of_isGE`) and dimension shifting
(`Stacks.Triangulated.isIso_app_of_dimensionShifting`) ask of a base change map.

## Main results

* `Stacks.Homology.DerivedSquare.totalRightDerived_isTriangulated`: the total right derived
  functor of an additive functor out of a Grothendieck abelian category is triangulated.
* `Stacks.Homology.DerivedSquare.natTransCommShift_derivedSquare`: the compatibility.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteCohomologyPresheaf (totalRightDerivedCompUnit
  isRightDerivedFunctor_totalRightDerived_comp)

universe wA wA' wB wB' vA vA' vB vB' uA uA' uB uB' wG

namespace Stacks.Homology.DerivedSquare

variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
  [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  {F : A ⥤ B} [F.Additive] {F' : A' ⥤ B'} [F'.Additive]
  [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  {E : A ⥤ A'} [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  {E' : B ⥤ B'} [E'.Additive] [PreservesFiniteLimits E'] [PreservesFiniteColimits E']

omit [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B'] in
/-- **The total right derived functor is triangulated**, for its canonical commutation with the
shift: it is a right derived functor of the triangulated functor `K(G) ⋙ Q_h`, and every complex
of a Grothendieck abelian category has a K-injective resolution. -/
instance totalRightDerived_isTriangulated (G : A ⥤ B) [G.Additive]
    [(G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    (totalRightDerived G).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    Stacks.Cohomology.Localization.enoughKInjectives
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (totalRightDerived G)
    (totalRightDerivedUnit G)

/-- The transformation that `derivedSquare` descends commutes with the shift: each of its
factors does. -/
instance natTransCommShift_derivedSquareBeta (c : F ⋙ E' ⟶ E ⋙ F') :
    NatTrans.CommShift (derivedSquareBeta c) ℤ := by
  dsimp only [derivedSquareBeta]
  infer_instance

/-- **The derived transformation of a square commutes with the shift.** -/
instance natTransCommShift_derivedSquare (c : F ⋙ E' ⟶ E ⋙ F') :
    NatTrans.CommShift (derivedSquare c) ℤ := by
  have := isRightDerivedFunctor_totalRightDerived_comp
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) E'.mapDerivedCategory
  have : NatTrans.CommShift (totalRightDerivedCompUnit
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      E'.mapDerivedCategory) ℤ := by
    dsimp only [totalRightDerivedCompUnit]
    infer_instance
  exact Stacks.Triangulated.natTransCommShift_rightDerivedDesc _ _ _ ℤ _ _

end Stacks.Homology.DerivedSquare

end
