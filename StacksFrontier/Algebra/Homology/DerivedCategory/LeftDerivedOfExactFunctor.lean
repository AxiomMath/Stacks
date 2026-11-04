module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# A total left derived functor of an exact functor is the functor it induces on derived
categories

Let `F : A ⥤ B` be an additive functor between abelian categories with derived categories, and
suppose a total left derived functor of `F` — a functor `LF : D(A) ⥤ D(B)` together with a
comparison `α : Q_h ⋙ LF ⟶ K(F) ⋙ Q_h` exhibiting `LF` as a left derived functor of
`K(F) ⋙ Q_h` with respect to the quasi-isomorphisms — has been constructed.  If `F` is
isomorphic to an *exact* functor `G`, then no derivation happened: `LF` is `G.mapDerivedCategory`,
the functor `D(A) ⥤ D(B)` that `G` induces degreewise.

The reason is that for an exact `G` the comparison
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` is an *isomorphism*, so
`G.mapDerivedCategory` is itself a left derived functor of `K(G) ⋙ Q_h`, trivially; and a left
derived functor is unique up to a unique isomorphism.

This is the statement that identifies a derived functor built by resolutions with the
degreewise one whenever the functor being derived turns out to be exact — for instance the
derived pullback along a morphism of ringed topoi whose pullback of sheaves of modules is
exact, as happens for a localization morphism, where the derived pullback is restriction to
the localized site.

## Main results

* `Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso`: a total left derived functor of a
  functor isomorphic to an exact functor `G` is `G.mapDerivedCategory`.
* `Stacks.Homology.leftDerivedIsoMapDerivedCategory`: the same for an exact functor itself.
* `Stacks.Homology.isLE_mapDerivedCategory_obj`: an exact functor's induced functor on derived
  categories preserves the cohomological bound `IsLE n`, since it preserves a strictly bounded
  representative degreewise.

## Implementation notes

The isomorphism `e : F ≅ G` is carried rather than assumed to be the identity because the
functor whose derived functor was built is in practice not the exact one itself but a functor
isomorphic to it: the comparison identifying it with the exact functor is the mathematical
input, and it enters here. `Stacks.Homology.mapHomotopyCategoryIso` transports it to the
homotopy categories, which is where the universal property of the left derived functor
consumes it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Homology

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- **A total left derived functor of a functor isomorphic to an exact functor is the functor
the exact one induces degreewise.**  If `LF` is a left derived functor of
`K(F) ⋙ Q_h` with comparison `α`, and `e : F ≅ G` with `G` exact, then
`LF ≅ G.mapDerivedCategory`.

For an exact `G` the comparison `G.mapDerivedCategoryFactorsh` is invertible, so
`G.mapDerivedCategory` is a left derived functor of `K(G) ⋙ Q_h` and hence, transported along
`e`, of `K(F) ⋙ Q_h`; uniqueness of left derived functors does the rest. -/
def leftDerivedIsoMapDerivedCategoryOfIso
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (e : F ≅ G) :
    LF ≅ G.mapDerivedCategory :=
  let η : DerivedCategory.Qh ⋙ G.mapDerivedCategory ≅
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
    G.mapDerivedCategoryFactorsh ≪≫
      Functor.isoWhiskerRight (mapHomotopyCategoryIso e.symm (ComplexShape.up ℤ))
        DerivedCategory.Qh
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G.mapDerivedCategory η
  Functor.leftDerivedUnique G.mapDerivedCategory LF α η.hom
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- **A total left derived functor of an exact functor is the functor it induces degreewise.**
This is `Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso` at the identity comparison. -/
def leftDerivedIsoMapDerivedCategory
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    LF ≅ F.mapDerivedCategory :=
  leftDerivedIsoMapDerivedCategoryOfIso F F LF α (Iso.refl F)

/-- **An exact functor preserves the cohomological bound `IsLE n` on derived categories.** The
cohomology of the image is the image of the cohomology, by
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, and an additive functor carries a zero
object to a zero object. -/
theorem isLE_mapDerivedCategory_obj
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : DerivedCategory A) (n : ℤ) [DerivedCategory.IsLE E n] :
    DerivedCategory.IsLE (F.mapDerivedCategory.obj E) n := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact (F.map_isZero (DerivedCategory.isZero_of_isLE E n i hi)).of_iso
    ((F.mapDerivedCategoryHomologyIso i).app E)

end Stacks.Homology

end
