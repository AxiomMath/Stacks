module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveResolutionDerived
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCechOnUnion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCechCohomologyOnUnion

/-!
# The two models of derived global sections on an open subspace

Tag 08C1 represents derived global sections of an unbounded complex of modules on a space by
the global sections of the functorial K-injective resolution of Tag 079P, with values lifted to
the universe of the index type of the covering.  The rest of this development uses instead the
total right derived functor of the sections functor.  On an open subspace of a space the two
agree: the universe lift is trivial, and a right derived functor is computed by the functorial
K-injective resolution.

This is the identification that lets the Čech comparison map of Tag 08C1 be read as a map into
the derived sections of Tag 0D5V, which is what the Koszul comparison map of Tag 08DC is stated
against.

## Main definitions

* `Koszul.DerivedSystem.uliftAddCommGrpIso` is the identification of the universe lift on
  abelian groups with the identity functor.
* `Koszul.DerivedSystem.ordinarySectionsIso` identifies the ordinary global-sections functor of
  Tag 08C1 on an open subspace with sections over the whole subspace.
* `Koszul.DerivedSystem.unboundedDerivedSectionsIso` identifies the Čech-theoretic model of
  derived global sections on an open subspace with the total right derived functor of sections.

## Implementation notes

The sheaf of rings on the open subspace is spelled `resRing U 𝒪_X` rather than
`(U.toScheme).ringCatSheaf`, although the two are the same object: instance search does not see
through the second spelling to the first, so a statement mixing them cannot have its
zero-morphism structure synthesised.  The identifications with the Čech side of this
development, which uses the scheme's own structure sheaf, are left to unification at the point
of use.

## References

* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace

universe u

namespace Koszul.DerivedSystem

attribute [local instance] HasDerivedCategory.standard

/-! ### Undoing the universe lift -/

/-- The universe lift on abelian groups, in the case of a trivial lift, is the identity. -/
public def uliftAddCommGrpIso : AddCommGrpCat.uliftFunctor.{u, u} ≅ 𝟭 AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ ↦ AddEquiv.ulift.toAddCommGrpIso) (by intros; rfl)

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)

/-- Global sections on an open subspace preserve zero morphisms. -/
public instance sectionsOnOpenSubspace_preservesZeroMorphisms :
    (sectionsOnOpenSubspace O U).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ rfl⟩

/-- Reading a module on an open subspace as an abelian presheaf, taking its sections over the
whole subspace and lifting the universe preserves zero morphisms. -/
public instance presheafSectionsUlift_preservesZeroMorphisms :
    ((SheafOfModules.forget (resRing U O) ⋙
        PresheafOfModules.toPresheaf (resRing U O).obj) ⋙
      ((CategoryTheory.evaluation (Opens (Usp U))ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) ⋙
        AddCommGrpCat.uliftFunctor.{u, u})).PreservesZeroMorphisms :=
  ⟨fun M N ↦ (congrArg ((CategoryTheory.evaluation (Opens (Usp U))ᵒᵖ
      AddCommGrpCat.{u}).obj (op ⊤) ⋙ AddCommGrpCat.uliftFunctor.{u, u}).map
    (Functor.map_zero (SheafOfModules.forget (resRing U O) ⋙
      PresheafOfModules.toPresheaf (resRing U O).obj) M N)).trans
    (Functor.map_zero _ _ _)⟩

/-! ### The two models of derived global sections -/

/-- **The ordinary global-sections complex of Tag 08C1 on an open subspace is the group of
sections over the whole subspace.**  The only difference is the universe lift, which is trivial
here. -/
public def ordinarySectionsIso :
    (SheafOfModules.forget (resRing U O) ⋙
          PresheafOfModules.toPresheaf (resRing U O).obj) ⋙
        ((CategoryTheory.evaluation (Opens (Usp U))ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) ⋙
          AddCommGrpCat.uliftFunctor.{u, u}) ≅
      sectionsOnOpenSubspace O U :=
  NatIso.ofComponents (fun _ ↦ AddEquiv.ulift.toAddCommGrpIso) (by intros; rfl)

/-- The same identification, applied degreewise to a complex. -/
public def ordinarySectionsComplexIso :
    ((SheafOfModules.forget (resRing U O) ⋙
          PresheafOfModules.toPresheaf (resRing U O).obj) ⋙
        ((CategoryTheory.evaluation (Opens (Usp U))ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) ⋙
          AddCommGrpCat.uliftFunctor.{u, u})).mapHomologicalComplex (up ℤ) ≅
      (sectionsOnOpenSubspace O U).mapHomologicalComplex (up ℤ) :=
  NatIso.mapHomologicalComplex (ordinarySectionsIso O U) (up ℤ)

/-- **The Čech-theoretic model of derived global sections on an open subspace is the total
right derived functor of sections.**  Tag 08C1 represents `RΓ(U, -)` by the global sections of
the functorial K-injective resolution of Tag 079P, which computes the right derived functor. -/
public def unboundedDerivedSectionsIso :
    Stacks.Cech.unboundedDerivedGlobalSectionsFunctor (Usp U) (resRing U O) ≅
      DerivedCategory.Q ⋙ derivedSectionsOnOpenSubspace O U :=
  Functor.isoWhiskerLeft (Stacks.Cech.kInjectiveResolution (Usp U) (resRing U O))
      (Functor.isoWhiskerRight (ordinarySectionsComplexIso O U) DerivedCategory.Q) ≪≫
    Stacks.Cohomology.ResolutionDerived.resolutionDerivedIso
      (sectionsOnOpenSubspace O U) (derivedSectionsOnOpenSubspace O U)
      ((homotopySectionsOnOpenSubspace O U).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (resRing U O)) (up ℤ)))

/-! ### Restriction to an open subspace on derived categories -/

/-- **Restriction of complexes commutes with the passage to the derived category.** -/
public def restrictComplexDerivedIso :
    (jStar U O).mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ derivedRestriction O U :=
  (jStar U O).mapDerivedCategoryFactors.symm ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Q (derivedRestrictionIso O U).symm

end Koszul.DerivedSystem

end
