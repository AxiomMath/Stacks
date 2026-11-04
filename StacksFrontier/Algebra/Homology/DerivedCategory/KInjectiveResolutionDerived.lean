module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCechIdentification

/-!
# A right derived functor is computed by the functorial K-injective resolution

Let `F : C ⥤ D` be an additive functor between abelian categories with `C` Grothendieck
abelian, and let `RF` be a total right derived functor of `F` on unbounded derived categories,
with structure map `α`.  The functorial K-injective resolution of Tag 079P then computes `RF`:
there is a canonical isomorphism

`kInjectiveResolution ⋙ F.mapHomologicalComplex ⋙ Q ≅ Q ⋙ RF`

natural in the complex.  Both sides are functors on complexes, so this is the identification
that lets a derived functor defined as a total right derived functor be compared with one
defined by applying `F` termwise to a chosen K-injective resolution.

## Main definitions

* `Stacks.Cohomology.ResolutionDerived.derivedComplexComparison`: the canonical map from the
  termwise image of a complex to its right derived functor.
* `Stacks.Cohomology.ResolutionDerived.resolutionDerivedIso`: the isomorphism above.

## Main results

* `Stacks.Koszul.Cech.derivedComplexComparison_isIso`: the comparison map is
  invertible on a K-injective complex.

## Implementation notes

The comparison map is the structure map `α` of the derived functor, transported from the
homotopy category to complexes along the factorisations of the localisation functors.  It is
invertible at a K-injective complex by
`Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective`, and the resolution inclusion
becomes invertible in the derived category because it is a quasi-isomorphism; composing the two
gives the isomorphism.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe w w' wG v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.ResolutionDerived

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)

/-- The structure map of a right derived functor, read on complexes: the canonical map from
the image of a complex under `F`, applied termwise, to its right derived functor. -/
public def derivedComplexComparison :
    F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF :=
  (Functor.isoWhiskerLeft (F.mapHomologicalComplex (up ℤ))
    (DerivedCategory.quotientCompQhIso D)).inv ≫
  (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (up ℤ)) DerivedCategory.Qh).inv ≫
  Functor.whiskerLeft (HomotopyCategory.quotient C (up ℤ)) α ≫
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) RF).hom

variable [IsGrothendieckAbelian.{wG} C]
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (up ℤ))]

/-- **A right derived functor is computed by the functorial K-injective resolution.** -/
public def resolutionDerivedIso :
    Stacks.Injectives.kInjectiveResolutionFunctor C ⋙
      F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF := by
  let β := Functor.whiskerLeft (Stacks.Injectives.kInjectiveResolutionFunctor C)
    (derivedComplexComparison F RF α)
  letI : IsIso β := by
    have : ∀ K, IsIso (β.app K) := fun K ↦
      Stacks.Koszul.Cech.derivedComplexComparison_isIso F RF α _
    exact NatIso.isIso_of_isIso_app β
  let γ := Functor.whiskerRight (Stacks.Injectives.kInjectiveResolutionInclusion C)
    (DerivedCategory.Q ⋙ RF)
  letI : IsIso γ := by
    have : ∀ K, IsIso (γ.app K) := by
      intro K
      change IsIso (RF.map (DerivedCategory.Q.map
        ((Stacks.Injectives.kInjectiveResolutionInclusion C).app K)))
      infer_instance
    exact NatIso.isIso_of_isIso_app γ
  exact asIso β ≪≫ (asIso γ).symm

end Stacks.Cohomology.ResolutionDerived

end
