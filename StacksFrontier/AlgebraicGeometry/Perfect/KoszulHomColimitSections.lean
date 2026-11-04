module

public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulRestrictedStructureSheaf
public import StacksFrontier.Homology.DerivedCategory.HomColimit
public import StacksFrontier.Homology.HomologyColimit

/-!
# The Koszul Hom complexes compute cohomology over a union of basic opens

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`,
let `X = Spec A` and let `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`.  For a complex `M^•` of `A`-modules the
filtered colimit over the exponent of the degree-zero cohomology of the Koszul Hom complexes is
the degree-zero hypercohomology of `M̃^•` over `U`:

`colimₑ H⁰(Hom^•(I^•(f^e), M^•)) ≅ H⁰(U, M̃^•)`,

naturally in `M^•`.  This is Tag 08D1 followed by Tag 08D2, with the colimit moved past the
cohomology.

## Main definitions

* `Koszul.DerivedSystem.koszulHomStageFunctor` is the `ℕ`-diagram
  `e ↦ H⁰(Hom^•(I^•(f^{e+1}), M^•))`, functorial in `M^•`.

## Main results

* `Koszul.DerivedSystem.koszulHomColimitHomologyIso`: the colimit of that diagram is the
  degree-zero cohomology of the total alternating Čech complex.
* `Koszul.DerivedSystem.koszulHomSectionsIso`: composing with
  `Koszul.DerivedSystem.alternatingCechTotalDerivedSectionsIso`, it is `H⁰(U, M̃^•)`.

## Implementation notes

Taking the colimit commutes with taking degree-zero cohomology because filtered colimits of
abelian groups are exact: the degree-zero cohomology of a complex is the homology of its short
complex in that degree, and both the passage to the short complex and the homology of a short
complex commute with exact colimits.  This is
`Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor`, and the exactness of the
`ℕ`-indexed colimits of abelian groups is
`Stacks.MappingTelescope.hasExactColimitsOfShape_addCommGrpCat`.

The Koszul Hom complexes are complexes of `A`-modules, and Tag 08D1 compares their colimit with
the total alternating Čech complex after forgetting the module structure; the forgetful functor
also preserves the colimit, so the two moves commute in either order.

## References

* [Stacks Project, Tag 08D1](https://stacks.math.columbia.edu/tag/08D1)
* [Stacks Project, Tag 08D2](https://stacks.math.columbia.edu/tag/08D2)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open scoped Stacks.MappingTelescope

universe u

namespace Koszul.DerivedSystem

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : CommRingCat.{u}} {r : ℕ} (f : Fin r → A)

/-- The degree-zero cohomology of the Koszul Hom complexes, as an `ℕ`-diagram depending
functorially on the coefficient complex. -/
public abbrev koszulHomStageFunctor :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ (ℕ ⥤ AddCommGrpCat.{u}) :=
  Koszul.koszulHomDiagramFunctor f ⋙ (Functor.whiskeringRight ℕ _ _).obj
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (up ℤ) 0)

/-- **The colimit of the degree-zero cohomologies of the Koszul Hom complexes is the degree-zero
cohomology of the total alternating Čech complex.** -/
public def koszulHomColimitHomologyIso :
    koszulHomStageFunctor f ⋙ colim ≅
      Koszul.alternatingCechTotalFunctor f ⋙ DerivedCategory.Q ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0 := by
  letI G := (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (up ℤ) 0
  haveI : PreservesColimitsOfShape ℕ G := by
    have : PreservesColimitsOfShape ℕ
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (up ℤ) 0) :=
      Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor _ _
    infer_instance
  exact Functor.isoWhiskerLeft (Koszul.koszulHomDiagramFunctor f)
      (preservesColimitNatIso (J := ℕ) G).symm ≪≫
    Functor.isoWhiskerRight (Koszul.koszulHomColimitIsoAlternatingCechTotal f)
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (up ℤ) 0) ≪≫
    Functor.isoWhiskerLeft (Koszul.alternatingCechTotalFunctor f)
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).symm

/-- **The Koszul Hom complexes compute `H⁰(U, -)` on the associated sheaves.**  For a complex
`M^•` of `A`-modules the filtered colimit over the exponent of the degree-zero cohomology of
`Hom^•(I^•(f^e), M^•)` is the degree-zero hypercohomology of `M̃^•` over
`U = D(f₁) ∪ ⋯ ∪ D(f_r)`, naturally in `M^•`. -/
public def koszulHomSectionsIso :
    koszulHomStageFunctor f ⋙ colim ≅
      DerivedCategory.Q ⋙ derivedSheafify A ⋙ sectionsOnUnion f :=
  koszulHomColimitHomologyIso f ≪≫ alternatingCechTotalDerivedSectionsIso f

end Koszul.DerivedSystem

end
