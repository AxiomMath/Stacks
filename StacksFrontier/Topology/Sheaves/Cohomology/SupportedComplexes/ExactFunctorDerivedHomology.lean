module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# An exact functor commutes with the cohomology of derived objects

Let `F : C ⥤ D` be an additive functor between abelian categories which preserves finite limits
and finite colimits.  Then `F` applied degreewise to a complex commutes with taking cohomology,
and that comparison descends through the localization `DerivedCategory.Q` to a comparison on
unbounded derived categories.

## Main definitions

* `exactFunctorHomologyIso`: the complex-level comparison
  `F ∘ (-) ⋙ Hⁿ ≅ Hⁿ ⋙ F` for cochain complexes.
* `exactFunctorDerivedHomologyIso`: the same comparison on unbounded derived categories,
  obtained from the complex-level one by the universal property of the localization.

## Implementation notes

These two statements are pure homological algebra: they mention no ringed space and no sheaf.
They are stated here, in a module whose only imports are Mathlib's, so that both the supported
complexes development and the pseudo-coherence development can use one copy.  Previously each
had its own, with identical statements and identical bodies.

The derived-category universes of the source and the target are independent parameters `w₁` and
`w₂`, so a consumer that works at two different models of the derived category can still apply
the comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.SupportedComplexes

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- For an exact functor `F`, applying `F` to a complex degreewise and taking `n`-th homology
agrees with taking `n`-th homology and then applying `F`. -/
noncomputable def exactFunctorHomologyIso
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F :=
  NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso F) (fun φ ↦
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map φ) F)

/-- **An exact functor commutes with the homology of derived objects.** For an exact functor
`F`, the induced functor on unbounded derived categories commutes with the cohomology functors:
`F^D ⋙ Hⁿ ≅ Hⁿ ⋙ F`.

This is `exactFunctorHomologyIso` lifted through the localization `DerivedCategory.Q`. -/
noncomputable def exactFunctorDerivedHomologyIso
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C n ⋙ F)) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor D n) ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors D n) ≪≫
      exactFunctorHomologyIso F n ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n).symm F)

end Stacks.Cohomology.SupportedComplexes

end
