module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapConstruction
public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.Homology.KFlat.RestrictFlat

/-!
# The comparison of Stacks 065Z through a resolution over a flat algebra

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a commutative square of commutative rings, `M` a
K-flat complex of `A`-modules, `F` an `R`-algebra through which `R → A` factors, and
`p : P ⟶ M` a quasi-isomorphism of complexes of `F`-modules from a K-flat `P`.  The comparison
`τ : M ⊗ᴸ_R R' ⟶ M ⊗ᴸ_A A'` of Stacks 065Z, precomposed with `p ⊗ᴸ_R R'`, is the class of the
map of complexes `P ⊗_R R' ⟶ M ⊗_R R' ⟶ M ⊗_A A'`, read through the comparisons of derived with
degreewise extension of scalars.

## Main results

* `RingTheory.TorIndependence.squareDerivedComparison_honest`.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A']
  [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- The pinning equation of the comparison, at a complex. -/
theorem squareDerivedComparison_app_comp_counit (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app
          (DerivedCategory.Q.obj M) ≫
        (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A A')).comparison.app M) ≫
        (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R R')).functor.map
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.hom.app M) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R R')).comparison.app
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (@derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
            R A R' A' _ _ _ _ _ _ _ _ (algebraMap R A) (algebraMap R R') (algebraMap A A')
            (algebraMap R' A') baseChangeSquare
            (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap R R')).functor
            (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A A')).functor
            (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap R R')).comparison
            (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A A')).comparison
            (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap R R')).isLeftDerived
            (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A A')).isLeftDerived).1 (ComplexShape.up ℤ)).app M) :=
  @derivedBaseChangeComparison_snd_app_comp_counit.{u, u, u, u, u} R A R' A' _ _ _ _ _ _ _ _
    (algebraMap R A) (algebraMap R R') (algebraMap A A') (algebraMap R' A') _ _ baseChangeSquare
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).isLeftDerived
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).isLeftDerived M

end RingTheory.TorIndependence
