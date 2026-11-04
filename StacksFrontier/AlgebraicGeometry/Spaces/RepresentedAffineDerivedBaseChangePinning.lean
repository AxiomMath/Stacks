module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedExtendScalarsContraction
public import StacksFrontier.CategoryTheory.Functor.Derived.ComparisonSquareChase

/-!
# The pinning equation of the affine derived base change morphism

`AlgebraicGeometry.Space.representedAffineDerivedBaseChangeHom` is produced by the universal
property of `Φ_{R'} ∘ (- ⊗^𝐋_R R')` as a total left derived functor, so it is characterised by one
equation: composed with the comparison of that left derived functor, it is the comparison
`AlgebraicGeometry.Space.representedAffineBaseChangeComparison` on complexes.  This file records
that equation with every whiskering evaluated, which is the shape a chase of two base change
squares consumes.

## Main results

* `AlgebraicGeometry.Space.representedAffineDerivedBaseChangeHom_fac`: the pinning equation.

## Implementation notes

`CategoryTheory.Functor.leftDerived_fac_app` produces the equation with the comparison datum of
the left derived functor — an inverse associator followed by a whiskering — left unevaluated, and
with the factorisation of the derived associated module appearing on the wrong side.  Both are
rearranged on variables, by
`StacksDraft.ComparisonSquare.associator_inv_comp_whiskerRight_app` and
`StacksDraft.ComparisonSquare.comp_cancel_right'`; performed on the concrete goal, whose objects
are derived categories of modules on algebraic spaces, the `isDefEq` checks a `simp` would run
exhaust the heartbeat budget.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.DerivedExtensionScalars

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

attribute [local instance] additive_extendScalars_ofRingHom
  additive_pullbackModules_ofRepresentedSpaceMap additive_associated_ofAffineRepresentable

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

/-- **The pinning equation of the affine derived base change morphism, with every whiskering
evaluated.**  The base change morphism at `Q M`, followed by the associated module of the
comparison of derived extension of scalars and the factorisation of the derived associated module,
is the derived pullback of that factorisation, then the comparison `Lg^* ⟶ g^*` of Stacks 06YY,
then the localization of the degreewise pullback isomorphism.

This is `CategoryTheory.Functor.leftDerived_fac_app` for
`AlgebraicGeometry.Space.representedAffineDerivedBaseChangeHom`, read through
`AlgebraicGeometry.Space.representedAffineBaseChangeComparison_app`. -/
theorem representedAffineDerivedBaseChangeHom_fac
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineDerivedBaseChangeHom B S hS g).app (DerivedCategory.Q.obj M) ≫
        (representedAffineDerivedAssociated B S hS U').map
          ((extendScalarsComparison (representedAffineCommRingCatHom B S hS g).hom).app M) ≫
        (representedAffineDerivedAssociatedFactors B S hS U').hom.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M) =
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedAffineDerivedAssociatedFactors B S hS U).hom.app M) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS
            (representedSpaceMap B S hS g)).app
          ((representedAffineHomotopyAssociated B S hS U).obj M) ≫
        DerivedCategory.Qh.map ((representedAffineHomotopyPullbackIso B S hS g).hom.app M) := by
  refine StacksDraft.ComparisonSquare.comp_cancel_right'
    ((representedAffineDerivedAssociatedFactors B S hS U').inv_hom_id_app _) ?_
  have hfac := Functor.leftDerived_fac_app _ ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (representedAffineDerivedExtension B S hS g).comparison
        (representedAffineDerivedAssociated B S hS U'))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
    (representedAffineBaseChangeComparison B S hS g) M
  rw [representedAffineBaseChangeComparison_app] at hfac
  refine Eq.trans ?_ hfac
  exact congrArg
    (fun y => (representedAffineDerivedBaseChangeHom B S hS g).app (DerivedCategory.Q.obj M) ≫ y)
    (StacksDraft.ComparisonSquare.associator_inv_comp_whiskerRight_app DerivedCategory.Q
      (representedAffineDerivedExtension B S hS g).comparison
      (representedAffineDerivedAssociated B S hS U') M).symm

end AlgebraicGeometry.Space

end
