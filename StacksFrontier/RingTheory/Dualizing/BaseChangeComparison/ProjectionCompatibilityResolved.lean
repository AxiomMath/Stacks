module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonResolved
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ResolvedProjectionFormulaEq
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChange

/-!
# The compatibility of the two projection formulas of [stacks 0E2A]

The two algebra actions `Dualizing.algebraActionLeft` and `Dualizing.algebraActionRight` of
[stacks 0E2A] agree for every pair of models of the two derived extensions of scalars, so the two
projection formulas are compatible at every object of `D(R)`, in each of the forms listed below.

## Main results

* `Dualizing.algebraActionLeft_eq_algebraActionRight` — the two algebra actions agree.
* `Dualizing.projectionFormulaCompatibility` — `Dualizing.ProjectionFormulaCompatibility` at every
  object, for every pair of models.
* `Dualizing.projectionFormulaCompatibilityCanonical` — the same at the canonical models.
* `Dualizing.kFlatAlgebraActionEq` — `Dualizing.KFlatAlgebraActionEq`.
* `Dualizing.PolynomialPresentation.projectionCompatibility` —
  `Dualizing.PolynomialPresentation.ProjectionCompatibility` for every polynomial presentation.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

universe uR uA uRp v

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]


include hTor hf hi in
/-- **The two algebra actions of [stacks 0E2A] agree.**  For every pair of models of the derived
extensions of scalars along `R → A` and along `R' → A ⊗_R R'`, the `A ⊗_R R'`-action transported by
the comparison of [stacks 0661] is the derived base change of the `A`-action. -/
theorem algebraActionLeft_eq_algebraActionRight :
    algebraActionLeft hTor baseChangeR comparisonR hR baseChangeA comparisonA hA Fi alphai =
      algebraActionRight hTor baseChangeR comparisonR hR baseChangeA comparisonA hA Ff alphaf := by
  obtain ⟨P, p, hP, -, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{uR, max v uA uRp}
    (algebraComplex.{max v uRp} (algebraMap R A))
  have := hp
  have hP' := kFlat_baseChangeResolution.{uR, uA, uRp, v} (R' := R') P hP
  have := quasiIso_baseChangeResolution'.{uR, uA, uRp, v} hTor baseChangeR comparisonR
    baseChangeA comparisonA P p hP
  have hpf := derivedExtendRestrictScalarsTensorIso_eq_resolvedProjectionFormula.{max v uRp}
    (algebraMap R A) Ff alphaf P hP p
  have hpf' := derivedExtendRestrictScalarsTensorIso_eq_resolvedProjectionFormula.{max v uR}
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai
    (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) hP'
    (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P p)
  ext W
  have h := algebraAction_app_eq_of_tensorComparisonCompatibilityOf hTor baseChangeR comparisonR
    baseChangeA comparisonA Ff alphaf Fi alphai _ _ W
    (tensorComparisonCompatibilityOf_resolved.{uR, uA, uRp, v} hTor baseChangeR comparisonR
      baseChangeA comparisonA Ff alphaf Fi alphai P hP p hP' _)
  rw [← hpf, ← hpf'] at h
  exact h

include hTor hf hi in
/-- **The compatibility of the two projection formulas**,
`Dualizing.ProjectionFormulaCompatibility`, at every object of `D(R)` and for every pair of models
of the two derived extensions of scalars. -/
theorem projectionFormulaCompatibility (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ProjectionFormulaCompatibility hTor baseChangeR comparisonR hR baseChangeA comparisonA hA
      Ff alphaf Fi alphai K :=
  projectionFormulaCompatibility_of_algebraAction hTor baseChangeR comparisonR hR baseChangeA
    comparisonA hA Ff alphaf Fi alphai
    (algebraActionLeft_eq_algebraActionRight.{uR, uA, uRp, v} hTor baseChangeR comparisonR
      baseChangeA comparisonA Ff alphaf Fi alphai) K


include hTor in
/-- **The compatibility of the two projection formulas at the canonical models**,
`Dualizing.ProjectionFormulaCompatibilityCanonical`, at every object of `D(R)`. -/
theorem projectionFormulaCompatibilityCanonical
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ProjectionFormulaCompatibilityCanonical hTor baseChangeR comparisonR hR baseChangeA
      comparisonA hA K :=
  projectionFormulaCompatibility.{uR, uA, uRp, v} hTor baseChangeR comparisonR baseChangeA
    comparisonA
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
    (hf := (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived)
    (hi := (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived) K

end Dualizing

namespace Dualizing

universe u

/-- **`Dualizing.KFlatAlgebraActionEq` holds**: at every Tor-independent square of rings in one
universe and every pair of models of the two derived extensions of scalars, the two algebra actions
agree. -/
theorem kFlatAlgebraActionEq : KFlatAlgebraActionEq.{u} := by
  intro B C B' _ _ _ _ _ hTor bc cmp ld bcC cmpC ldC X _
  have := ld
  have := ldC
  exact congrArg (fun t => NatTrans.app t (DerivedCategory.Q.obj X))
    (algebraActionLeft_eq_algebraActionRight.{u, u, u, 0} hTor bc cmp bcC cmpC
      (canonicalExtensionModel.{u, u, u} B C).functor
      (canonicalExtensionModel.{u, u, u} B C).comparison
      (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').functor
      (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').comparison
      (hf := (canonicalExtensionModel.{u, u, u} B C).isLeftDerived)
      (hi := (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').isLeftDerived))

/-- **`Dualizing.PolynomialPresentation.ProjectionCompatibility` holds** for every polynomial
presentation and every base change. -/
theorem PolynomialPresentation.projectionCompatibility {R A R' : Type u} [CommRing R]
    [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    (p : PolynomialPresentation (algebraMap R A)) : p.ProjectionCompatibility R' :=
  PolynomialPresentation.projectionCompatibility_of_kFlatAlgebraActionEq kFlatAlgebraActionEq p

end Dualizing
