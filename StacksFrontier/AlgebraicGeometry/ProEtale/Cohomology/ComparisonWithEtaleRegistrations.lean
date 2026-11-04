module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ComparisonWithEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ConstructibleComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.DirectImageComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.InverseImageInjective
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.LocallyConstantComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ModuleComparisonWithEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.TorsorComparison

/-!
# Stacks registrations of the comparison of pro-étale and étale cohomology

The comparison theorems between the small étale and the pro-étale site of a scheme along
`ε : X_proétale → X_étale` are proved, unconditionally, in the modules imported here. This module
registers them with the Stacks project tags they formalize:

* 099U: `AlgebraicGeometry.ProEtale.subsingleton_sheafH_proetaleInverseImage_of_injective`
  (`ProEtale/Cohomology/InverseImageInjective`);
* 099V (1), (2) and 099W (1), (2): `ProEtale/Cohomology/ComparisonWithEtale`;
* 099X: `AlgebraicGeometry.ProEtale.bijective_torsorClassesMap`
  (`ProEtale/Cohomology/TorsorComparison`);
* 099Y: `AlgebraicGeometry.ProEtale.isEquivalence_etaleInverseImageLocallyConstant`
  (`ProEtale/Cohomology/LocallyConstantComparison`);
* 099Z, 09AL, 09B1 (1), (2): `ProEtale/Cohomology/ModuleComparisonWithEtale`;
* 09A6 (1), (2): `ProEtale/Cohomology/DirectImageComparison`;
* 09AK: `AlgebraicGeometry.ProEtale.isEquivalence_etaleInverseImageConstructible`
  (`ProEtale/Cohomology/ConstructibleComparison`).
-/

@[expose] public section

add_to_stacks 099U "pro-étale cohomology is `Ext` out of the constant sheaf `ℤ`, and `ε⁻¹` is an \
  arbitrary left adjoint of the restriction `ε_*` to the small étale site"
  AlgebraicGeometry.ProEtale.subsingleton_sheafH_proetaleInverseImage_of_injective

add_to_stacks 099V "part (1): `ε_* ε⁻¹ ℱ = ℱ` by the unit, and `R^q ε_*(ε⁻¹ ℱ) = 0` for `q > 0`"
  AlgebraicGeometry.ProEtale.isIso_unit_app_and_isZero_rightDerived_epsilonDirectImage

add_to_stacks 099V "part (2); `ε⁻¹` on `D⁺` is `ε⁻¹` applied termwise (its right derived \
  functor), and the map is the unit of the derived adjunction"
  AlgebraicGeometry.ProEtale.isIso_epsilonAdjunction_rightDerivedFunctorPlus_unit

add_to_stacks 099W "part (1), naturally in the sheaf; \
  cohomology is `Ext` out of the constant sheaf `ℤ`"
  AlgebraicGeometry.ProEtale.epsilonInverseImageCompFunctorHIso

add_to_stacks 099W "part (2), naturally in `K`; `ε⁻¹` on `D⁺` is `ε⁻¹` applied termwise"
  AlgebraicGeometry.ProEtale.rightDerivedFunctorPlusΓIso

add_to_stacks 099X "`H¹` is the set of isomorphism classes of torsors and the map is `ε⁻¹`"
  AlgebraicGeometry.ProEtale.bijective_torsorClassesMap

add_to_stacks 099Y AlgebraicGeometry.ProEtale.isEquivalence_etaleInverseImageLocallyConstant

add_to_stacks 099Z AlgebraicGeometry.ProEtale.isEquivalence_etaleInverseImageDerivedLocallyConstant

add_to_stacks 09A6 "part (1), naturally in the sheaf of sets"
  AlgebraicGeometry.Scheme.proetaleDirectImageEtaleInverseImageIso

add_to_stacks 09A6 "part (2), for complexes bounded below: \
  `R f_{proétale,*} ∘ ε⁻¹ ≅ ε⁻¹ ∘ R f_{étale,*}` on `D⁺`, with `ε⁻¹` applied termwise"
  AlgebraicGeometry.ProEtale.proetaleDirectImageRightDerivedEpsilonInverseImageIso

add_to_stacks 09AK AlgebraicGeometry.ProEtale.isEquivalence_etaleInverseImageConstructible

add_to_stacks 09AL AlgebraicGeometry.ProEtale.isEquivalence_etaleInverseImageDerivedConstructible

add_to_stacks 09B1 "part (1)" AlgebraicGeometry.Scheme.isWeakSerreClass_etaleInverseImage_essImage

add_to_stacks 09B1 "part (2); the equivalence has functor `ε⁻¹` applied termwise and inverse `Rε_*`"
  AlgebraicGeometry.Scheme.exists_equivalence_etaleInverseImage_derivedCategoryPlus

end
