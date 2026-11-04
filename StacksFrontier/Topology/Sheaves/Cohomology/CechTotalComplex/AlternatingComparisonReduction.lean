module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AlternatingDerivedGlobalSections

/-!
# Reducing the alternating Čech comparison to a quasi-isomorphism of total complexes

Let `(X, O_X)` be a ringed space, `U : I → Opens X` a finite open covering of `X` and `K^•` a
complex of sheaves of `O_X`-modules. The comparison map `Tot(Č_alt^•(U, K^•)) ⟶ RΓ(X, K^•)` is
invertible exactly when the map of total alternating Čech complexes of abelian groups induced by
the inclusion of `K^•` into its K-injective resolution `I^•` is a quasi-isomorphism.

## Main definitions

* `Stacks.Cech.alternatingCechResolutionTotalMap`: the map of total alternating Čech complexes
  induced by `K^• ⟶ I^•`.

## Main results

* `Stacks.Cech.isIso_alternatingCechToDerivedComparison_app_iff`: the comparison map at `K^•` is
  invertible if and only if `alternatingCechResolutionTotalMap` is a quasi-isomorphism.
* `Stacks.Cech.isIso_alternatingCechToDerivedComparison_app`: the comparison map at `K^•` is
  invertible once `alternatingCechResolutionTotalMap` is a quasi-isomorphism.

## References

* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 08C2](https://stacks.math.columbia.edu/tag/08C2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u

namespace Stacks.Cech

noncomputable section

variable (X : TopCat.{u})

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

attribute [local instance] HasDerivedCategory.standard

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The map of total alternating Čech complexes induced by the inclusion of a complex of
sheaves of modules into its K-injective resolution. -/
noncomputable def alternatingCechResolutionTotalMap {I : Type u} (U : I → Opens X)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (alternatingCechTotalComplexFunctor U).obj ((underlyingPresheafComplexFunctor X R).obj K) ⟶
      (alternatingCechTotalComplexFunctor U).obj
        ((underlyingPresheafComplexFunctor X R).obj ((kInjectiveResolution X R).obj K)) :=
  (alternatingCechTotalComplexFunctor U).map
    ((underlyingPresheafComplexFunctor X R).map (kInjectiveResolutionUnit X R K))

/-- The image of `alternatingCechResolutionTotalMap` in the derived category is
`alternatingCechResolutionMap`. -/
theorem alternatingCechResolutionMap_eq {I : Type u} (U : I → Opens X)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    alternatingCechResolutionMap X R U K =
      DerivedCategory.Q.map (alternatingCechResolutionTotalMap X R U K) :=
  rfl

/-- The comparison map `alternatingCechToDerivedComparison` is invertible at `K` exactly when the
total alternating Čech complex of the K-injective resolution inclusion is a quasi-isomorphism. -/
theorem isIso_alternatingCechToDerivedComparison_app_iff
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    IsIso ((alternatingCechToDerivedComparison X R U hU).app K) ↔
      QuasiIso (alternatingCechResolutionTotalMap X R U K) := by
  rw [alternatingCechToDerivedComparison_app, alternatingCechResolutionMap_eq,
    ← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact isIso_comp_right_iff _ _

/-- The comparison map `alternatingCechToDerivedComparison` is invertible at `K` once the total
alternating Čech complex of the K-injective resolution inclusion is a quasi-isomorphism. -/
theorem isIso_alternatingCechToDerivedComparison_app
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ)
    (h : QuasiIso (alternatingCechResolutionTotalMap X R U K)) :
    IsIso ((alternatingCechToDerivedComparison X R U hU).app K) :=
  (isIso_alternatingCechToDerivedComparison_app_iff X R U hU K).mpr h

end

end Stacks.Cech

end
