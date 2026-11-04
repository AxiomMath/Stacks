module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafExact
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Precomp
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `(M, ρ) ↦ H^i(X_K, ℱ_ρ)` as a cohomological δ-functor on representations

Let `X` be a connected scheme over a field `k` with a geometric point `x`, `Λ` a finite ring and
`K/k` a field extension. The functor `ρ ↦ ℱ_ρ|_{X_K}` of
`AlgebraicGeometry.geometricRepresentationSheaf`, from finite `Λ`-modules with a continuous action
of `π₁(X, x)` to sheaves of `Λ`-modules on `(X_K)_étale`, is exact
(`AlgebraicGeometry.preservesFiniteLimits_geometricRepresentationSheaf` and its colimit
companion). Precomposing the δ-functor of étale cohomology `H^i(X_K, -)` — the right derived
functors of global sections, `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`
— with it therefore gives a cohomological δ-functor

```
(M, ρ) ↦ H^i(X_K, ℱ_ρ)
```

on the abelian category of finite `Λ`-modules with continuous `π₁(X, x)`-action. For `K = k̄` this
is the left-hand side of the right-derived assertion of Stacks Tag 03VM.

## Main definitions

* `AlgebraicGeometry.geometricRepresentationCohomology` — the δ-functor `(M, ρ) ↦ H^i(X_K, ℱ_ρ)`.

## Main results

* `AlgebraicGeometry.geometricRepresentationCohomology_functor` — its degree-`n` component is
  `ρ ↦ Rⁿ Γ(X_K, ℱ_ρ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe u r

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type r) [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K]

/-- The restriction `ρ ↦ ℱ_ρ|_{X_K}` is additive, being exact. -/
instance additive_geometricRepresentationSheaf :
    (geometricRepresentationSheaf B X x Λ f K).Additive :=
  have := preservesFiniteLimits_geometricRepresentationSheaf B X x Λ f K
  Functor.additive_of_preserves_binary_products _

/-- **The δ-functor `(M, ρ) ↦ H^i(X_K, ℱ_ρ)`.** The étale cohomology of the sheaf attached to a
finite `Λ`-module with a continuous `π₁(X, x)`-action, restricted to the base change `X_K`, as a
cohomological δ-functor on such modules: the right derived functors of global sections on
`(X_K)_étale`, precomposed with the exact functor `ρ ↦ ℱ_ρ|_{X_K}`. -/
@[sga "7 I 0.2" "partial"]
def geometricRepresentationCohomology :
    DeltaFunctor (FiniteTypeContinuousModule.{r, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
      (ModuleCat.{max (u + 1) r} Λ) :=
  have := preservesFiniteLimits_geometricRepresentationSheaf B X x Λ f K
  have := preservesFiniteColimits_geometricRepresentationSheaf B X x Λ f K
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))).precomp
    (geometricRepresentationSheaf B X x Λ f K)

/-- The degree-`n` component of `AlgebraicGeometry.geometricRepresentationCohomology` is
`ρ ↦ Rⁿ Γ(X_K, ℱ_ρ)`. -/
theorem geometricRepresentationCohomology_functor (n : ℕ) :
    (geometricRepresentationCohomology B X x Λ f K).functor n =
      geometricRepresentationSheaf B X x Λ f K ⋙
        (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived n :=
  rfl

end AlgebraicGeometry

end
