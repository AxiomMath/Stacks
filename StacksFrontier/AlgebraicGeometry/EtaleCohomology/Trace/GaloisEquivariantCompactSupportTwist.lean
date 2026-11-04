module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantCohomologyAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCanonicalTwistGalois

/-!
# The Galois module `H²(RΓ^Gal_c(X_k̄, ℱ_ρ))` and the canonical twist `Ψ`

Let `X` be a geometrically connected smooth curve over `k`, `k̄` an algebraic closure which is
separable over `k` (for instance `k` finite), `Λ` a finite ring of order invertible in `k̄` and
`ρ` a finite `Λ`-module with a continuous action of `π₁(X)`. The choice-free identification
`Ψ : H²_c(X_k̄, ℱ_ρ) ≃ Hom(μ_n(k̄), M_N)` of Stacks 03VK
(`AlgebraicGeometry.compactSupportCanonicalTwistEquiv`) is Galois-equivariant for the action of
Remark 03UI (2) (`AlgebraicGeometry.compactSupportCanonicalTwistEquiv_galois`). This file reads
that statement on the Galois module `H²(RΓ^Gal_c(X_k̄, ℱ_ρ))` of discrete
`Λ[Aut_k(k̄)]`-modules: through `Stacks.EtaleCohomology.galoisCompactSupportGroupForgetIso`, the
action of `σ` coming from the Galois-module structure is carried by `Ψ` to the action of `σ` on
`Hom(μ_n(k̄), M_N)`.

## Main results

* `AlgebraicGeometry.compactSupportCanonicalTwistEquiv_galoisCompactSupportGroupForgetIso`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK).
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (2).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.EtaleCohomology.etaleModulesEnoughInjectivesZeroTraceTwist

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))
  (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

/-- **`Ψ` on the Galois module `H²(RΓ^Gal_c(X_k̄, ℱ_ρ))` is Galois-equivariant**: for `x` in the
underlying module of `H²(RΓ^Gal_c(X_k̄, ℱ_ρ))`, `Ψ` of the image of `σ · x` in `H²_c(X_k̄, ℱ_ρ)`
is `σ` applied to `Ψ` of the image of `x`, `σ` acting on `Hom(μ_n(k̄), M_N)` on both `μ_n` and
`M_N`. -/
theorem compactSupportCanonicalTwistEquiv_galoisCompactSupportGroupForgetIso
    (σ : kbar ≃ₐ[k] kbar) (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (x : letI := connectedSpace_of_isCurve B X f
      ((DerivedCategory.Plus.homologyFunctor (GaloisModules Λ k kbar) ((2 : ℕ) : ℤ)).obj
        (galoisDerivedCompactSupport Λ f j kbar ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)))).obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn ρ
        ((galoisCompactSupportGroupForgetIso Λ f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)).hom
          ((((DerivedCategory.Plus.homologyFunctor (GaloisModules Λ k kbar) ((2 : ℕ) : ℤ)).obj
            (galoisDerivedCompactSupport Λ f j kbar
              ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                ((representationSheaf B X _ Λ).obj ρ)))).obj.obj.ρ σ).hom x)) =
      rootsOfUnityHomRepresentation k kbar (Fintype.card Λ) Λ
        (geometricNormalCoinvariantsGaloisRepresentation B X f kbar Λ y ρ) σ
        (compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn ρ
          ((galoisCompactSupportGroupForgetIso Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)).hom x)) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have h := ConcreteCategory.congr_hom (galoisCompactSupportGroupForgetIso_hom_galoisAction Λ f j
      kbar σ ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) x
  -- `convert` compares the two sides by congruence: the base states the action at `Λ : Type r`
  -- with `r := 0`, and comparing the unsplit terms exceeds the default recursion depth.
  convert compactSupportCanonicalTwistEquiv_galois B X f kbar Λ y j hn σ ρ
    ((galoisCompactSupportGroupForgetIso Λ f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)).hom x) using 2
  exact h

end AlgebraicGeometry

end
