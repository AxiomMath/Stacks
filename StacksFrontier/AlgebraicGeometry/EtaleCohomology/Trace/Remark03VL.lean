module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGeometricCoinvariantsEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupport

/-!
# Degree two of Remark 03VL: `H²_c(X_k̄, ℱ_ρ) = M_{π₁(X_k̄, η̄)}(-1)` for a projective curve

Let `X` be a geometrically connected smooth curve over a field `k`, `Λ` a finite ring with
`#Λ ∈ k^*`, and `ℱ_ρ` the sheaf on `X_étale` attached to a finite `Λ`-module `M` with a continuous
action `ρ` of `π₁(X, η̄)`. Remark 03VL of the Trace Formula chapter records, for `X` projective,
the identification `H²_c(X_k̄, ℱ_ρ) = M_{π₁(X_k̄, η̄)}(-1)` functorially in `ρ`. Here `X` is its
own compactification (`AlgebraicGeometry.CompactificationOf.ofProper`), `H²_c` is that of
Remark 03UI (2), and `M_π(-1)` is `Hom(μ_n(k̄), M_π)` with `n = #Λ`, the choice-free form of the
Tate twist, through which no primitive root of unity has to be chosen.

The two degree-zero assertions of the remark are
`AlgebraicGeometry.curveGlobalSectionsIsoInvariants` and
`AlgebraicGeometry.isZero_curveCompactlySupportedCohomologyZero_of_not_isProjective`.

## Main results

* `AlgebraicGeometry.compactSupportGeometricTwistEquiv_naturality` — the identification
  `H²_c(X_k̄, ℱ_ρ) ≃ Hom(μ_n, M_π)` of Lemma 03VK is natural in `ρ`.
* `AlgebraicGeometry.properCurveCompactSupportTwoEquiv` and
  `AlgebraicGeometry.properCurveCompactSupportTwoEquiv_naturality` — the degree-two assertion of
  Remark 03VL.

## References

* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- A homomorphism out of the `n`-th roots of unity into a group killed by `n` is determined by
its value at a primitive root. -/
theorem addMonoidHom_rootsOfUnity_ext {K : Type*} [Field K] {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (R : Type*) [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    (hM : ∀ m : M, n • m = 0) {g₁ g₂ : Additive (_root_.rootsOfUnity n K) →+ M}
    (h : g₁ (Additive.ofMul hζ.toRootsOfUnity) = g₂ (Additive.ofMul hζ.toRootsOfUnity)) :
    g₁ = g₂ :=
  (rootsOfUnityHomEvalEquiv hζ R hM).injective h

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))
  (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

/-- **The choice-free identification of Lemma 03VK is natural in `ρ`.** For a morphism
`v : ρ ⟶ ρ'`, the map induced on `H²_c(X_k̄, -)` corresponds to composition with the map induced
on coinvariants. -/
theorem compactSupportGeometricTwistEquiv_naturality (j : CompactificationOf (Over.mk f))
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ')
    (x : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    compactSupportGeometricTwistEquiv B X f kbar Λ y j hn ρ'
        (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
              ((representationSheaf B X _ Λ).map v)))).hom x) =
      (geometricCoinvariantsMap B X f kbar Λ y v).toAddMonoidHom.comp
        (compactSupportGeometricTwistEquiv B X f kbar Λ y j hn ρ x) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
  have hζ := (exists_isPrimitiveRoot_of_isUnit hn).choose_spec
  refine addMonoidHom_rootsOfUnity_ext hζ Λ (card_nsmul_eq_zero_of_module Λ) ?_
  have h1 := compactSupportGeometricTwistEquiv_apply_ofMul B X f kbar Λ y j hn hζ ρ'
    (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
      (galoisCompactSupportCohomologyMap Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
          ((representationSheaf B X _ Λ).map v)))).hom x)
  have h2 := compactSupportGeometricTwistEquiv_apply_ofMul B X f kbar Λ y j hn hζ ρ x
  have h3 := LinearMap.congr_fun
    (compactSupportGeometricCoinvariantsMap_naturality B X f kbar Λ y j hn hζ v) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h3
  rw [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, h1, h2]
  convert h3 using 2

/-- **Stacks Project, Tag 03VL, degree two: `H²_c(X_k̄, ℱ_ρ) = M_{π₁(X_k̄, η̄)}(-1)` for `X`
projective.** For a geometrically connected smooth proper curve `X` over a field `k`, an
algebraic closure `k̄`, a finite ring `Λ` with `#Λ` invertible, and a finite `Λ`-module `M` with a
continuous action `ρ` of `π₁(X, η̄)`, the compactly supported cohomology `H²_c(X_k̄, ℱ_ρ)`, `X`
being its own compactification, is `M_{π₁(X_k̄, η̄)}(-1) = Hom(μ_n(k̄), M_{π₁(X_k̄, η̄)})`,
`n = #Λ`, with no choice of a root of unity. The source assumes `X` projective; a projective
morphism is proper (`AlgebraicGeometry.isProper_of_isProjectiveMorphism`), and for a curve the two
are equivalent (Tag 0A26), so properness is the hypothesis. Its functoriality in `ρ` is
`AlgebraicGeometry.properCurveCompactSupportTwoEquiv_naturality`. -/
@[stacks 03VL "H²_c(X_k̄, ℱ_ρ) = M_{π₁(X_k̄,η̄)}(-1) for X projective (here: proper): the \
root-of-unity free (ζ-independent) Λ-linear identification, M(-1) being Hom(μ_n, M); \
functoriality in ρ is properCurveCompactSupportTwoEquiv_naturality"]
def properCurveCompactSupportTwoEquiv [IsProper f]
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f (CompactificationOf.ofProper f) kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ) ≃ₗ[Λ]
      (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar) →+
        Stacks.Trace.coinvariants (geometricRepresentation B X f kbar Λ y ρ)) :=
  compactSupportGeometricTwistEquiv B X f kbar Λ y (CompactificationOf.ofProper f) hn ρ

/-- **Stacks Project, Tag 03VL, degree two, functoriality in `ρ`.** For `v : ρ ⟶ ρ'`, the
identification `H²_c(X_k̄, ℱ_ρ) = M_{π₁(X_k̄, η̄)}(-1)` carries the map induced by `v` on `H²_c` to
the map induced by `v` on coinvariants. -/
@[stacks 03VL "H²_c(X_k̄, ℱ_ρ) = M_{π₁(X_k̄,η̄)}(-1) is functorial in ρ"]
theorem properCurveCompactSupportTwoEquiv_naturality [IsProper f]
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (v : ρ ⟶ ρ')
    (x : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f (CompactificationOf.ofProper f) kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    properCurveCompactSupportTwoEquiv B X f kbar Λ y hn ρ'
        (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
          (galoisCompactSupportCohomologyMap Λ f (CompactificationOf.ofProper f) kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
              ((representationSheaf B X _ Λ).map v)))).hom x) =
      (geometricCoinvariantsMap B X f kbar Λ y v).toAddMonoidHom.comp
        (properCurveCompactSupportTwoEquiv B X f kbar Λ y hn ρ x) := by
  convert compactSupportGeometricTwistEquiv_naturality B X f kbar Λ y hn
    (CompactificationOf.ofProper f) v x using 2 <;> rfl

end AlgebraicGeometry
