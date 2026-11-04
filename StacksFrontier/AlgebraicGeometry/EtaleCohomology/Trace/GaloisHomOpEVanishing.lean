module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpERepresentationDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisDerivedGlobalSectionsVanishing
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteTypeDual

/-!
# `Γ^Gal(X̄, ℋom^•_ℤ(I, K))` has no cohomology outside `[0, 2]`

On a smooth geometrically connected curve `X` over `k` with compactification `j : X ⟶ X̄`, let `I`
be an injective resolution of `(j_! ℱ_M)[0]` and `K` the complex of abelian sheaves underlying an
injective resolution of `j_! ℱ_μ`. The complex `E = Γ^Gal(X̄, ℋom^•_ℤ(I, K))` of the evaluation
pairing of Tag 03VM represents `RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))`
(`AlgebraicGeometry.galoisHomOpERepresentationDerivedIso`), which is concentrated in degrees
`[0, 2]` (`Stacks.EtaleCohomology.isZero_homology_galoisDerivedGlobalSections_single`). Hence
`Hᵠ(E) = 0` for `q < 0` and for `q > 2`
(`AlgebraicGeometry.isZero_homology_galoisHomOpE_cyclotomic`).

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology
open Stacks.AbelianInternalHom Stacks.ConstantSheaf

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]
  (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod n) j.immersion).obj
          ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n)))))
  (Λ : Type) [Ring Λ] [Finite Λ] [Algebra (ZMod n) Λ]

/-- **`Hᵠ(Γ^Gal(X̄, ℋom^•_ℤ(I, K))) = 0` for `q < 0` and for `q > 2`**, for `I` an injective
resolution of `(j_! ℱ_M)[0]` and `K` the complex underlying an injective resolution of
`j_! ℱ_μ`. -/
theorem isZero_homology_galoisHomOpE_cyclotomic [ConnectedSpace X.1] (x : GeometricPoint X.1)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
          ((representationSheaf B X x Λ).obj M))))
    [K₀.cocomplex.IsStrictlyGE 0]
    (hG' : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} X.1.smallEtaleTopology
      (ZMod n) ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) X.1).obj
        ((representationSheaf B X x Λ).obj M)))
    (hω : letI := connectedSpace_of_isCurve B X f
      Stacks.ModuleInternalHom.IsLocallyConstantInjective X.1.smallEtaleTopology (ZMod n)
        ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n)))
    (q : ℤ) (hq : q < 0 ∨ 2 < q) :
    IsZero ((galoisHomOpE (Over.mk j.toBase) kbar I.cocomplex
      (cyclotomicIntResolution B X f kbar y n j K₀)).homology q) := by
  have hT := isZero_homology_galoisDerivedGlobalSections_single Λᵐᵒᵖ f kbar
    (homOpSheaf X.1.smallEtaleTopology ((representationSheaf B X x Λ).obj M)
      (let := connectedSpace_of_isCurve B X f; toAb _ ((representationSheaf B X _ (ZMod n)).obj
        (cyclotomicContinuousModule B X f kbar y n)))) q hq
  have hQ := IsZero.of_iso hT ((DerivedCategory.homologyFunctor _ q).mapIso
    (galoisHomOpERepresentationDerivedIso B X f kbar y n j K₀ Λ x M I hG' hω))
  exact IsZero.of_iso hQ ((DerivedCategory.homologyFunctorFactors _ q).app _).symm

end AlgebraicGeometry

end
