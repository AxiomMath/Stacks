module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpEVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpECyclotomicDerivedIsoOfIsUnit

/-!
# `Γ^Gal(X̄, ℋom^•_ℤ(I, K))` has no cohomology outside `[0, 2]` when `n` is invertible

`AlgebraicGeometry.isZero_homology_galoisHomOpE_cyclotomic` with its two side conditions
discharged, which holds as soon as `n` is invertible in `k̄`. The side conditions are
`isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf` and
`isLocallyConstantInjective_representationSheaf_cyclotomic`, both in `AlgebraicGeometry`.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology
open Stacks.AbelianInternalHom Stacks.ConstantSheaf

universe u

namespace AlgebraicGeometry

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

/-- **`Hᵠ(Γ^Gal(X̄, ℋom^•_ℤ(I, K))) = 0` for `q < 0` and for `q > 2`**, for `n` invertible in
`k̄`, `I` an injective resolution of `(j_! ℱ_M)[0]` and `K` the complex underlying an injective
resolution of `j_! ℱ_μ`. -/
theorem isZero_homology_galoisHomOpE_cyclotomic_of_isUnit (hn : IsUnit ((n : ℕ) : kbar))
    [ConnectedSpace X.1] (x : GeometricPoint X.1)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
          ((representationSheaf B X x Λ).obj M))))
    [K₀.cocomplex.IsStrictlyGE 0] (q : ℤ) (hq : q < 0 ∨ 2 < q) :
    IsZero ((galoisHomOpE (Over.mk j.toBase) kbar I.cocomplex
      (cyclotomicIntResolution B X f kbar y n j K₀)).homology q) :=
  isZero_homology_galoisHomOpE_cyclotomic B X f kbar y n j K₀ Λ x M I
    (isFinitePresentationLocallyConstantModuleSheaf_restrictScalars_representationSheaf B X x n Λ M)
    (isLocallyConstantInjective_representationSheaf_cyclotomic B X f kbar y n hn) q hq

end AlgebraicGeometry

end
