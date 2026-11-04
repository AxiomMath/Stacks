module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisPoincareDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincarePairingDegreeTwoIso

/-!
# The base case of the derived Poincaré duality of Tag 03VM, at `n = #Λ`

For a finite ring `Λ` with `n = #Λ` invertible in `k`, an injective resolution `K₀` of `j_! μ_n`
in degrees `≥ 0` and a lift `t` of the trace `H²_c(X_k̄, μ_n) → ℚ/ℤ`, the map of complexes
`Γ^Gal(I) ⟶ Hom^•(Γ^Gal(ℋom^•(I, res_ℤ K₀)), T)` of the Poincaré pairing of every member
`(M, I)` of the family is an isomorphism on `H²`
(`AlgebraicGeometry.isIso_homologyMap_poincarePairing_two`). This is the hypothesis `hbase` of
`AlgebraicGeometry.galoisCompactSupportPoincareDualityNatIso`, stated in exactly its form; it is
`AlgebraicGeometry.isIso_homologyMap_poincarePairing_two_of_fintypeCard` read at `Nat.card Λ`.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology
open Stacks.ContinuousCohomology Stacks.AbelianInternalHom

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] [Algebra.IsSeparable k K]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) K)) (Λ : Type) [Ring Λ] [Finite Λ]
  (j : CompactificationOf (Over.mk f))

/-- **The base case of the derived Poincaré duality of Tag 03VM**: for `n = #Λ` invertible in
`k`, every injective resolution `K₀` of `j_! μ_n` in degrees `≥ 0` and every lift `t` of the trace
`H²_c(X_k̄, μ_n) → ℚ/ℤ`, the map of the Poincaré pairing of each member `(M, I)` of the family is an
isomorphism on `H²`. This is the hypothesis `hbase` of
`AlgebraicGeometry.galoisCompactSupportPoincareDualityNatIso`. -/
theorem isIso_homologyMap_poincarePairing_two (hΛ : IsUnit ((Nat.card Λ : ℕ) : k)) :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
    letI := zmodNatCardAlgebra Λ
    ∀ (K₀ : CochainComplex.InjectiveResolution
        ((CochainComplex.singleFunctor _ 0).obj
          ((etaleModuleExtensionByZero (ZMod (Nat.card Λ)) j.immersion).obj
            ((representationSheaf B X _ (ZMod (Nat.card Λ))).obj
              (cyclotomicContinuousModule B X f K y (Nat.card Λ)))))) [K₀.cocomplex.IsStrictlyGE 0]
      (t : (show CochainComplex
          (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
          galoisHomOpG (Over.mk j.toBase) K
            (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) ⟶
          traceTarget.{u, u + 1} (K ≃ₐ[k] K) 2),
      DerivedCategory.Q.map t =
        @derivedTraceOfIsLE.{u, u + 1} (K ≃ₐ[k] K) _ _ _
          (show CochainComplex
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
          galoisHomOpG (Over.mk j.toBase) K
            (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) 2
          (isLE_galoisHomOpG_cyclotomic B X f K y (Nat.card Λ) j K₀)
          (galoisHomOpCyclotomicTrace B X f K y (Nat.card Λ) j K₀
            (isUnit_natCard_of_isUnit_field K Λ hΛ)) ≫
        (@DerivedCategory.Q (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K))
          _ _ (HasDerivedCategory.standard _)).map (traceTargetι.{u, u + 1} (K ≃ₐ[k] K) 2) →
      ∀ i : PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
        IsIso (HomologicalComplex.homologyMap
          (internalHomComplexOfPairing
            (poincarePairing K (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀) t i)) 2) := by
  let := connectedSpace_of_isCurve B X f
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  have : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
  let := Fintype.ofFinite Λ
  suffices H : ∀ (n : ℕ) [NeZero n] [Algebra (ZMod n) Λ] (hn : IsUnit ((n : ℕ) : K)),
      Fintype.card Λ = n →
      ∀ (K₀ : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor _ 0).obj
            ((etaleModuleExtensionByZero (ZMod n) j.immersion).obj
              ((representationSheaf B X _ (ZMod n)).obj
                (cyclotomicContinuousModule B X f K y n))))) [K₀.cocomplex.IsStrictlyGE 0]
        (t : (show CochainComplex
            (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
            galoisHomOpG (Over.mk j.toBase) K (cyclotomicIntResolution B X f K y n j K₀)) ⟶
            traceTarget.{u, u + 1} (K ≃ₐ[k] K) 2),
        DerivedCategory.Q.map t =
          @derivedTraceOfIsLE.{u, u + 1} (K ≃ₐ[k] K) _ _ _
            (show CochainComplex
                (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
            galoisHomOpG (Over.mk j.toBase) K (cyclotomicIntResolution B X f K y n j K₀)) 2
            (isLE_galoisHomOpG_cyclotomic B X f K y n j K₀)
            (galoisHomOpCyclotomicTrace B X f K y n j K₀ hn) ≫
          (@DerivedCategory.Q
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K))
            _ _ (HasDerivedCategory.standard _)).map (traceTargetι.{u, u + 1} (K ≃ₐ[k] K) 2) →
        ∀ i : PoincareIndex B X (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
          IsIso (HomologicalComplex.homologyMap
            (internalHomComplexOfPairing
              (poincarePairing K (cyclotomicIntResolution B X f K y n j K₀) t i)) 2) from
    @H (Nat.card Λ) _ (zmodNatCardAlgebra Λ) (isUnit_natCard_of_isUnit_field K Λ hΛ)
      Nat.card_eq_fintype_card.symm
  intro n _ _ hn hcard
  subst hcard
  intro K₀ _ t ht i
  exact isIso_homologyMap_poincarePairing_two_of_fintypeCard B X f K Λ y j K₀ hn t ht i

end AlgebraicGeometry

end
