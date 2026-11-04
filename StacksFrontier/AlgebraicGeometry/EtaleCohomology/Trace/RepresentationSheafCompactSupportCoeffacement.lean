module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCompactSupportDelta
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.CoindRelativeSum
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalCardinality

/-!
# Coeffacing `(M, ρ) ↦ H_c^1(X_k̄, ℱ_ρ)` by a coinduced module: the reduction to a count

Let `T` be the homological δ-functor `Tᵢ(ρ) = H_c^{2-i}(X_k̄, ℱ_ρ)`
(`AlgebraicGeometry.compactSupportRepresentationHomology`). For open subgroups `H' ≤ H` of
`π₁(X, x)` the sum map `Σ_{H'} : Coind_{H'} M ⟶ M` factors as the relative sum
`Σ_{H'/H} : Coind_{H'} M ⟶ Coind_H M` followed by `Σ_H`. The long exact sequence of `T` for
`0 → K → Coind_{H'} M → Coind_H M → 0` and a count then give `T₁(Σ_{H'}) = 0`. The count needed
is that `T₁(Coind_H M)` have at most as many elements as the kernel of `T₀(K ⟶ Coind_{H'} M)`.

## Main results

* `AlgebraicGeometry.shortExact_kernel_coindRelSum`: `0 → K → Coind_{H'} M → Coind_H M → 0`.
* `AlgebraicGeometry.compactSupportRepresentationHomology_map_coindSum_eq_zero_of_natCard_le`:
  `T₁(Σ_{H'}) = 0` under that count.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar]
  {H' H : OpenSubgroup (EtaleFundamentalGroup X.1 x)} (h : H' ≤ H)

/-- The short complex `K ⟶ Coind_{H'} M ⟶ Coind_H M` of the kernel of the relative sum map. -/
abbrev kernelCoindRelSumShortComplex
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ShortComplex (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :=
  ShortComplex.mk (kernel.ι (finiteTypeContinuousModuleCoindRelSum Λ h M))
    (finiteTypeContinuousModuleCoindRelSum Λ h M) (kernel.condition _)

/-- **`0 → K → Coind_{H'} M → Coind_H M → 0` is short exact.** -/
theorem shortExact_kernel_coindRelSum
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (kernelCoindRelSumShortComplex B X x Λ h M).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel (kernelCoindRelSumShortComplex B X x Λ h M)
      (kernelIsKernel (finiteTypeContinuousModuleCoindRelSum Λ h M)))
    (inferInstanceAs (Mono (kernel.ι (finiteTypeContinuousModuleCoindRelSum Λ h M))))
    (inferInstanceAs (Epi (finiteTypeContinuousModuleCoindRelSum Λ h M)))

/-- **`T₁(Σ_{H'}) = 0` from a count.** If `T₁(Coind_H M) = H_c^1(X_k̄, ℱ_{Coind_H M})` is finite
with at most as many elements as the kernel of `T₀(K ⟶ Coind_{H'} M)`, then the sum map
`Σ_{H'} : Coind_{H'} M ⟶ M` is killed by `T₁`. -/
theorem compactSupportRepresentationHomology_map_coindSum_eq_zero_of_natCard_le
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    [Finite (((compactSupportRepresentationHomology B X x Λ f j kbar).functor 1).obj
      ((finiteTypeContinuousModuleCoind Λ H).obj M))]
    (hcard : Nat.card (((compactSupportRepresentationHomology B X x Λ f j kbar).functor 1).obj
        ((finiteTypeContinuousModuleCoind Λ H).obj M)) ≤
      Nat.card (LinearMap.ker (((compactSupportRepresentationHomology B X x Λ f j kbar).functor
        0).map (kernel.ι (finiteTypeContinuousModuleCoindRelSum Λ h M))).hom)) :
    ((compactSupportRepresentationHomology B X x Λ f j kbar).functor 1).map
      (finiteTypeContinuousModuleCoindSum Λ H' M) = 0 := by
  have h0 := Stacks.CategoryHomology.HomologicalDeltaFunctor.map_g_eq_zero_of_natCard_le
    (compactSupportRepresentationHomology B X x Λ f j kbar)
    (shortExact_kernel_coindRelSum B X x Λ h M) 0 hcard
  rw [← finiteTypeContinuousModuleCoindRelSum_comp_coindSum Λ h M, Functor.map_comp]
  show ((compactSupportRepresentationHomology B X x Λ f j kbar).functor 1).map
      (finiteTypeContinuousModuleCoindRelSum Λ h M) ≫ _ = 0
  rw [h0, zero_comp]

end AlgebraicGeometry

end
