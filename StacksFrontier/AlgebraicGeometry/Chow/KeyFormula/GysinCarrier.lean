module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge

/-!
# The Gysin map kills a rational equivalence without enlarging its carrier

For the zero scheme `i : D = Z(s) ⟶ X` of a global section `s` of an invertible module, the
Gysin map sends a `(k+1)`-cycle rationally equivalent to zero within a subset `T` of `X` to a
`k`-cycle on `D` rationally equivalent to zero within the preimage `i^{-1}(T)`. This refines
Stacks 02TO, which forgets the subset carrying the rational equivalence.

## Main results

* `Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup` — the Gysin cycle
  of a cycle rationally equivalent to zero within `T` is rationally equivalent to zero within
  `i^{-1}(T)`.

## References

* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02R9](https://stacks.math.columbia.edu/tag/02R9)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **The Gysin map preserves a rational equivalence within a carrier.** If a `(k+1)`-cycle on
`X` is rationally equivalent to zero within a subset `T`, its Gysin cycle on the zero scheme
`D = Z(s)` is rationally equivalent to zero within the preimage of `T` in `D`. -/
theorem isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup
    {α : CycleGroup C p (k + 1)} {T : Set X}
    (hα : IsRationallyEquivalentToZeroWithin C p (k + 1) α T) :
    IsRationallyEquivalentToZeroWithin C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup α)
      ((Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹' T) := by
  obtain ⟨J, W, hW, hDim, hLocal, hsub, g, hg⟩ := hα
  set R := gysinRule C p k L s (firstChernComponentClass C p k L)
  set i := (Stacks.Divisors.zeroScheme X L s).subschemeι
  set D : J → CycleGroup C p (k + 1) := fun j ↦
    ⟨principalDivisorPushforward C p (W j) (hW j) (g j),
      principalDivisorPushforward_mem_cyclesOfDimension C p (k + 1) (W j) (hW j) (hDim j) (g j)⟩
  refine (rationallyEquivalentToZeroWithin_finsum C (i ≫ p) k (fun j ↦ R.extendCycleGroup (D j))
    (fun j ↦ i.base ⁻¹' ((W j).support : Set X)) (hLocal.preimage_continuous i.continuous)
    (fun j ↦ gysinOfInvertibleKillsPrincipalDivisorOnComponent C p k L s (W j) (hW j) (hDim j)
      (g j))
    (R.extendCycleGroup_finsum D _ hLocal
      (fun j ↦ support_principalDivisorPushforward_subset C p (W j) (hW j) (g j)) α hg)).mono
    (Set.iUnion_subset fun j ↦ Set.preimage_mono (hsub j))

end Stacks.Chow

end
