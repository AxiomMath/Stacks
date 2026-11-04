module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrDegreeSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationIntegralPushforward

/-!
# Specialization of cycles commutes with proper pushforward

Let `R` be a discrete valuation ring with fraction field `K` and residue field `κ`, let
`f : X ⟶ Y` be a proper morphism of schemes locally of finite type over `R` and let `r ≥ 0`.
The square

```
  Z_r(X_K) --- sp_{X/R} ---> Z_r(X_κ)
      |                          |
   f_{K,*}                    f_{κ,*}
      ↓                          ↓
  Z_r(Y_K) --- sp_{Y/R} ---> Z_r(Y_κ)
```

commutes, where the vertical arrows are proper pushforward along the morphisms induced by `f` on
the generic and the closed fibres. This is Stacks 0H4M.

## Main results

* `Stacks.Chow.fiberSpecializationMap_eq_specializationCycle` — the specialization map built in
  `StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Specialization` and the one built in
  `StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationCycle` agree.
* `Stacks.Chow.specializationCycle_fiberProperPushforward`,
  `Stacks.Chow.properPushforward_specializationMap` — **Stacks 0H4M**, in the two spellings of
  the specialization map.

## Implementation notes

The content is the identity on the fundamental cycle of a single integral closed subscheme of
the generic fibre, which comes from
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationIntegralPushforward`,
which rests on the degree computation of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrDegreeSpecialization`; the work here is
the extension of that identity to an arbitrary cycle. Both sides of the square are locally
finite double sums, so matching them needs the sum over `X` reindexed as a sum over `X_K`,
the sum over `Y_K` reindexed over the fibres of `f_K`, and a finiteness bound for each, which is
where the properness of `f` is used.

The integral-component identity is applied only at the points of the generic fibre of dimension
`r`, which is all a cycle in `Z_r(X_K)` is supported on.

## References

* [Stacks Project, Tag 0H4M](https://stacks.math.columbia.edu/tag/0H4M)
* [Stacks Project, Tag 0H4H](https://stacks.math.columbia.edu/tag/0H4H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The extension from integral components to an arbitrary cycle -/

section ProperPushforward

variable {S X Y : Scheme.{u}} (sX : X ⟶ S) [LocallyOfFiniteType sX] (sY : Y ⟶ S)
  [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (η s : S) (r : ℕ)

/-- Only finitely many components of a cycle on the fibre over `η` contribute to the coefficient
of its specialized pushforward at a point `z`: such a component has the image of `z` in the
closure of the image of its generic point, so, `f` being proper and hence closed, its closure
meets the compact fibre of `f` over the image of `z`. -/
private theorem finite_support_specializationTerm (α : FiberCycleGroup sX η r)
    (z : sY.fiber s) :
    (Function.support fun x : sX.fiber η ↦ α.1 x * fiberPushforwardWeight sX sY f hf η x *
      (inverseImageCycle (fieldChowSituation (S.residueField s))
        (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)
        ((sY.fiberι η).base ((inducedFiberMap sX sY f hf η).base x))).1 z).Finite := by
  have hbase : ∀ x : sX.fiber η,
      (sY.fiberι η).base ((inducedFiberMap sX sY f hf η).base x) = f.base ((sX.fiberι η).base x) :=
    inducedFiberMap_fiberι_base sX sY f hf η
  have hK : IsCompact (f.base ⁻¹' {(sY.fiberι s).base z}) :=
    f.isProperMap.isCompact_preimage isCompact_singleton
  have hA := finite_support_inter_generalizations
    (ofFiberCycle sX η α.1).locallyFiniteSupport hK
  refine (Set.Finite.preimage ((sX.fiberι η).isEmbedding.injective.injOn) hA).subset ?_
  intro x hx
  replace hx : α.1 x * fiberPushforwardWeight sX sY f hf η x *
    (inverseImageCycle (fieldChowSituation (S.residueField s))
      (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)
      ((sY.fiberι η).base ((inducedFiberMap sX sY f hf η).base x))).1 z ≠ 0 := hx
  have hαx : α.1 x ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hx)
  have hclos : (sY.fiberι s).base z ∈
      closure ({(sY.fiberι η).base ((inducedFiberMap sX sY f hf η).base x)} : Set Y) :=
    (inverseImageComponentRule (fieldChowSituation (S.residueField s))
      (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)).mem_closure_of_apply_ne_zero _ z
      (right_ne_zero_of_mul hx)
  rw [hbase] at hclos
  have himg : closure ({f.base ((sX.fiberι η).base x)} : Set Y) ⊆
      f.base '' closure ({(sX.fiberι η).base x} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.2 ⟨_, subset_closure rfl, rfl⟩)
      (f.isProperMap.isClosedMap _ isClosed_closure)
  obtain ⟨a, haclos, hav⟩ := himg hclos
  refine ⟨⟨a, hav, haclos⟩, ?_⟩
  show ofFiberCycle sX η _ ((sX.fiberι η).base x) ≠ 0
  rw [ofFiberCycle_apply_fiberι]
  exact hαx

/-- The coefficient of the pushforward of a specialization, as a locally finite sum over the
fibre over `η`: the pushforward of the cycle attached to each component is evaluated by the
integral-component hypothesis. -/
private theorem properPushforward_fiberSpecializationMap_coeff
    (hcompat : ∀ x : sX.fiber η,
      relativeDimension (fieldChowSituation (S.residueField η)).dimensionFunction
          (sX.fiberToSpecResidueField η) x = (r : ℤ) → ∀ z : sY.fiber s,
      (properPushforward (fieldChowSituation (S.residueField s))
          (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s)
          (inducedFiberMap sX sY f hf s)
          (inducedFiberMap_fiberToSpecResidueField sX sY f hf s) (r : ℤ)
          (inverseImageCycle (fieldChowSituation (S.residueField s))
            (sX.fiberToSpecResidueField s) (sX.fiberι s) (r : ℤ) ((sX.fiberι η).base x))).1 z =
        fiberPushforwardWeight sX sY f hf η x *
          (inverseImageCycle (fieldChowSituation (S.residueField s))
            (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)
            ((sY.fiberι η).base ((inducedFiberMap sX sY f hf η).base x))).1 z)
    (α : FiberCycleGroup sX η r) (z : sY.fiber s) :
    (properPushforward (fieldChowSituation (S.residueField s))
        (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s) (inducedFiberMap sX sY f hf s)
        (inducedFiberMap_fiberToSpecResidueField sX sY f hf s) (r : ℤ)
        (fiberSpecializationMap sX η s r α)).1 z =
      ∑ᶠ x : sX.fiber η, α.1 x * fiberPushforwardWeight sX sY f hf η x *
        (inverseImageCycle (fieldChowSituation (S.residueField s))
          (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)
          ((sY.fiberι η).base ((inducedFiberMap sX sY f hf η).base x))).1 z := by
  have hcpt : IsCompact ((inducedFiberMap sX sY f hf s).base ⁻¹' {z}) :=
    (inducedFiberMap sX sY f hf s).isProperMap.isCompact_preimage isCompact_singleton
  have hstep : (properPushforward (fieldChowSituation (S.residueField s))
        (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s) (inducedFiberMap sX sY f hf s)
        (inducedFiberMap_fiberToSpecResidueField sX sY f hf s) (r : ℤ)
        (fiberSpecializationMap sX η s r α)).1 z =
      ∑ᶠ y : X, ofFiberCycle sX η α.1 y *
        (properPushforward (fieldChowSituation (S.residueField s))
          (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s)
          (inducedFiberMap sX sY f hf s)
          (inducedFiberMap_fiberToSpecResidueField sX sY f hf s) (r : ℤ)
          (inverseImageCycle (fieldChowSituation (S.residueField s))
            (sX.fiberToSpecResidueField s) (sX.fiberι s) (r : ℤ) y)).1 z :=
    ComponentRule.map_extendCycle_apply
      (inverseImageComponentRule (fieldChowSituation (S.residueField s))
        (sX.fiberToSpecResidueField s) (sX.fiberι s) (r : ℤ))
      (sX.fiberι s).continuous (inducedFiberMap sX sY f hf s).isSpectralMap _
      (ofFiberCycle sX η α.1) hcpt
  have hpt : ∀ x : sX.fiber η, α.1 x *
      (properPushforward (fieldChowSituation (S.residueField s))
        (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s) (inducedFiberMap sX sY f hf s)
        (inducedFiberMap_fiberToSpecResidueField sX sY f hf s) (r : ℤ)
        (inverseImageCycle (fieldChowSituation (S.residueField s))
          (sX.fiberToSpecResidueField s) (sX.fiberι s) (r : ℤ)
          ((sX.fiberι η).base x))).1 z =
      α.1 x * fiberPushforwardWeight sX sY f hf η x *
        (inverseImageCycle (fieldChowSituation (S.residueField s))
          (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)
          ((sY.fiberι η).base ((inducedFiberMap sX sY f hf η).base x))).1 z := by
    intro x
    by_cases hx : α.1 x = 0
    · rw [hx, zero_mul, zero_mul, zero_mul]
    · rw [hcompat x
        ((mem_cyclesOfDimension_iff_forall_point (fieldChowSituation (S.residueField η))
          (sX.fiberToSpecResidueField η) (r : ℤ) α.1).mp α.2 x hx) z, mul_assoc]
  have hfinL : (Function.support fun x : sX.fiber η ↦ α.1 x *
      (properPushforward (fieldChowSituation (S.residueField s))
        (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s) (inducedFiberMap sX sY f hf s)
        (inducedFiberMap_fiberToSpecResidueField sX sY f hf s) (r : ℤ)
        (inverseImageCycle (fieldChowSituation (S.residueField s))
          (sX.fiberToSpecResidueField s) (sX.fiberι s) (r : ℤ)
          ((sX.fiberι η).base x))).1 z).Finite := by
    rw [funext hpt]
    exact finite_support_specializationTerm sX sY f hf η s r α z
  rw [hstep, finsum_ofFiberCycle_mul sX η α.1 _ hfinL]
  exact finsum_congr hpt

/-- The coefficient of the specialization of a pushforward, as a locally finite sum over the
fibre over `η`: the sum over the fibre over `η` of the target is reindexed over the fibres of the
induced morphism of generic fibres. -/
private theorem fiberSpecializationMap_properPushforward_coeff (α : FiberCycleGroup sX η r)
    (z : sY.fiber s) :
    (fiberSpecializationMap sY η s r
        (properPushforward (fieldChowSituation (S.residueField η))
          (sX.fiberToSpecResidueField η) (sY.fiberToSpecResidueField η)
          (inducedFiberMap sX sY f hf η)
          (inducedFiberMap_fiberToSpecResidueField sX sY f hf η) (r : ℤ) α)).1 z =
      ∑ᶠ x : sX.fiber η, α.1 x * fiberPushforwardWeight sX sY f hf η x *
        (inverseImageCycle (fieldChowSituation (S.residueField s))
          (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)
          ((sY.fiberι η).base ((inducedFiberMap sX sY f hf η).base x))).1 z := by
  have hT := finite_support_specializationTerm sX sY f hf η s r α z
  have hfinR : (Function.support fun v : sY.fiber η ↦
      (properPushforward (fieldChowSituation (S.residueField η))
        (sX.fiberToSpecResidueField η) (sY.fiberToSpecResidueField η) (inducedFiberMap sX sY f hf η)
        (inducedFiberMap_fiberToSpecResidueField sX sY f hf η) (r : ℤ) α).1 v *
      (inverseImageCycle (fieldChowSituation (S.residueField s))
        (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)
        ((sY.fiberι η).base v)).1 z).Finite := by
    have hA := finite_support_inter_generalizations
      (ofFiberCycle sY η (properPushforward (fieldChowSituation (S.residueField η))
        (sX.fiberToSpecResidueField η) (sY.fiberToSpecResidueField η) (inducedFiberMap sX sY f hf η)
        (inducedFiberMap_fiberToSpecResidueField sX sY f hf η) (r : ℤ) α).1).locallyFiniteSupport
      (isCompact_singleton (x := (sY.fiberι s).base z))
    refine (Set.Finite.preimage ((sY.fiberι η).isEmbedding.injective.injOn) hA).subset ?_
    intro v hv
    replace hv : (properPushforward (fieldChowSituation (S.residueField η))
        (sX.fiberToSpecResidueField η) (sY.fiberToSpecResidueField η) (inducedFiberMap sX sY f hf η)
        (inducedFiberMap_fiberToSpecResidueField sX sY f hf η) (r : ℤ) α).1 v *
      (inverseImageCycle (fieldChowSituation (S.residueField s))
        (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)
        ((sY.fiberι η).base v)).1 z ≠ 0 := hv
    refine ⟨⟨(sY.fiberι s).base z, rfl, ?_⟩, ?_⟩
    · exact (inverseImageComponentRule (fieldChowSituation (S.residueField s))
        (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)).mem_closure_of_apply_ne_zero _ z
        (right_ne_zero_of_mul hv)
    · show ofFiberCycle sY η _ ((sY.fiberι η).base v) ≠ 0
      rw [ofFiberCycle_apply_fiberι]
      exact left_ne_zero_of_mul hv
  have hweight : ∀ x : sX.fiber η,
      (if relativeDimension (fieldChowSituation (S.residueField η)).dimensionFunction
            (sX.fiberToSpecResidueField η) x =
          relativeDimension (fieldChowSituation (S.residueField η)).dimensionFunction
            (sY.fiberToSpecResidueField η) ((inducedFiberMap sX sY f hf η).base x)
        then (((inducedFiberMap sX sY f hf η).residueDegree x : ℤ)) else 0) =
      fiberPushforwardWeight sX sY f hf η x := fun _ ↦ rfl
  rw [fiberSpecializationMap_apply, finsum_ofFiberCycle_mul sY η _ _ hfinR]
  have hfib : ∀ v : sY.fiber η,
      (properPushforward (fieldChowSituation (S.residueField η))
          (sX.fiberToSpecResidueField η) (sY.fiberToSpecResidueField η)
          (inducedFiberMap sX sY f hf η)
          (inducedFiberMap_fiberToSpecResidueField sX sY f hf η) (r : ℤ) α).1 v *
        (inverseImageCycle (fieldChowSituation (S.residueField s))
          (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ) ((sY.fiberι η).base v)).1 z =
      ∑ᶠ x ∈ (inducedFiberMap sX sY f hf η).base ⁻¹' {v},
        α.1 x * fiberPushforwardWeight sX sY f hf η x *
          (inverseImageCycle (fieldChowSituation (S.residueField s))
            (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)
            ((sY.fiberι η).base ((inducedFiberMap sX sY f hf η).base x))).1 z := by
    intro v
    rw [properPushforward_apply, finsum_mem_mul]
    refine finsum_mem_congr rfl fun x hx ↦ ?_
    have hxv : (inducedFiberMap sX sY f hf η).base x = v := hx
    rw [hweight x, hxv]
  rw [finsum_congr hfib]
  exact finsum_finsum_mem_fiber (inducedFiberMap sX sY f hf η).base _ hT

/-- **The extension from integral components to an arbitrary cycle**, over an arbitrary base
scheme and for an arbitrary pair of points of it.

Both sides are locally finite double sums; the proof evaluates each as the single locally finite
sum over the fibre over `η` of the coefficient of the cycle, the pushforward weight, and the
coefficient of the cycle of the inverse image of the closure of the image point. -/
private theorem properPushforward_fiberSpecializationMap_of_integralComponents
    (hcompat : ∀ x : sX.fiber η,
      relativeDimension (fieldChowSituation (S.residueField η)).dimensionFunction
          (sX.fiberToSpecResidueField η) x = (r : ℤ) → ∀ z : sY.fiber s,
      (properPushforward (fieldChowSituation (S.residueField s))
          (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s)
          (inducedFiberMap sX sY f hf s)
          (inducedFiberMap_fiberToSpecResidueField sX sY f hf s) (r : ℤ)
          (inverseImageCycle (fieldChowSituation (S.residueField s))
            (sX.fiberToSpecResidueField s) (sX.fiberι s) (r : ℤ) ((sX.fiberι η).base x))).1 z =
        fiberPushforwardWeight sX sY f hf η x *
          (inverseImageCycle (fieldChowSituation (S.residueField s))
            (sY.fiberToSpecResidueField s) (sY.fiberι s) (r : ℤ)
            ((sY.fiberι η).base ((inducedFiberMap sX sY f hf η).base x))).1 z)
    (α : FiberCycleGroup sX η r) :
    properPushforward (fieldChowSituation (S.residueField s))
        (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s) (inducedFiberMap sX sY f hf s)
        (inducedFiberMap_fiberToSpecResidueField sX sY f hf s) (r : ℤ)
        (fiberSpecializationMap sX η s r α) =
      fiberSpecializationMap sY η s r
        (properPushforward (fieldChowSituation (S.residueField η))
          (sX.fiberToSpecResidueField η) (sY.fiberToSpecResidueField η)
          (inducedFiberMap sX sY f hf η)
          (inducedFiberMap_fiberToSpecResidueField sX sY f hf η) (r : ℤ) α) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [properPushforward_fiberSpecializationMap_coeff sX sY f hf η s r hcompat α z,
    fiberSpecializationMap_properPushforward_coeff sX sY f hf η s r α z]

end ProperPushforward

/-! ### The two specialization maps agree -/

/-- The `k`-cycle of the inverse image in the fibre over `s` of the reduced closure of a point
of the ambient scheme, read as the cycle of a closed subscheme of that fibre. -/
theorem inverseImageCycle_eq_fiberSubschemeCycle {S X : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (s : S) (r : ℕ) (x : X) :
    inverseImageCycle (fieldChowSituation (S.residueField s)) (sX.fiberToSpecResidueField s)
        (sX.fiberι s) (r : ℤ) x =
      fiberSubschemeCycle sX s r ((integralComponentAt x).comap (sX.fiberι s)) :=
  rfl

/-- The coefficientwise formula for `Stacks.Chow.fiberSpecializationMap`, as a locally finite sum
over the fibre over `η` rather than over the ambient scheme. -/
theorem fiberSpecializationMap_apply_finsum {S X : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (η s : S) (r : ℕ) (c : FiberCycleGroup sX η r) (z : sX.fiber s)
    (hfin : (Function.support fun ξ : sX.fiber η ↦ c.1 ξ *
      (fiberSubschemeCycle sX s r
        ((integralComponentAt ((sX.fiberι η).base ξ)).comap (sX.fiberι s))).1 z).Finite) :
    (fiberSpecializationMap sX η s r c).1 z =
      ∑ᶠ ξ : sX.fiber η, c.1 ξ *
        (fiberSubschemeCycle sX s r
          ((integralComponentAt ((sX.fiberι η).base ξ)).comap (sX.fiberι s))).1 z := by
  rw [fiberSpecializationMap_apply, finsum_ofFiberCycle_mul sX η c.1 _ hfin]
  rfl

section Dvr

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X Y : Scheme.{u}}

/-- The cycle of the inverse image in the special fibre of the reduced closure of the image of a
point `ξ` of the generic fibre is the specialization of the fundamental cycle of `ξ`: the reduced
closure of the image of `ξ` is the scheme-theoretic image of the reduced closure of `ξ`. -/
theorem fiberSubschemeCycle_comap_eq_specializationIntegralCycle (sX : X ⟶ Spec (.of R))
    [LocallyOfFiniteType sX] (r : ℕ) (ξ : sX.fiber (genericPoint (Spec (.of R)))) :
    fiberSubschemeCycle sX (IsLocalRing.closedPoint R) r
        ((integralComponentAt ((sX.fiberι (genericPoint (Spec (.of R)))).base ξ)).comap
          (sX.fiberι (IsLocalRing.closedPoint R))) =
      specializationIntegralCycle sX r ξ := by
  show _ = fiberSubschemeCycle sX (IsLocalRing.closedPoint R) r
    (specializationSpecialFibre sX ξ)
  rw [specializationSpecialFibre, specializationClosure,
    map_integralComponentAt (sX.fiberι (genericPoint (Spec (.of R)))) ξ]

/-- **The two constructions of the specialization map agree.** The map built in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Specialization` out of a component rule and
the map built in `StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationCycle` out of
the coefficientwise formula are the same map. -/
theorem fiberSpecializationMap_eq_specializationCycle (sX : X ⟶ Spec (.of R))
    [LocallyOfFiniteType sX] (r : ℕ) (c : FiberCycleGroup sX (genericPoint (Spec (.of R))) r) :
    fiberSpecializationMap sX (genericPoint (Spec (.of R))) (IsLocalRing.closedPoint R) r c =
      specializationCycle sX r c := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  have hfin : (Function.support fun ξ : sX.fiber (genericPoint (Spec (.of R))) ↦ c.1 ξ *
      (fiberSubschemeCycle sX (IsLocalRing.closedPoint R) r
        ((integralComponentAt ((sX.fiberι (genericPoint (Spec (.of R)))).base ξ)).comap
          (sX.fiberι (IsLocalRing.closedPoint R)))).1 z).Finite := by
    simp only [fiberSubschemeCycle_comap_eq_specializationIntegralCycle]
    exact (locallyFinite_support_specializationTerm sX r c.1).point_finite z
  rw [fiberSpecializationMap_apply_finsum sX _ _ r c z hfin, specializationCycle_apply]
  exact finsum_congr fun ξ ↦ by
    rw [fiberSubschemeCycle_comap_eq_specializationIntegralCycle]

/-! ### Stacks 0H4M -/

/-- **Stacks 0H4M.** Let `R` be a discrete valuation ring with fraction field `K` and residue
field `κ`, let `f : X ⟶ Y` be a proper morphism of schemes locally of finite type over `R` and
let `r ≥ 0`. The square formed by the specialization maps `sp_{X/R} : Z_r(X_K) ⟶ Z_r(X_κ)` and
`sp_{Y/R} : Z_r(Y_K) ⟶ Z_r(Y_κ)` and the proper pushforwards along the morphisms `f_K` and
`f_κ` induced by `f` on the generic and the closed fibres commutes. -/
@[stacks 0H4M "the square of the specialization maps and the proper pushforwards commutes"]
theorem specializationCycle_fiberProperPushforward (sX : X ⟶ Spec (.of R))
    [LocallyOfFiniteType sX] (sY : Y ⟶ Spec (.of R)) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [IsProper f] (hf : f ≫ sY = sX) (r : ℕ)
    (c : FiberCycleGroup sX (genericPoint (Spec (.of R))) r) :
    fiberProperPushforward sX sY f hf (IsLocalRing.closedPoint R) r
        (specializationCycle sX r c) =
      specializationCycle sY r
        (fiberProperPushforward sX sY f hf (genericPoint (Spec (.of R))) r c) := by
  rw [← fiberSpecializationMap_eq_specializationCycle,
    ← fiberSpecializationMap_eq_specializationCycle]
  refine properPushforward_fiberSpecializationMap_of_integralComponents sX sY f hf
    (genericPoint (Spec (.of R))) (IsLocalRing.closedPoint R) r ?_ c
  intro x hx z
  have he1 := (inverseImageCycle_eq_fiberSubschemeCycle sX (IsLocalRing.closedPoint R) r
      ((sX.fiberι (genericPoint (Spec (.of R)))).base x)).trans
    (fiberSubschemeCycle_comap_eq_specializationIntegralCycle sX r x)
  have he2 := (inverseImageCycle_eq_fiberSubschemeCycle sY (IsLocalRing.closedPoint R) r
      ((sY.fiberι (genericPoint (Spec (.of R)))).base
        ((inducedFiberMap sX sY f hf (genericPoint (Spec (.of R)))).base x))).trans
    (fiberSubschemeCycle_comap_eq_specializationIntegralCycle sY r
      ((inducedFiberMap sX sY f hf (genericPoint (Spec (.of R)))).base x))
  rw [he1, he2]
  have hstar := properPushforward_specializationIntegralCycle sX sY f hf r x hx
  have hz := congrArg
    (fun w : FiberCycleGroup sY (IsLocalRing.closedPoint R) r ↦
      (w : AlgebraicCycle (sY.fiber (IsLocalRing.closedPoint R)) ℤ) z) hstar
  have hz2 : (fiberProperPushforward sX sY f hf (IsLocalRing.closedPoint R) r
        (specializationIntegralCycle sX r x) :
      AlgebraicCycle (sY.fiber (IsLocalRing.closedPoint R)) ℤ) z =
    fiberPushforwardWeight sX sY f hf (genericPoint (Spec (.of R))) x *
      (specializationIntegralCycle sY r
          ((inducedFiberMap sX sY f hf (genericPoint (Spec (.of R)))).base x) :
        AlgebraicCycle (sY.fiber (IsLocalRing.closedPoint R)) ℤ) z := by
    simpa using hz
  exact hz2

/-- The specialization map `sp_{X/R}` of Stacks 0H4H is the coefficientwise specialization of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationCycle`. -/
@[simp]
theorem specializationMap_apply (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (sX : X ⟶ Spec (.of R))
    [LocallyOfFiniteType sX] (r : ℕ)
    (c : FiberCycleGroup sX (genericPoint (Spec (.of R))) r) :
    specializationMap R sX r c = specializationCycle sX r c :=
  fiberSpecializationMap_eq_specializationCycle sX r c

/-- **Stacks 0H4M**, read on the specialization map `sp_{X/R}` of Stacks 0H4H: the square
formed by `sp_{X/R}`, `sp_{Y/R}` and the proper pushforwards along the morphisms induced by `f`
on the generic and the closed fibres commutes. -/
@[stacks 0H4M "the square, read on the specialization map sp_{X/R} of Stacks 0H4H"]
theorem properPushforward_specializationMap (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of R))
    [LocallyOfFiniteType sX] (sY : Y ⟶ Spec (.of R)) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [IsProper f] (hf : f ≫ sY = sX) (r : ℕ)
    (α : FiberCycleGroup sX (genericPoint (Spec (.of R))) r) :
    fiberProperPushforward sX sY f hf (IsLocalRing.closedPoint R) r
        (specializationMap R sX r α) =
      specializationMap R sY r
        (fiberProperPushforward sX sY f hf (genericPoint (Spec (.of R))) r α) := by
  rw [specializationMap_apply, specializationMap_apply]
  exact specializationCycle_fiberProperPushforward sX sY f hf r α

end Dvr

end Stacks.Chow

end
