module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniHypotheses

/-!
# A chart on which the first section of the Bertini situation is invertible

Let `D` be a family of divisors satisfying the hypotheses of the Bertini irreducibility theorem.
Since `Z ⊄ |H_{v₁}|`, there is a trivializing affine chart meeting `Z` on which the function
representing `ψ(v₁)` is invertible: a point of `Z` outside `|H_{v₁}|` has a trivializing affine
neighbourhood inside the complement of `|H_{v₁}|`, and on it the function of `v₁` vanishes
nowhere.

## Main results

* `Stacks.Bertini.FamilyDivisors.isUnit_chartFunction_of_subset_compl_divisorSet`: on a
  trivializing affine open avoiding `|H_w|` the function representing `ψ(w)` is a unit.
* `Stacks.Bertini.FamilyDivisors.chartFunction_eq_sum`: the function of a vector is the
  corresponding combination of the functions of the basis, with coefficients the images of the
  coordinates of the vector under `k → Γ(U, ⊤)`.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.exists_chart_isUnit_chartFunction`: there is a
  trivializing affine chart meeting `Z` on which the function of `v₁` is a unit.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

namespace Stacks.Bertini.FamilyDivisors

section Chart

variable {D : FamilyDivisors.{u, v}} {U : D.X.Opens}
  (eU : D.restrictedModule U ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- The function of a vector is the corresponding combination of the functions of the basis, with
coefficients the images in `Γ(U, ⊤)` of the coordinates of the vector, through the structure
morphism of `X` restricted to `U`. -/
theorem chartFunction_eq_sum (w : D.V) :
    chartFunction eU w =
      ∑ i, U.ι.appTop (D.baseScalar (D.basis.repr w i)) * D.chartEquation eU i := by
  classical
  show chartFrameSections eU (D.restrictedSection U w) = _
  rw [D.restrictedSection_eq_sum w, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- If the trivializing affine open `U` avoids the support of `H_w` then the function
`f_w ∈ Γ(U, ⊤)` representing `ψ(w)` is invertible. -/
theorem isUnit_chartFunction_of_subset_compl_divisorSet [IsAffine U.toScheme] (w : D.V)
    (hU : (U : Set D.X) ⊆ (D.divisorSet w)ᶜ) : IsUnit (chartFunction eU w) := by
  refine RingedSpace.isUnit_of_isUnit_germ U.toScheme.toLocallyRingedSpace.toRingedSpace ⊤
    (chartFunction eU w) fun x hx ↦ ?_
  have hmem : U.ι.base x ∈ (U : Set D.X) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩
  have hz : x ∉ U.toScheme.zeroLocus (U := ⊤) {chartFunction eU w} := fun hc ↦
    hU hmem ((mem_divisorSet_iff eU w x).mpr hc)
  rw [Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not] at hz
  exact (U.toScheme.mem_basicOpen (chartFunction eU w) x hx).mp hz

end Chart

namespace Hypotheses

variable {D : FamilyDivisors.{u, v}} (h : D.Hypotheses)

include h

/-- There is a trivializing affine chart meeting `Z` on which the function of `v₁` is
invertible. -/
@[stacks 0G4F "hypothesis (3) as an invertible section on a chart meeting Z"]
theorem exists_chart_isUnit_chartFunction :
    ∃ c : D.Chart, ((c.U : Set D.X) ∩ (h.Z : Set D.X)).Nonempty ∧
      IsUnit (chartFunction c.triv h.v₁) := by
  obtain ⟨x, hxZ, hxv⟩ := Set.not_subset.mp h.Z_not_subset
  obtain ⟨c, hcW, hxc⟩ := D.exists_chart_le
    ⟨(D.divisorSet h.v₁)ᶜ, (D.isClosed_divisorSet h.v₁).isOpen_compl⟩ x hxv
  exact ⟨c, ⟨x, hxc, hxZ⟩,
    isUnit_chartFunction_of_subset_compl_divisorSet c.triv h.v₁ fun _ hy ↦ hcW hy⟩

end Hypotheses

end Stacks.Bertini.FamilyDivisors

end
