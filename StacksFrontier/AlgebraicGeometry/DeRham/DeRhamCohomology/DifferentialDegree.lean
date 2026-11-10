module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DeRham.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.FormsDirectSum

/-!
# The de Rham differential preserves total degree

Give the differential forms of a graded algebra the grading in which the total degree of
`a₀ ⋅ da₁ ∧ ⋯ ∧ daₚ` is the sum of the degrees of the homogeneous elements `aᵢ`. The de Rham
differential then carries the degree-`g` component in exterior degree `p` into the degree-`g`
component in exterior degree `p + 1`: it raises exterior degree by one and leaves the total
degree unchanged.

## Main results

* `KaehlerDifferential.deRhamDifferential_maps_gradedDifferentialFormComponent` says that a map
  satisfying the defining rule for the de Rham differential preserves total degree.

## Implementation notes

The result is stated for any linear map satisfying the characteristic rule of the de Rham
differential; by the existence and uniqueness theorem for that differential this is precisely the
differential of the de Rham complex. Only the condition that `1` has degree zero is needed from
the grading hypotheses, because after applying the differential each homogeneous generator is
represented with coefficient `1`; the internal direct-sum property and multiplicative
compatibility are not used.

## References

* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9)
-/

@[expose] public section

namespace KaehlerDifferential

universe u v w

/-- The de Rham differential preserves the total degree of homogeneous
differential forms. -/
@[stacks 0FU9 "differential_preserves_degree"]
theorem deRhamDifferential_maps_gradedDifferentialFormComponent
    {G : Type u} {R : Type v} {A : Type w}
    [AddCommMonoid G] [CommRing R] [CommRing A] [Algebra R A]
    (gr : G → Submodule R A) (hunit : (1 : A) ∈ gr 0) (p : ℕ) (g : G)
    (d : (⋀[A]^p (KaehlerDifferential R A)) →ₗ[R]
      (⋀[A]^(p + 1) (KaehlerDifferential R A)))
    (hd : ∀ a : Fin (p + 1) → A,
      d (a 0 • exteriorPower.ιMulti A p (fun i ↦
        KaehlerDifferential.D R A (a i.succ))) =
        exteriorPower.ιMulti A (p + 1) (fun i ↦
          KaehlerDifferential.D R A (a i))) :
    Submodule.map d (gradedDifferentialFormComponent gr p g) ≤
      gradedDifferentialFormComponent gr (p + 1) g := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.2
  rintro x ⟨degree, a, hg, rfl⟩
  change d ((a 0 : A) • exteriorPower.ιMulti A p (fun i ↦
    KaehlerDifferential.D R A (a i.succ : A))) ∈
      gradedDifferentialFormComponent gr (p + 1) g
  rw [hd (fun i ↦ (a i : A))]
  apply Submodule.subset_span
  refine ⟨Fin.cons 0 degree, Fin.cases ⟨1, hunit⟩ a, ?_, ?_⟩
  · simpa [Fin.sum_univ_succ] using hg
  · change _ = (1 : A) • exteriorPower.ιMulti A (p + 1)
      (fun i ↦ KaehlerDifferential.D R A (a i : A))
    simp

end KaehlerDifferential
