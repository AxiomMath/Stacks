module

public import Mathlib.LinearAlgebra.Isomorphisms
public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective

/-! # A criterion for a short exact sequence to be admissible

An admissible monomorphism `f : K ⟶ L` of right differential graded modules and a surjection
`g : L ⟶ N` whose kernel is the image of `f` always form an *admissible* short exact sequence:
the graded splitting of `f` already produces one for `g`, with no hypothesis on `N` beyond the
exactness. This is the form in which the successive steps of a filtration whose inclusions are
admissible — a property-(P) filtration, say — are recognised as admissible short exact
sequences, with the quotients presented by a surjection onto a prescribed module rather than as
the canonical cokernel.

The section is the descent of `x ↦ x - f (r x)` along `g`, where `r` is a graded retraction of
`f`. That map kills the image of `f`, hence the kernel of `g`, so it factors through `g`
uniquely; it is a section of `g` because `f (r x)` lies in the kernel of `g`; and it is graded
because `g`, being surjective and degree-preserving, is already surjective on each homogeneous
piece.

## Main results

* `DifferentialGradedModule.isAdmissibleShortExact_of_ker_eq_range`: an admissible
  monomorphism and a surjection whose kernel is its image form an admissible short exact
  sequence.

## Implementation notes

`DifferentialGradedModule.Hom.isAdmissibleShortExact_cokernelπ` is the special case in which
`N` is the canonical cokernel and `g` the canonical projection. Neither statement follows from
the other by transport along the comparison isomorphism `L / f(K) ≃ N`, because that comparison
is produced by the first isomorphism theorem as a map of `R`-modules only; so the graded section
is built here directly, from the same retraction.

## References

* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT)
-/

@[expose] public noncomputable section

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
  {K L N : DifferentialGradedModule A}

/-- An admissible monomorphism `f : K ⟶ L` and a surjection `g : L ⟶ N` whose kernel is the
image of `f` form an admissible short exact sequence. The graded section of `g` is obtained from
a graded retraction `r` of `f` by descending `x ↦ x - f (r x)` along `g`. -/
theorem isAdmissibleShortExact_of_ker_eq_range (f : Hom K L) (g : Hom L N)
    (hf : IsAdmissibleMono f) (hg : Function.Surjective g.toFun)
    (hker : LinearMap.ker g.toFun = LinearMap.range f.toFun) :
    IsAdmissibleShortExact f g := by
  obtain ⟨r, hr⟩ := id hf
  have hsub : LinearMap.ker g.toFun ≤ LinearMap.ker (LinearMap.id - f.toFun ∘ₗ r.toFun) := by
    intro x hx
    rw [hker, LinearMap.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_coe, id_eq,
      LinearMap.comp_apply, hr y, sub_self]
  obtain ⟨s, hs⟩ : ∃ s : N.M →ₗ[R] L.M,
      ∀ x : L.M, s (g.toFun x) = x - f.toFun (r.toFun x) := by
    refine ⟨(LinearMap.ker g.toFun).liftQ (LinearMap.id - f.toFun ∘ₗ r.toFun) hsub ∘ₗ
      (g.toFun.quotKerEquivOfSurjective hg).symm.toLinearMap, fun x => ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply]
  have hzero (x : L.M) : g.toFun (f.toFun (r.toFun x)) = 0 := by
    rw [← LinearMap.mem_ker, hker]
    exact ⟨r.toFun x, rfl⟩
  refine { injective := hf.injective
           surjective := hg
           exact := hker.symm
           admissibleMono := hf
           admissibleEpi := ⟨{ toFun := s, map_smul := ?_, map_grading := ?_ }, ?_⟩ }
  · intro z a
    obtain ⟨x, rfl⟩ := hg z
    rw [← g.map_smul, hs, hs, r.map_smul, f.map_smul, smul_sub]
  · intro n z hz
    obtain ⟨x, hx, rfl⟩ := Hom.exists_mem_grading_of_surjective hg hz
    rw [hs]
    exact (L.grading n).sub_mem hx (f.map_grading n _ (r.map_grading n x hx))
  · intro z
    obtain ⟨x, rfl⟩ := hg z
    rw [hs, map_sub, hzero, sub_zero]

end DifferentialGradedModule

end
