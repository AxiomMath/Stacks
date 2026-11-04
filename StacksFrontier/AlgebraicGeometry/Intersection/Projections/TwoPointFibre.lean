module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.DualClosedPoints

/-!
# The endomorphisms carrying one point of a projective space to another

A closed point of `𝐏(V) = Proj (Sym V)` is the class `[f]` of a nonzero linear functional on `V`,
and the projective transformation attached to an endomorphism `g` of `V` sends `[f]` to
`[f ∘ g]`. So the endomorphisms carrying `[f]` to `[f']` are those with `f ∘ g ∈ k ∙ f'`, and
that locus is the preimage of a line under a *linear* map: a linear subspace of `End V` of
corank `dim V - 1`.

This is what makes the fibres of the two-point map `([g], x) ↦ (x, g · x)` tractable without any
group-scheme theory. Each fibre is a nonempty open subset of the projective linear subspace cut
out by this submodule, hence irreducible of dimension `(dim V)² - dim V`, which is
`dim 𝐏((End V)ᵛ) - dim 𝐏(V)`; the stabiliser of a point of `𝐏(V)` is the case `f' = f`.

That projective linear subspace, its dimension and its irreducibility are
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEquations`,
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_linearSubspace_transitionEquations`
and
`AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_linearSubspace_transitionEquations` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionLocus`, which also records
what the incidence variety of Tag 0B1S still owes.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.dualPostcomp`: the linear map `g ↦ f ∘ g` on
  `End V`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSubmodule`: the submodule of `End V` of
  endomorphisms carrying `[f]` to `[f']`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.surjective_dualPostcomp`: `g ↦ f ∘ g` is surjective
  onto `Vᵛ` for `f ≠ 0`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionSubmodule_iff`: membership is the
  condition `f ∘ g ∈ k ∙ f'`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.finrank_quotient_transitionSubmodule`: the corank is
  `dim V - 1`, stated without subtraction as `corank + 1 = dim V`.

## References

* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
-/

@[expose] public section

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **Postcomposition with a linear functional**, as a linear map on `End V`: it sends `g` to
`f ∘ g`, which is the functional cutting out the image of the point `[f]` under the projective
transformation attached to `g`. -/
public noncomputable def dualPostcomp (f : Module.Dual k V) :
    (V →ₗ[k] V) →ₗ[k] Module.Dual k V :=
  LinearMap.llcomp k V V k f

/-- `dualPostcomp k V f` sends an endomorphism `g` to the composite `f ∘ₗ g`. -/
@[simp]
public theorem dualPostcomp_apply (f : Module.Dual k V) (g : V →ₗ[k] V) :
    dualPostcomp k V f g = f ∘ₗ g := rfl

/-- **Postcomposition with a nonzero functional is surjective.** Given `h : Vᵛ` and a vector `v`
with `f v = 1`, the endomorphism `w ↦ h w • v` composes with `f` to give `h`. -/
public theorem surjective_dualPostcomp {f : Module.Dual k V} (hf : f ≠ 0) :
    Function.Surjective (dualPostcomp k V f) := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hc
    exact hf (LinearMap.ext fun v => not_not.mp (not_exists.mp hc v))
  intro h
  refine ⟨LinearMap.smulRight h ((f v)⁻¹ • v), LinearMap.ext fun w => ?_⟩
  rw [dualPostcomp_apply, LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ hv, mul_one]

/-- **The endomorphisms carrying `[f]` to `[f']`.** The preimage under `g ↦ f ∘ g` of the line
spanned by `f'`: a linear subspace of `End V`. -/
public noncomputable def transitionSubmodule (f f' : Module.Dual k V) :
    Submodule k (V →ₗ[k] V) :=
  Submodule.comap (dualPostcomp k V f) (Submodule.span k {f'})

/-- An endomorphism `g` lies in `transitionSubmodule k V f f'` exactly when `f ∘ₗ g` lies in the
line spanned by `f'`. -/
@[simp]
public theorem mem_transitionSubmodule_iff (f f' : Module.Dual k V) (g : V →ₗ[k] V) :
    g ∈ transitionSubmodule k V f f' ↔ f ∘ₗ g ∈ Submodule.span k {f'} := Iff.rfl

/-- **The corank of that subspace is `dim V - 1`**, stated without subtraction. Postcomposition
with `f` is surjective, so the quotient of `End V` by the subspace is the quotient of `Vᵛ` by the
line spanned by `f'`, which has codimension one in a space of dimension `dim V`. -/
public theorem finrank_quotient_transitionSubmodule [FiniteDimensional k V]
    {f f' : Module.Dual k V} (hf : f ≠ 0) (hf' : f' ≠ 0) :
    Module.finrank k ((V →ₗ[k] V) ⧸ transitionSubmodule k V f f') + 1 = Module.finrank k V := by
  set L := Submodule.span k {f'} with hL
  set Φ := (L.mkQ).comp (dualPostcomp k V f) with hΦ
  have hsurj : Function.Surjective Φ :=
    L.mkQ_surjective.comp (surjective_dualPostcomp k V hf)
  have hker : LinearMap.ker Φ = transitionSubmodule k V f f' := by
    rw [hΦ, LinearMap.ker_comp, Submodule.ker_mkQ]
    rfl
  have e : ((V →ₗ[k] V) ⧸ transitionSubmodule k V f f') ≃ₗ[k] (Module.Dual k V ⧸ L) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)
  rw [e.finrank_eq]
  have hquot := Submodule.finrank_quotient_add_finrank (R := k) L
  rw [finrank_span_singleton hf', Subspace.dual_finrank_eq] at hquot
  omega

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
