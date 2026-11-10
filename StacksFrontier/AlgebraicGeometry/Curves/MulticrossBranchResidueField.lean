module

public import StacksFrontier.AlgebraicGeometry.Curves.MulticrossNormalization

/-!
# The residue fields of the normalization of the two-branch multicross ring

The normalization of the two-branch multicross ring is `k[[t]] × k[[t]]`
(`Stacks.Curves.integralClosureMulticrossAlgEquiv`), whose maximal ideals are the two branch
maximal ideals `Stacks.Curves.branchMaximalIdeal` (`Stacks.Curves.eq_branchMaximalIdeal`). This
file computes the residue field at each of them: it is the ground field `k`
(`Stacks.Curves.quotientBranchMaximalIdealAlgEquiv`), so the residue-field extension at every
maximal ideal of the normalization of a node in Case I of Stacks Tag 0C4A is trivial, in
particular separable.

The residue field at the `i`-th branch maximal ideal is identified with `k` through the
surjective `k`-algebra map `Stacks.Curves.branchResidueHom` taking a pair of power series to the
constant coefficient of its `i`-th component, whose kernel is the branch maximal ideal.

## Main definitions

* `Stacks.Curves.branchResidueHom` — evaluation of one branch at the origin.

## Main results

* `Stacks.Curves.ker_branchResidueHom` — its kernel is the branch maximal ideal.
* `Stacks.Curves.quotientBranchMaximalIdealAlgEquiv` — the residue field at a branch maximal
  ideal of `k[[t]] × k[[t]]` is `k`.
* `Stacks.Curves.finrank_quotient_branchMaximalIdeal` — that residue field has degree one
  over `k`.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

/-- Evaluation of the `i`-th branch of a pair of one-variable power series at the origin. -/
def branchResidueHom (k : Type u) [Field k] (i : Fin 2) : (Fin 2 → PowerSeries k) →ₐ[k] k where
  toRingHom := (PowerSeries.constantCoeff (R := k)).comp
    (Pi.evalRingHom (fun _ : Fin 2 ↦ PowerSeries k) i)
  commutes' := fun r ↦ by
    change PowerSeries.constantCoeff (algebraMap k (Fin 2 → PowerSeries k) r i) = r
    simp

/-- `branchResidueHom k i f` is the constant coefficient of the `i`-th component of `f`. -/
theorem branchResidueHom_apply (i : Fin 2) (f : Fin 2 → PowerSeries k) :
    branchResidueHom k i f = PowerSeries.constantCoeff (f i) :=
  rfl

/-- Evaluation of the `i`-th branch at the origin is surjective onto `k`. -/
theorem branchResidueHom_surjective (i : Fin 2) :
    Function.Surjective (branchResidueHom k i) := fun r ↦
  ⟨fun _ ↦ PowerSeries.C r, by simp [branchResidueHom_apply]⟩

/-- **The kernel of evaluation of the `i`-th branch at the origin is the `i`-th branch maximal
ideal of `k[[t]] × k[[t]]`.** -/
theorem ker_branchResidueHom (i : Fin 2) :
    RingHom.ker (branchResidueHom k i).toRingHom = branchMaximalIdeal k i := by
  refine Ideal.ext fun f ↦ ?_
  rw [RingHom.mem_ker, mem_branchMaximalIdeal, PowerSeries.isUnit_iff_constantCoeff]
  change PowerSeries.constantCoeff (f i) = 0 ↔ ¬ IsUnit (PowerSeries.constantCoeff (f i))
  rw [isUnit_iff_ne_zero, not_not]

/-- **The residue field at a branch maximal ideal of `k[[t]] × k[[t]]` is `k`.** -/
def quotientBranchMaximalIdealAlgEquiv (k : Type u) [Field k] (i : Fin 2) :
    ((Fin 2 → PowerSeries k) ⧸ branchMaximalIdeal k i) ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq k (ker_branchResidueHom i).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (branchResidueHom_surjective i))

/-- The residue field at a branch maximal ideal of `k[[t]] × k[[t]]` has degree one over `k`. -/
theorem finrank_quotient_branchMaximalIdeal (i : Fin 2) :
    Module.finrank k ((Fin 2 → PowerSeries k) ⧸ branchMaximalIdeal k i) = 1 := by
  rw [(quotientBranchMaximalIdealAlgEquiv k i).toLinearEquiv.finrank_eq,
    Module.finrank_self]

end Stacks.Curves

end
