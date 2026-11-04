module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardLocallyTrivial

/-!
# The Picard group of a one-point scheme is trivial

The Picard group of a scheme with exactly one point, in particular of the spectrum of a field, is
zero.

## Main results

* `Stacks.Picard.eq_zero_of_subsingleton`: the Picard group of a scheme with exactly one point is
  trivial.
* `Stacks.Picard.eq_zero_of_isField`: the Picard group of `Spec K` for a field `K` is trivial.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Picard

/-- **The Picard group of a scheme with exactly one point is trivial.** -/
theorem eq_zero_of_subsingleton {Y : Scheme.{u}} [Subsingleton Y] [Nonempty Y] (N : ofScheme Y) :
    N = 0 := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  obtain ⟨U, hyU, hU⟩ := exists_mem_schemePullbackClass_eq_zero N y
  have hUtop : U = ⊤ := by
    ext z
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact Subsingleton.elim y z ▸ hyU
  subst hUtop
  have h := congrArg (schemePullbackClass Y.topIso.inv) hU
  rwa [schemePullbackClass_comp, Scheme.toIso_inv_ι, schemePullbackClass_id,
    show schemePullbackClass Y.topIso.inv 0 = 0 from
      map_zero (schemePullbackClassHom _)] at h

/-- **The Picard group of the spectrum of a field is trivial.** -/
theorem eq_zero_of_isField (K : Type u) [Field K] (N : ofScheme (Spec (.of K))) : N = 0 := by
  have : Subsingleton (Spec (CommRingCat.of K)) := by
    show Subsingleton (PrimeSpectrum K); infer_instance
  have : Nonempty (Spec (CommRingCat.of K)) := by
    show Nonempty (PrimeSpectrum K); infer_instance
  exact eq_zero_of_subsingleton N

end Stacks.Picard
