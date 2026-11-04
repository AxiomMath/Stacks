module

public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyExtension

/-! # Null-homotopies out of a direct sum of differential graded modules

A homomorphism out of a differential graded module whose underlying right module is a direct
sum is null-homotopic as soon as each of its restrictions to the summands is: the component
homotopies assemble, because every element of a direct sum has finite support. Consequently a
differential graded module presented as a direct sum of modules orthogonal on the left to the
acyclic ones is itself orthogonal on the left to them.

This is the form in which the graded pieces of a property-(P) filtration — direct sums of
shifts of the algebra — are recognised as orthogonal.

## Main results

* `DifferentialGradedModule.leftOrthogonal_acyclic_of_directSum`: a differential graded module
  presented as a direct sum of modules orthogonal on the left to the acyclic modules is itself
  orthogonal on the left to them.

## Implementation notes

The presentation is taken as data rather than as a universal property: an `A`-linear
equivalence from `⨁ j, (X j).M` onto the carrier, carrying the `j`-th coprojection to a given
homomorphism `X j ⟶ T`, and reflecting homogeneity componentwise. The direct sums occurring in
this chapter are concrete, and assembling the homotopies by hand needs only finite support, so
no universal property is required.

The differential of the direct sum is *not* `A`-linear, so the componentwise differential is
built with `DirectSum.toAddMonoid` rather than `DirectSum.toModule`; only additivity is needed
of it, and that avoids having to name a ring over which it is linear.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules all live in a single universe `u`, following the `DifferentialGradedAlgebra` encoding
of Stacks Tag 09JJ.

## References

* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), in whose proof the
  graded pieces of a property-(P) filtration are direct sums of shifts of the algebra.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- A differential graded module presented as a direct sum of modules orthogonal on the left to
the acyclic differential graded modules is itself orthogonal on the left to them.

The presentation is an `A`-linear equivalence `ev` from `⨁ j, (X j).M` onto the carrier of `T`
which carries the `j`-th coprojection to `inj j` and reflects homogeneity componentwise. -/
theorem leftOrthogonal_acyclic_of_directSum
    {ι : Type u} [DecidableEq ι] {X : ι → DifferentialGradedModule A}
    {T : DifferentialGradedModule A} (inj : ∀ j, X j ⟶ T)
    (ev : (⨁ j, (X j).M) ≃ₗ[MulOpposite A.A] T.M)
    (hev : ∀ j x, ev (DirectSum.of (fun j => (X j).M) j x) = (inj j).toFun x)
    (hgr : ∀ (n : ℤ) (z : ⨁ j, (X j).M), ev z ∈ T.grading n → ∀ j, z j ∈ (X j).grading n)
    (hX : ∀ j, (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (X j))) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj T) := by
  classical
  rw [leftOrthogonal_acyclic_iff]
  intro N hN f
  -- a null-homotopy on each summand
  have h : ∀ j, Homotopy (inj j ≫ f) 0 :=
    fun j => ((leftOrthogonal_acyclic_iff (X j)).1 (hX j) N hN (inj j ≫ f)).some
  -- their assembly over the direct sum
  set Hsum : (⨁ j, (X j).M) →ₗ[MulOpposite A.A] N.M :=
    DirectSum.toModule (MulOpposite A.A) ι N.M (fun j => (h j).toLinearMap) with hHsumdef
  have hHsum_of : ∀ j x, Hsum (DirectSum.of (fun j => (X j).M) j x) = (h j).toLinearMap x := by
    intro j x
    rw [hHsumdef, ← DirectSum.lof_eq_of (MulOpposite A.A), DirectSum.toModule_lof]
  -- the componentwise differential of the direct sum
  set dsum : (⨁ j, (X j).M) →+ (⨁ j, (X j).M) :=
    DirectSum.toAddMonoid (fun j =>
      (DirectSum.of (fun j => (X j).M) j).comp (X j).d.toAddMonoidHom) with hdsumdef
  have hdsum_of : ∀ j x, dsum (DirectSum.of (fun j => (X j).M) j x)
      = DirectSum.of (fun j => (X j).M) j ((X j).d x) := by
    intro j x
    rw [hdsumdef, DirectSum.toAddMonoid_of]
    rfl
  -- the presentation carries the componentwise differential to the differential of `T`
  have hd : ∀ z, T.d (ev z) = ev (dsum z) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of j x =>
      rw [hev, hdsum_of, hev]
      exact (LinearMap.congr_fun (inj j).map_d x).symm
    | add z w hz hw => simp only [map_add, hz, hw]
  -- the glued homotopy
  refine ⟨{ toLinearMap := Hsum ∘ₗ (ev.symm : T.M →ₗ[MulOpposite A.A] (⨁ j, (X j).M))
            map_grading := ?_
            homotopy_eq := ?_ }⟩
  · intro n t ht
    show Hsum (ev.symm t) ∈ N.grading (n - 1)
    have hcomp : ∀ j, (ev.symm t) j ∈ (X j).grading n :=
      hgr n (ev.symm t) (by rw [ev.apply_symm_apply]; exact ht)
    rw [← DirectSum.sum_support_of (ev.symm t), map_sum]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [hHsum_of]
    exact (h j).map_grading n _ (hcomp j)
  · have key : ∀ z, f.toFun (ev z) = N.d (Hsum z) + Hsum (dsum z) := by
      intro z
      induction z using DirectSum.induction_on with
      | zero => simp
      | of j x =>
        have heq := (h j).homotopy_eq x
        simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero,
          Hom.comp_toFun_apply] at heq
        rw [hev, hHsum_of, hdsum_of, hHsum_of, heq]
      | add z w hz hw =>
        simp only [map_add, hz, hw]
        abel
    intro t
    show f.toFun t - (0 : T ⟶ N).toFun t
      = N.d (Hsum (ev.symm t)) + Hsum (ev.symm (T.d t))
    simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero]
    rw [show t = ev (ev.symm t) from (ev.apply_symm_apply t).symm, hd,
      ev.symm_apply_apply, ev.symm_apply_apply, key]

end DifferentialGradedModule
