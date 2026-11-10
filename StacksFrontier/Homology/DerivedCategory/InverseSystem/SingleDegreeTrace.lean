module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower

/-!
# The trace of an endomorphism of a perfect complex concentrated in degree zero

For a finite free module `M` over a commutative ring `R`, placed in degree `0`, the trace in the
sense of [Tag 03TH](https://stacks.math.columbia.edu/tag/03TH) of the endomorphism induced by
`g : M ⟶ M`, evaluated in `R`, is the ordinary trace of `g`. This is the form in which the local
terms `Tr(π_x | K_x̄)` of the trace formula of [Tag 03V3] reduce to traces on stalks when the
coefficient complex is a flat sheaf placed in degree `0`, as in the proof of
[Tag 03V2](https://stacks.math.columbia.edu/tag/03V2).

## Main results

* `CategoryTheory.FilteredDerived.eval_perfectDerivedTrace_single`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Trace

universe v

namespace CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

/-- **The trace of an endomorphism of a finite free module placed in degree `0`** is its
ordinary trace. -/
theorem eval_perfectDerivedTrace_single {R : Type} [CommRing R] (M : ModuleCat.{v} R)
    [Module.Free R M] [Module.Finite R M]
    (hK : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M)))
    (g : M ⟶ M) :
    commutativeAdditiveCommutatorQuotientEval R (perfectDerivedTrace R ⟨_, hK⟩
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g))) =
      LinearMap.trace R M g.hom := by
  classical
  let P := (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M
  have hsub : ∀ i : ℤ, i ≠ 0 → Subsingleton (P.X i) := fun i hi =>
    ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
  let e₀ : P.X 0 ≅ M := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M
  have hfree : ∀ i, Module.Free R (P.X i) ∧ Module.Finite R (P.X i) := fun i => by
    by_cases hi : i = 0
    · subst hi
      exact ⟨Module.Free.of_equiv e₀.symm.toLinearEquiv,
        Module.Finite.equiv e₀.symm.toLinearEquiv⟩
    · have := hsub i hi
      exact ⟨inferInstance, inferInstance⟩
  have hP : finiteProjectiveComplex R P := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun i => ?_⟩
    have := (hfree i).1
    exact ⟨inferInstance, (hfree i).2⟩
  have : ∀ i, Module.Free R (P.X i) := fun i => (hfree i).1
  rw [perfectDerivedTrace_eq_alternatingTrace R ⟨_, hK⟩ _ P hP (Iso.refl _)
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g) (Category.comp_id _).symm,
    Stacks.InverseSystem.alternatingTrace_eval_eq_sum_trace, finsum_eq_single _ 0 (fun i hi => by
      have := hsub i hi
      rw [show (((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g).f i).hom = 0 from
        LinearMap.ext fun _ => Subsingleton.elim _ _, map_zero, mul_zero])]
  have hg : ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g).f 0 = e₀.hom ≫ g ≫ e₀.inv :=
    HomologicalComplex.single_map_f_self _ _ _
  rw [ite_eq_left Even.zero, one_mul, hg, ← LinearMap.trace_conj' g.hom e₀.symm.toLinearEquiv]
  rfl

end CategoryTheory.FilteredDerived
