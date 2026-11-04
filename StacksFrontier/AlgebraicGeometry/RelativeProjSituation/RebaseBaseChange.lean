module

public import Mathlib.RingTheory.IsTensorProduct

/-!
# Re-basing a base change along a pushout of the base rings

Let `R → S` and `R → C` be ring maps with `D = S ⊗_R C`, let `M` be a `C`-module and `N` a
`D`-module, and let `f : M ⟶ N` be `C`-linear. If `f` exhibits `N` as the base change of `M`
along `R → S`, then it exhibits `N` as the base change of `M` along `C → D`:

  `N = S ⊗_R M = (S ⊗_R C) ⊗_C M = D ⊗_C M`.

## Main results

* `Stacks.RelativeProj.isBaseChange_of_isPushout`: the re-basing above.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public section

open TensorProduct

namespace Stacks.RelativeProj

/-- **Re-basing a base change along a pushout of the base rings.** If `D = S ⊗_R C` and the
`C`-linear map `f : M ⟶ N` exhibits `N` as `S ⊗_R M`, then it exhibits `N` as `D ⊗_C M`. -/
public theorem isBaseChange_of_isPushout
    {R S C D M N : Type*} [CommRing R] [CommRing S] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R C] [Algebra R D] [Algebra S D] [Algebra C D]
    [IsScalarTower R S D] [IsScalarTower R C D] [Algebra.IsPushout R S C D]
    [AddCommGroup M] [Module R M] [Module C M] [IsScalarTower R C M]
    [AddCommGroup N] [Module R N] [Module S N] [Module C N] [Module D N]
    [IsScalarTower R S N] [IsScalarTower R C N] [IsScalarTower S D N] [IsScalarTower C D N]
    (f : M →ₗ[C] N) (hf : IsBaseChange S (f.restrictScalars R)) : IsBaseChange D f := by
  let e := Algebra.IsPushout.cancelBaseChange R S C D M
  let l := LinearMap.liftBaseChange D f
  have he (x : S ⊗[R] M) : l (e.symm x) = hf.equiv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      show l ((Algebra.IsPushout.cancelBaseChange R S C D M).symm (s ⊗ₜ[R] m)) = _
      rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, LinearMap.liftBaseChange_tmul,
        IsBaseChange.equiv_tmul, IsScalarTower.algebraMap_smul]
      rfl
  have hl : (l : D ⊗[C] M → N) = hf.equiv ∘ e := funext fun x ↦ by simpa using he (e x)
  exact IsBaseChange.of_equiv
    (LinearEquiv.ofBijective l (hl ▸ hf.equiv.bijective.comp e.bijective))
    (LinearMap.liftBaseChange_one_tmul D f)

end Stacks.RelativeProj

end
