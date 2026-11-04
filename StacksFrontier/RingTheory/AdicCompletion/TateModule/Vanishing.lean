module

public import StacksFrontier.Homology.DerivedComplete.CompletionSequences

/-!
# Vanishing of the `f`-adic Tate module of a bounded torsion module

For an element `f` of a commutative ring `A` and an `A`-module `M`, the `f`-adic Tate module
`CompletionSequences.adicTateModule A M f` is the inverse limit of the tower of torsion
submodules `M[f^{n+1}]`, whose transition maps are multiplication by `f`. An element of that
limit is therefore a sequence `(x_n)` with `f^{n+1} x_n = 0` and `x_n = f x_{n+1}`, and such a
sequence satisfies `x_n = f^k x_{n+k}` for every `k`. Consequently, if a single power `f^k`
annihilates `M`, then every `x_n` vanishes and the Tate module is zero.

## Main results

* `Stacks.TateModule.isZero_adicTateModule_of_pow_smul_eq_zero` — if `f ^ k` annihilates `M`,
  then the `f`-adic Tate module of `M` is a zero object.

## References

* [Stacks Project, Tag 0BKG](https://stacks.math.columbia.edu/tag/0BKG)
* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits PrincipalTorsionTower

universe u v

namespace Stacks.TateModule

variable (A : Type u) [CommRing A] (M : ModuleCat.{v} A) (f : A)

/-- The limit projection at `n` factors the projection at `n + 1` through multiplication by `f`. -/
private lemma limit_π_comp_powerTorsionTransition (n : ℕ) :
    limit.π (powerTorsionSystem A M f) ⟨n + 1⟩ ≫ powerTorsionTransition A M f n
      = limit.π (powerTorsionSystem A M f) ⟨n⟩ := by
  rw [← powerTorsionSystem_map_succ]
  exact limit.w _ _

/-- The `n`-th component of an element of the `f`-adic Tate module is `f` times its
`(n + 1)`-st component, both viewed inside `M`. -/
private lemma kernelι_limit_π_succ (n : ℕ) (x : ↥(limit (powerTorsionSystem A M f))) :
    kernel.ι (powerMultiplication A M (f ^ (n + 1)))
        (limit.π (powerTorsionSystem A M f) ⟨n⟩ x)
      = f • kernel.ι (powerMultiplication A M (f ^ (n + 2)))
        (limit.π (powerTorsionSystem A M f) ⟨n + 1⟩ x) := by
  have h : powerTorsionTransition A M f n
        (limit.π (powerTorsionSystem A M f) ⟨n + 1⟩ x)
      = limit.π (powerTorsionSystem A M f) ⟨n⟩ x :=
    ConcreteCategory.congr_hom (limit_π_comp_powerTorsionTransition A M f n) x
  rw [← h]
  exact ConcreteCategory.congr_hom (powerTorsionTransition_ι A M f n)
    (limit.π (powerTorsionSystem A M f) ⟨n + 1⟩ x)

/-- The `n`-th component of an element of the `f`-adic Tate module is `f ^ k` times its
`(n + k)`-th component, for every `k`. -/
private lemma kernelι_limit_π_add (k n : ℕ) (x : ↥(limit (powerTorsionSystem A M f))) :
    kernel.ι (powerMultiplication A M (f ^ (n + 1)))
        (limit.π (powerTorsionSystem A M f) ⟨n⟩ x)
      = f ^ k • kernel.ι (powerMultiplication A M (f ^ (n + k + 1)))
        (limit.π (powerTorsionSystem A M f) ⟨n + k⟩ x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [ih, kernelι_limit_π_succ A M f (n + k) x, smul_smul, ← pow_succ]
      rfl

/-- **The `f`-adic Tate module of a bounded `f`-power torsion module vanishes.** If `f ^ k`
annihilates `M`, then `lim_n M[f^{n+1}]`, the inverse limit along multiplication by `f`, is a zero
object. -/
theorem isZero_adicTateModule_of_pow_smul_eq_zero (k : ℕ) (hM : ∀ x : M, f ^ k • x = 0) :
    IsZero (CompletionSequences.adicTateModule A M f) := by
  refine (IsZero.iff_id_eq_zero _).mpr (limit.hom_ext fun ⟨n⟩ ↦ ?_)
  have hmono : Mono (kernel.ι (powerMultiplication A M (f ^ (n + 1)))) := inferInstance
  have hz : limit.π (powerTorsionSystem A M f) ⟨n⟩ ≫
      kernel.ι (powerMultiplication A M (f ^ (n + 1))) = 0 := by
    ext x
    exact (kernelι_limit_π_add A M f k n x).trans (hM _)
  rw [Category.id_comp, Limits.zero_comp]
  exact @zero_of_comp_mono _ _ _ _ _ _ _ _ hmono hz

end Stacks.TateModule

end
