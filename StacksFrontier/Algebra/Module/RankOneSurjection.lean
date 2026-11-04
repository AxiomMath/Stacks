module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# A surjection from a free module of rank one onto a torsion free module

Let `R` be a domain, `F` a free `R`-module of rank one and `N` a nonzero torsion free
`R`-module. Every surjective `R`-linear map `F → N` is an isomorphism: writing `F = R e`, the
kernel of `φ` is the annihilator of `φ(e)`, and `φ(e) ≠ 0` because `N ≠ 0`.

This is the last step of the proof of [Stacks, Tag 0BBV], applied at the stalks of a normal
surface: there the free module of rank one is the stalk of an invertible module, the target is
the stalk of the dualizing module, which is torsion free by [Stacks, Tag 0AWK], and the map is the
canonical surjection of [Stacks, Tag 0BBU] and [Stacks, Tag 0B64] through the torsion free
quotient.

## Main results

* `LinearMap.bijective_of_surjective_of_finrank_eq_one` — the statement above.

## References

* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
-/

@[expose] public section

namespace LinearMap

variable {R F N : Type*} [CommRing R] [IsDomain R] [AddCommGroup F] [Module R F]
  [Module.Free R F] [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N] [Nontrivial N]

/-- **A surjection from a free module of rank one onto a nonzero torsion free module is
bijective.** -/
theorem bijective_of_surjective_of_finrank_eq_one (hF : Module.finrank R F = 1)
    (φ : F →ₗ[R] N) (hφ : Function.Surjective φ) : Function.Bijective φ := by
  have : Module.Finite R F := Module.finite_of_finrank_eq_succ hF
  let b : Module.Basis (Fin 1) R F := Module.finBasisOfFinrankEq R F hF
  have hspan : ∀ x : F, x = b.repr x 0 • b 0 := fun x => by
    conv_lhs => rw [← b.sum_repr x]
    simp
  have hne : φ (b 0) ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := exists_ne (0 : N)
    obtain ⟨x, rfl⟩ := hφ y
    exact hy (by rw [hspan x, map_smul, h0, smul_zero])
  refine ⟨(injective_iff_map_eq_zero φ).mpr fun x hx => ?_, hφ⟩
  rw [hspan x, map_smul] at hx
  rw [hspan x, (smul_eq_zero_iff_left hne).mp hx, zero_smul]

end LinearMap

end
