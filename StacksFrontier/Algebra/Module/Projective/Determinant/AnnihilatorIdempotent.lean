module

public import StacksFrontier.Algebra.Module.Projective.Determinant.Graded

/-!
# The rank idempotent is the identity on the degree-`n` annihilator

Let `M` be a finite projective module over a commutative ring `R`. The idempotent
`ProjectiveDeterminant.rankIdempotent R M n` cutting out the rank-`n` stratum of `Spec R` acts as
the identity on the elements of `⋀ⁿ_R M` annihilated by every degree-one element of the exterior
algebra, and it annihilates every exterior power of degree greater than `n`
(`ProjectiveDeterminant.rankIdempotent_smul_eq_zero_of_mem_exteriorPower`).

Those two facts are the two halves of the retract condition of [Stacks, Tag 0FJN]: the second
says that multiplication by the idempotent carries a degree-`n` local section of the exterior
algebra into the degreewise exterior annihilator, and the first says that it is the identity on
that annihilator.

## Main results

* `ProjectiveDeterminant.rankIdempotent_smul_eq_self_of_mem_annihilatorPart`: **the rank-`n`
  idempotent is the identity on the degree-`n` annihilator of the degree-one elements.**

## Implementation notes

The annihilator is written as the comap along the inclusion of `⋀ⁿ_R M`, which is the spelling
`Stacks.ExteriorAnnihilator.part` is defined at, so the statement applies to that submodule with
no transport. `ProjectiveDeterminant.map_annihilatorPart_eq_component` identifies its image in
the exterior algebra with the rank-stratum summand of the determinant line, on which
`ProjectiveDeterminant.rankIdempotent_smul_eq_self_of_mem_component` is the conclusion.

## References

* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 0FJA](https://stacks.math.columbia.edu/tag/0FJA)
-/

@[expose] public section

universe u v

namespace ProjectiveDeterminant

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **The rank-`n` idempotent is the identity on the elements of `⋀ⁿ_R M` annihilated by every
degree-one element of the exterior algebra.** Such an element lies in the rank-`n` summand of the
determinant line by the degreewise form of Tag 0FJA, and the idempotent is the identity on that
summand. -/
theorem rankIdempotent_smul_eq_self_of_mem_annihilatorPart [Module.Finite R M]
    [Module.Projective R M] {n : ℕ} {y : ⋀[R]^n M}
    (hy : y ∈ (⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))).comap
      (⋀[R]^n M).subtype) :
    rankIdempotent (R := R) (M := M) n • (y : ExteriorAlgebra R M) =
      (y : ExteriorAlgebra R M) :=
  rankIdempotent_smul_eq_self_of_mem_component
    ((map_annihilatorPart_eq_component (R := R) (M := M) n) ▸ Submodule.mem_map_of_mem hy)

end ProjectiveDeterminant

end
