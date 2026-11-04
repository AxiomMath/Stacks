module

public import StacksFrontier.AlgebraicGeometry.Divisors.IntegralDivisorMultiplicity
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismDivisorLength

/-!
# The exponent of the twist is bounded by the colength of the stalk map

A nonzero morphism `σ : L ⟶ L'` of invertible modules on an integral locally Noetherian scheme
which is a stalkwise epimorphism away from an integral effective Cartier divisor `D` writes
`L'` as the twist of `L` by `D ^ k`. This file bounds `k`: it is the multiplicity of the divisor
of `σ` at the prime divisor carried by `D`, hence at most the length of the cokernel of the
stalk map of `σ` at the generic point of that prime divisor.

That is the last structural step of the second assertion of [Stacks, Tag 0B3T]: with `σ` the
determinant comparison map, the colength of the stalk map is bounded by `min s r`, so the twist
is by at most `min(s, r)` copies of `D`.

## Main results

* `AlgebraicGeometry.exists_pow_le_tensorIso_of_surjective_stalk_off`: **the bounded twist.**

## Implementation notes

The prime divisor is a hypothesis rather than constructed from `D`: the library has no
construction of a `AlgebraicGeometry.PrimeDivisor` out of an integral effective Cartier divisor,
and every consumer of `AlgebraicGeometry.effectiveCartierMultiplicity_pow` takes one the same
way.

The length hypothesis is stated as `≤ (n : ℕ∞)` rather than as an inequality between two
`Module.length`s followed by `ENat.toNat`, because `ENat.toNat` is monotone only below `⊤` and
`Module.length` of the cokernel is not known to be finite before the bound is in hand.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0BCP](https://stacks.math.columbia.edu/tag/0BCP)
* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (L L' : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']

/-- **A nonzero morphism of invertible modules which is a stalkwise epimorphism away from an
integral effective Cartier divisor `D` twists by `D ^ k` with `k` at most the colength of its
stalk map at the generic point of `D`.** -/
theorem exists_pow_le_tensorIso_of_surjective_stalk_off
    (D : X.IdealSheafData) (hDint : IsIntegral D.subscheme)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (Z : PrimeDivisor X) (hZ : Z.genericPoint ∈ ((D.support : Closeds X) : Set X))
    {σ : L ⟶ L'} (hσ : σ ≠ 0) (n : ℕ)
    (hlen : Module.length (X.presheaf.stalk Z.genericPoint)
        (L'.presheaf.stalk Z.genericPoint ⧸
          LinearMap.range (Stacks.ModuleStalk.map σ Z.genericPoint)) ≤ (n : ℕ∞))
    (hoff : ∀ x : X, x ∉ D.supportSet →
      Function.Surjective (Stacks.ModuleStalk.mapFun σ x)) :
    ∃ k : ℕ, k ≤ n ∧ Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).obj ((Stacks.Divisors.invertibleSheaf' (D ^ k)))).obj (L)) ≅
      L') := by
  obtain ⟨k, hk⟩ := exists_pow_eq_of_supportSet_subset (morphismZeroScheme L L' σ) D
    (isEffectiveCartierDivisor_morphismZeroScheme L L' hσ) hDint hD
    (supportSet_morphismZeroScheme_subset_of_surjective_stalk_off L L' hσ D.supportSet hoff)
  refine ⟨k, ?_, hk ▸ nonempty_tensorIso_morphismZeroScheme L L' hσ⟩
  have hmul : effectiveCartierMultiplicity (morphismZeroScheme L L' σ) Z = (k : ℤ) := by
    rw [hk]
    exact effectiveCartierMultiplicity_pow hD Z hZ k
  rw [effectiveCartierMultiplicity, Nat.cast_inj] at hmul
  rw [← hmul]
  refine ENat.toNat_le_of_le_coe ?_
  exact (length_quotient_stalk_morphismZeroScheme_le σ Z.genericPoint).trans hlen

end AlgebraicGeometry

end
