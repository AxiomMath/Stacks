module

public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Decomposition

/-!
# A morphism of invertible modules supported on one divisor is a twist by a power of it

`AlgebraicGeometry.morphismZeroScheme` is the effective Cartier divisor cut out by a nonzero
morphism `σ : L ⟶ L'` of invertible modules on an integral scheme, and `𝒪_X(Z(σ)) ⊗ L ≅ L'`.
When that divisor is supported on an *integral* effective Cartier divisor `D`, the decomposition
of [Stacks, Tag 0BCP] for the one-member covering family `{D}` makes it `D ^ k`, so the twist is
by a power of `D`. This is the form the determinant comparison of [Stacks, Tag 0B3T] needs: the
tag's conclusion is a twist by `D ^ k` with `k ≤ min s r`, and this supplies everything but the
bound on `k`.

## Main results

* `AlgebraicGeometry.exists_pow_tensorIso_of_ne_zero_of_supportSet_subset`: **the twist is by a
  power of `D`**, for a general morphism of invertible modules.
* `AlgebraicGeometry.exists_pow_tensorIso_detMap_of_supportSet_subset`: the same for the
  determinant comparison map `σ(f, r)` of [Stacks, Tag 0B3T].

## Implementation notes

**No `@[stacks]` attribute.** Two hypotheses of Tag 0B3T's second assertion are taken as given
here rather than proved: that the comparison map is nonzero, and that its divisor is supported
on the given one. The bound `k ≤ min(s, r)` is not proved at all. What is stated is therefore a
step of the proof, not the assertion.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0BCP](https://stacks.math.columbia.edu/tag/0BCP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules Scheme.Modules
open Stacks.AlgebraicGeometry.ReflexiveModules (reflexiveHull)

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] (L L' : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']

/-- **A nonzero morphism of invertible modules whose divisor is supported on an integral
effective Cartier divisor `D` exhibits the target as the twist of the source by `D ^ k`.** The
divisor of the morphism is effective Cartier, so Tag 0BCP for the covering family `{D}` writes
it as `D ^ k`. -/
theorem exists_pow_tensorIso_of_ne_zero_of_supportSet_subset
    (D : X.IdealSheafData) (hDint : IsIntegral D.subscheme)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) {σ : L ⟶ L'} (hσ : σ ≠ 0)
    (hsub : (morphismZeroScheme L L' σ).supportSet ⊆ D.supportSet) :
    ∃ k : ℕ, Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).obj ((Stacks.Divisors.invertibleSheaf' (D ^ k)))).obj (L)) ≅
      L') := by
  obtain ⟨k, hk⟩ := exists_pow_eq_of_supportSet_subset (morphismZeroScheme L L' σ) D
    (isEffectiveCartierDivisor_morphismZeroScheme L L' hσ) hDint hD hsub
  exact ⟨k, hk ▸ nonempty_tensorIso_morphismZeroScheme L L' hσ⟩

/-- **The determinant comparison map of [Stacks, Tag 0B3T] with its divisor supported on an
integral effective Cartier divisor `D` twists by `D ^ k`.** -/
theorem exists_pow_tensorIso_detMap_of_supportSet_subset {F F' : X.Modules} (r : ℤ) (f : F ⟶ F')
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (reflexiveHull (exteriorPower F r))]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (reflexiveHull (exteriorPower F' r))]
    (D : X.IdealSheafData) (hDint : IsIntegral D.subscheme)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (hf : detMap f r ≠ 0)
    (hsub : (morphismZeroScheme (reflexiveHull (exteriorPower F r))
      (reflexiveHull (exteriorPower F' r)) (detMap f r)).supportSet ⊆ D.supportSet) :
    ∃ k : ℕ, Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).obj ((Stacks.Divisors.invertibleSheaf' (D ^ k)))).obj
          ((reflexiveHull (exteriorPower F r)))) ≅
        reflexiveHull (exteriorPower F' r)) :=
  exists_pow_tensorIso_of_ne_zero_of_supportSet_subset _ _ D hDint hD hf hsub

end AlgebraicGeometry

end
