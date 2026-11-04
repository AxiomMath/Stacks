module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneWeilClassMultiplicative
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.NormalWeilDivisorInvertible

/-!
# Rank one coherent reflexive modules are the Weil divisor class group

Let `X` be an integral locally Noetherian normal scheme.  The map
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass` of [Stacks, Tag 0EBM], from
isomorphism classes of rank one coherent reflexive `𝒪_X`-modules to `Cl(X)`, is **surjective**.

Together with the injectivity of
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_injective` and the
multiplicativity of `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_mul` and
`rankOneSkeletonToWeilClass_one`, this makes the map an isomorphism of commutative monoids onto
`Cl(X)` written multiplicatively, which is the assertion of [Stacks, Tag 0EBM].

## Main results

* `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_surjective` — **the
  surjectivity clause of [Stacks, Tag 0EBM]**.
* `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_bijective` — the map is a
  bijection.
* `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonMulEquivWeilDivisorClass` — **[Stacks, Tag
  0EBM]**: the isomorphism itself.
* `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonCommGroup` — **the group clause of
  [Stacks, Tag 0EBL]**: the monoid law `ℱ, 𝒢 ↦ (ℱ ⊗_{𝒪_X} 𝒢)^∨∨` is an *abelian group* law.

## Implementation notes

The target `Multiplicative (Cl X)` is a group, so the isomorphism exhibits the commutative monoid
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonCommMonoid` of [Stacks, Tag 0EBL] as a group
`rankOneSkeletonCommGroup`. Its multiplication is that of `rankOneSkeletonCommMonoid` on the
nose, so by `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonMul_toSkeleton` the group law is
the rule the tag states.

## References

* [Stacks Project, Tag 0EBM](https://stacks.math.columbia.edu/tag/0EBM)
* [Stacks Project, Tag 0EBL](https://stacks.math.columbia.edu/tag/0EBL)
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry.CoherentReflexive

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The surjectivity clause of [Stacks, Tag 0EBM].**  Every Weil divisor class is the class of
a rank one coherent reflexive `𝒪_X`-module. -/
theorem rankOneSkeletonToWeilClass_surjective :
    Function.Surjective (rankOneSkeletonToWeilClass (X := X)) :=
  rankOneSkeletonToWeilClass_surjective_iff.mpr exists_weilClassOfCodimTwoInvertible_eq

/-- The map of [Stacks, Tag 0EBM] is a bijection. -/
theorem rankOneSkeletonToWeilClass_bijective :
    Function.Bijective (rankOneSkeletonToWeilClass (X := X)) :=
  ⟨rankOneSkeletonToWeilClass_injective, rankOneSkeletonToWeilClass_surjective⟩

attribute [local instance] rankOneSkeletonCommMonoid

/-- On an integral locally Noetherian normal scheme the isomorphism classes of rank one coherent
reflexive `𝒪_X`-modules, under the monoid law `ℱ, 𝒢 ↦ (ℱ ⊗_{𝒪_X} 𝒢)^∨∨` of [Stacks, Tag 0EBL],
are isomorphic to the Weil divisor class group `Cl(X)`, written multiplicatively.

The isomorphism is `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass`, which sends
a module to the class of its restriction to an open subscheme whose complement has codimension at
least two and on which it is invertible. -/
@[stacks 0EBM]
def rankOneSkeletonMulEquivWeilDivisorClass :
    Skeleton (RankOneReflexiveModules X) ≃* Multiplicative (weilDivisorClassGroup X) where
  toFun c := Multiplicative.ofAdd (rankOneSkeletonToWeilClass c)
  invFun d := (Equiv.ofBijective _ rankOneSkeletonToWeilClass_bijective).symm
    (Multiplicative.toAdd d)
  left_inv c := (Equiv.ofBijective _ rankOneSkeletonToWeilClass_bijective).symm_apply_apply c
  right_inv d := congrArg Multiplicative.ofAdd
    ((Equiv.ofBijective _ rankOneSkeletonToWeilClass_bijective).apply_symm_apply
      (Multiplicative.toAdd d))
  map_mul' a b := congrArg Multiplicative.ofAdd (rankOneSkeletonToWeilClass_mul a b)

/-- The isomorphism `rankOneSkeletonMulEquivWeilDivisorClass` sends the class of a rank one
reflexive module to its Weil divisor class `rankOneSkeletonToWeilClass c`, viewed
multiplicatively. -/
@[simp]
theorem rankOneSkeletonMulEquivWeilDivisorClass_apply (c : Skeleton (RankOneReflexiveModules X)) :
    rankOneSkeletonMulEquivWeilDivisorClass c =
      Multiplicative.ofAdd (rankOneSkeletonToWeilClass c) :=
  rfl

/-- On an integral locally Noetherian normal scheme the rule `ℱ, 𝒢 ↦ (ℱ ⊗_{𝒪_X} 𝒢)^∨∨` is an
**abelian group law** on the set of isomorphism classes of rank one coherent reflexive
`𝒪_X`-modules.

Multiplication and unit are those of
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonCommMonoid`, and the inverse of `[ℱ]` is the
class whose Weil divisor class is `-[ℱ]`. -/
@[instance_reducible,
  stacks 0EBL "the abelian group law on isomorphism classes of rank 1 coherent reflexive modules"]
noncomputable def rankOneSkeletonCommGroup (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] :
    CommGroup (Skeleton (RankOneReflexiveModules X)) where
  __ := rankOneSkeletonCommMonoid X
  inv c := (Equiv.ofBijective _ rankOneSkeletonToWeilClass_bijective).symm
    (-rankOneSkeletonToWeilClass c)
  inv_mul_cancel c := rankOneSkeletonToWeilClass_injective <| by
    rw [rankOneSkeletonToWeilClass_mul, rankOneSkeletonToWeilClass_one]
    exact add_eq_zero_iff_eq_neg.2
      ((Equiv.ofBijective _ rankOneSkeletonToWeilClass_bijective).apply_symm_apply _)

/-- The multiplication and the unit of `rankOneSkeletonCommGroup` are those of
`rankOneSkeletonCommMonoid`. -/
theorem rankOneSkeletonCommGroup_toCommMonoid (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] :
    (rankOneSkeletonCommGroup X).toCommMonoid = rankOneSkeletonCommMonoid X :=
  rfl

end AlgebraicGeometry.CoherentReflexive

end
