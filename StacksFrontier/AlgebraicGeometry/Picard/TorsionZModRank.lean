module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import StacksFrontier.AlgebraicGeometry.Picard.PurelyInseparablePullback

/-!
# The `F_ℓ`-dimension of the `ℓ`-torsion of an abelian group

For an abelian group `A` and a prime `ℓ`, the `ℓ`-torsion subgroup `A[ℓ]` is a vector space over
`ZMod ℓ = F_ℓ`, and the invariant `dim_{F_ℓ} A[ℓ]` is what the Picard-torsion bounds of the
source are stated in terms of.  This file provides the transport of that invariant along a
homomorphism of abelian groups: a homomorphism restricts to an `F_ℓ`-linear map of `ℓ`-torsion,
injectivity on the `ℓ`-torsion makes the dimension go up, and a bijection on the `ℓ`-torsion
makes it equal.

## Main definitions

* `Stacks.Picard.zmodTorsionRestrict` — the restriction `A[n] →ₗ[ZMod n] B[n]` of a homomorphism
  of abelian groups to `n`-torsion, as a `ZMod n`-linear map.

## Main results

* `Stacks.Picard.injective_zmodTorsionRestrict`, `Stacks.Picard.surjective_zmodTorsionRestrict`
  and `Stacks.Picard.bijective_zmodTorsionRestrict` — the restriction is injective, surjective or
  bijective as soon as the homomorphism is so on the `n`-torsion *sets*.
* `Stacks.Picard.finiteDimensional_zmodTorsion_of_injOn` — finite-dimensionality of the
  `ℓ`-torsion descends along a map injective on `ℓ`-torsion.
* `Stacks.Picard.finrank_zmodTorsion_le_of_injOn` — `dim_{F_ℓ} A[ℓ] ≤ dim_{F_ℓ} B[ℓ]` for a map
  injective on `ℓ`-torsion with `B[ℓ]` finite-dimensional.
* `Stacks.Picard.finrank_zmodTorsion_eq_of_bijOn` — `dim_{F_ℓ} A[ℓ] = dim_{F_ℓ} B[ℓ]` for a map
  bijective on `ℓ`-torsion, with no finiteness hypothesis.

## Implementation notes

The `ℓ`-torsion is `AddSubgroup.torsionBy A (ℓ : ℤ)` and its `ZMod ℓ`-module structure is
Mathlib's `AddSubgroup.torsionBy.zmodModule`, made a local instance throughout this file.  That
subgroup has the same carrier as `Stacks.Picard.zsmulTorsion A ℓ`, the *set* of elements killed
by `ℓ` in which this development's Picard-torsion statements are phrased
(`Stacks.Picard.mem_zsmulTorsion_of_mem_torsionBy` and its converse translate between them), so
the hypotheses here are stated as `Set.InjOn`, `Set.SurjOn` and `Set.BijOn` on those sets and
apply directly to the existing results.

`Stacks.Picard.zsmulTorsionRestrict` is the `ℤ`-linear restriction of a homomorphism to
`Submodule.torsionBy ℤ A n`.  The map here is the same on elements but carries the `ZMod n`
scalars, which is what a dimension over `F_ℓ` is taken with respect to; neither is definable
from the other without changing the scalar ring.

The finiteness hypotheses cannot be dropped from the two inequality statements: `Module.finrank`
is `0` on an infinite-dimensional space, so an injection into an infinite-dimensional space says
nothing about dimensions.  `Stacks.Picard.finrank_zmodTorsion_eq_of_bijOn` needs no such
hypothesis, a linear equivalence giving equal dimensions in all cases.
-/

@[expose] public section

namespace Stacks.Picard

attribute [local instance] AddSubgroup.torsionBy.zmodModule

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-! ### The `n`-torsion subgroup and the `n`-torsion set -/

/-- An element of the `n`-torsion subgroup is killed by `n`. -/
theorem mem_zsmulTorsion_of_mem_torsionBy {n : ℤ} {x : A} (hx : x ∈ AddSubgroup.torsionBy A n) :
    x ∈ zsmulTorsion A n :=
  (Submodule.mem_torsionBy_iff n x).mp hx

/-- An element killed by `n` lies in the `n`-torsion subgroup. -/
theorem mem_torsionBy_of_mem_zsmulTorsion {n : ℤ} {x : A} (hx : x ∈ zsmulTorsion A n) :
    x ∈ AddSubgroup.torsionBy A n :=
  (Submodule.mem_torsionBy_iff n x).mpr hx

/-! ### Restriction of a homomorphism to `n`-torsion -/

/-- **The restriction of a homomorphism of abelian groups to `n`-torsion, as a `ZMod n`-linear
map.** A homomorphism carries elements killed by `n` to elements killed by `n`, and a
homomorphism of abelian groups whose source and target are killed by `n` is automatically
`ZMod n`-linear. -/
def zmodTorsionRestrict (f : A →+ B) (n : ℕ) :
    AddSubgroup.torsionBy A (n : ℤ) →ₗ[ZMod n] AddSubgroup.torsionBy B (n : ℤ) :=
  AddMonoidHom.toZModLinearMap n
    { toFun := fun x => ⟨f (x : A), AddSubgroup.torsionBy.nsmul_iff.mpr (by
        rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp x.2, map_zero])⟩
      map_zero' := Subtype.ext (map_zero f)
      map_add' := fun x y => Subtype.ext (map_add f (x : A) (y : A)) }

/-- The restriction of `f` to `n`-torsion sends `x` to `f x`. -/
@[simp]
theorem zmodTorsionRestrict_coe (f : A →+ B) (n : ℕ) (x : AddSubgroup.torsionBy A (n : ℤ)) :
    (zmodTorsionRestrict f n x : B) = f (x : A) := rfl

/-- A homomorphism injective on the `n`-torsion restricts to an injective map of `n`-torsion. -/
theorem injective_zmodTorsionRestrict (f : A →+ B) (n : ℕ)
    (hf : Set.InjOn f (zsmulTorsion A (n : ℤ))) :
    Function.Injective (zmodTorsionRestrict f n) := fun x y hxy =>
  Subtype.ext (hf (mem_zsmulTorsion_of_mem_torsionBy x.2)
    (mem_zsmulTorsion_of_mem_torsionBy y.2) (congrArg Subtype.val hxy))

/-- A homomorphism carrying the `n`-torsion onto the `n`-torsion restricts to a surjective map of
`n`-torsion. -/
theorem surjective_zmodTorsionRestrict (f : A →+ B) (n : ℕ)
    (hf : Set.SurjOn f (zsmulTorsion A (n : ℤ)) (zsmulTorsion B (n : ℤ))) :
    Function.Surjective (zmodTorsionRestrict f n) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := hf (mem_zsmulTorsion_of_mem_torsionBy y.2)
  exact ⟨⟨x, mem_torsionBy_of_mem_zsmulTorsion hx⟩, Subtype.ext hxy⟩

/-- A homomorphism bijective from the `n`-torsion onto the `n`-torsion restricts to a bijective
map of `n`-torsion. -/
theorem bijective_zmodTorsionRestrict (f : A →+ B) (n : ℕ)
    (hf : Set.BijOn f (zsmulTorsion A (n : ℤ)) (zsmulTorsion B (n : ℤ))) :
    Function.Bijective (zmodTorsionRestrict f n) :=
  ⟨injective_zmodTorsionRestrict f n hf.injOn, surjective_zmodTorsionRestrict f n hf.surjOn⟩

/-! ### Dimension over `F_ℓ` -/

variable (p : ℕ) [Fact p.Prime]

/-- **Finite-dimensionality of the `ℓ`-torsion descends along a map injective on `ℓ`-torsion.** -/
theorem finiteDimensional_zmodTorsion_of_injOn (f : A →+ B)
    (hf : Set.InjOn f (zsmulTorsion A (p : ℤ)))
    (hB : FiniteDimensional (ZMod p) (AddSubgroup.torsionBy B (p : ℤ))) :
    FiniteDimensional (ZMod p) (AddSubgroup.torsionBy A (p : ℤ)) := by
  have := hB
  exact FiniteDimensional.of_injective (zmodTorsionRestrict f p)
    (injective_zmodTorsionRestrict f p hf)

/-- **`dim_{F_ℓ} A[ℓ] ≤ dim_{F_ℓ} B[ℓ]` for a homomorphism injective on `ℓ`-torsion**, the
`ℓ`-torsion of the target being finite-dimensional. -/
theorem finrank_zmodTorsion_le_of_injOn (f : A →+ B)
    (hf : Set.InjOn f (zsmulTorsion A (p : ℤ)))
    (hB : FiniteDimensional (ZMod p) (AddSubgroup.torsionBy B (p : ℤ))) :
    Module.finrank (ZMod p) (AddSubgroup.torsionBy A (p : ℤ)) ≤
      Module.finrank (ZMod p) (AddSubgroup.torsionBy B (p : ℤ)) := by
  have := hB
  exact LinearMap.finrank_le_finrank_of_injective (injective_zmodTorsionRestrict f p hf)

/-- **`dim_{F_ℓ} A[ℓ] = dim_{F_ℓ} B[ℓ]` for a homomorphism bijective on `ℓ`-torsion.** No
finiteness hypothesis is needed. -/
theorem finrank_zmodTorsion_eq_of_bijOn (f : A →+ B)
    (hf : Set.BijOn f (zsmulTorsion A (p : ℤ)) (zsmulTorsion B (p : ℤ))) :
    Module.finrank (ZMod p) (AddSubgroup.torsionBy A (p : ℤ)) =
      Module.finrank (ZMod p) (AddSubgroup.torsionBy B (p : ℤ)) :=
  (LinearEquiv.ofBijective (zmodTorsionRestrict f p)
    (bijective_zmodTorsionRestrict f p hf)).finrank_eq

/-- **Finite-dimensionality of the `ℓ`-torsion transfers along a map bijective on
`ℓ`-torsion.** -/
theorem finiteDimensional_zmodTorsion_of_bijOn (f : A →+ B)
    (hf : Set.BijOn f (zsmulTorsion A (p : ℤ)) (zsmulTorsion B (p : ℤ)))
    (hB : FiniteDimensional (ZMod p) (AddSubgroup.torsionBy B (p : ℤ))) :
    FiniteDimensional (ZMod p) (AddSubgroup.torsionBy A (p : ℤ)) :=
  finiteDimensional_zmodTorsion_of_injOn p f hf.injOn hB

end Stacks.Picard

end
