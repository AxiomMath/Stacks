module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# The function field is not finite over the local ring at a non-generic point

Let `X` be an integral scheme and `y` a point of `X` other than the generic point. The function
field of `X` is then not a finite module over the local ring `𝒪_{X, y}`, and the Krull dimension
of that local ring is at least one.

This is the arithmetic at the end of the first paragraph of [Stacks, Tag 0AWC]. There, `X` is the
closure of an associated point `x` of a coherent module, localized at a point `z` of the
complement of the open subscheme, and the paragraph closes with the words "`j_*𝒪_{X' ∩ U}`
corresponds to `κ(x)` as an `𝒪_{X, z}`-module which cannot be finite as `x` is not a closed
point". The field `κ(x)` is the function field of `X'` and `𝒪_{X, z}` acts through the surjection
onto `𝒪_{X', z}`, so the failure of finiteness is exactly `not_module_finite_functionField`
below.

## Main results

* `AlgebraicGeometry.lt_genericPoint`: a point other than the generic point of an irreducible
  scheme is a strict specialization of it.
* `AlgebraicGeometry.one_le_ringKrullDim_stalk`: the local ring at such a point has Krull
  dimension at least one.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_one`: if it has dimension at most one, it has
  dimension exactly one.
* `AlgebraicGeometry.not_module_finite_functionField`: the function field of an integral scheme
  is not a finite module over the local ring at a non-generic point.
* `AlgebraicGeometry.eq_genericPoint_of_module_finite_functionField`: the contrapositive.

## Implementation notes

`not_module_finite_functionField` is a statement about the local ring and the function field only,
with no quasi-coherence or coherence in it. That is deliberate: the geometric reductions of
[Stacks, Tag 0AWC] all end by identifying some module of sections with the function field, and
each of them can consume this lemma without carrying any sheaf-theoretic hypothesis into the
algebra.

The proof is the standard one: a domain whose fraction field is a finite module over it is a
field, because the fraction field is then integral over it; and the local ring at a non-generic
point is not a field, because the generic point gives a strict specialization and hence a chain
of length one in the local ring's spectrum. Mathlib supplies the fraction field relation as the
instance on an integral scheme, so no localization has to be constructed here.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A domain whose fraction field is a finite module over it is a field: the fraction field is
then integral over the domain, and an integral extension of a domain is a field only if the
domain is. -/
private theorem isField_of_finite_fractionRing (A K : Type u) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Module.Finite A K] : IsField A :=
  have : Algebra.IsIntegral A K := Algebra.IsIntegral.of_finite A K
  (Algebra.IsIntegral.isField_iff_isField
    (IsFractionRing.injective A K)).mpr (Field.toIsField K)

/-- A point of an irreducible scheme other than the generic point is a *strict* specialization of
the generic point. The order on the points of a scheme is specialization, and a scheme is `T0`, so
the two specializations between `y` and the generic point would make them equal. -/
theorem lt_genericPoint {X : Scheme.{u}} [IrreducibleSpace X] {y : X}
    (hy : y ≠ genericPoint X) : y < genericPoint X :=
  ⟨genericPoint_specializes y, fun h =>
    hy (inseparable_iff_specializes_and.mpr ⟨h, genericPoint_specializes y⟩).eq⟩

/-- **The local ring at a non-generic point of an irreducible scheme has dimension at least
one.** The generic point is a strict specialization of `y`, so the coheight of `y` is at least
one, and that coheight is the Krull dimension of the local ring by [Stacks, Tag 02IZ]. -/
theorem one_le_ringKrullDim_stalk {X : Scheme.{u}} [IrreducibleSpace X] {y : X}
    (hy : y ≠ genericPoint X) : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk y) := by
  have hco : (1 : ℕ∞) ≤ Order.coheight y :=
    le_trans (by simp) (Order.coheight_add_one_le (lt_genericPoint hy))
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
  exact_mod_cast hco

/-- **A non-generic point whose local ring has dimension at most one has dimension exactly
one.** This is the form in which the codimension hypothesis of [Stacks, Tag 0AWC] is used: the
hypothesis there is an inequality, while the completion argument needs an equality. -/
theorem ringKrullDim_stalk_eq_one {X : Scheme.{u}} [IrreducibleSpace X] {y : X}
    (hy : y ≠ genericPoint X) (h : ringKrullDim (X.presheaf.stalk y) ≤ 1) :
    ringKrullDim (X.presheaf.stalk y) = 1 :=
  le_antisymm h (one_le_ringKrullDim_stalk hy)

/-- **[Stacks, Tag 0AWC].** On an integral scheme the function field is not a finite module over
the local ring at a point other than the generic point.

This is the closing step of the first paragraph of the cited remark, where the module of sections
of the direct image is identified with the function field of the closure of an associated point
and has to fail to be finite. -/
theorem not_module_finite_functionField {X : Scheme.{u}} [IsIntegral X] {y : X}
    (hy : y ≠ genericPoint X) :
    ¬ Module.Finite (X.presheaf.stalk y) X.functionField := by
  intro h
  have hfield : IsField ↥(X.presheaf.stalk y) :=
    isField_of_finite_fractionRing ↥(X.presheaf.stalk y) ↥X.functionField
  have h1 := one_le_ringKrullDim_stalk (X := X) hy
  rw [ringKrullDim_eq_zero_of_isField hfield] at h1
  exact absurd h1 (by norm_num)

/-- The contrapositive of `AlgebraicGeometry.not_module_finite_functionField`: a point of an
integral scheme whose local ring has the function field as a finite module is the generic
point. -/
theorem eq_genericPoint_of_module_finite_functionField {X : Scheme.{u}} [IsIntegral X] {y : X}
    (h : Module.Finite (X.presheaf.stalk y) X.functionField) : y = genericPoint X := by
  by_contra hy
  exact not_module_finite_functionField hy h

end AlgebraicGeometry

end
