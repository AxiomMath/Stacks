module

public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic

/-!
# The Euler characteristic of a sheaf with cohomology only in degrees zero and one

On a curve the cohomology of a coherent sheaf vanishes above degree one, so its Euler
characteristic is `h⁰ - h¹` and in particular is at most `h⁰`. Here both statements are proved
for a sheaf whose cohomology vanishes from degree two on, together with the corresponding formula
for the degree of an invertible sheaf.

## Main results

* `AlgebraicGeometry.finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero`: the
  alternating sum of the dimensions of the cohomology of a sheaf whose cohomology vanishes above
  degree one is `h⁰ - h¹`.
* `AlgebraicGeometry.eulerCharacteristic_eq_sub_of_isZero`: the same statement for
  `AlgebraicGeometry.eulerCharacteristic`.
* `AlgebraicGeometry.eulerCharacteristic_le_finrank_cohomologyOverField_zero`:
  `χ(X, ℱ) ≤ dim_k H⁰(X, ℱ)`.
* `AlgebraicGeometry.invertibleCurveDegree_eq_sub_of_isZero`: the degree of an invertible sheaf
  as `(h⁰(𝓛) - h¹(𝓛)) - (h⁰(𝒪_X) - h¹(𝒪_X))`.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The alternating sum of the dimensions of cohomology vanishing above degree one.** If
`Hᵐ(X, ℱ) = 0` for every `m ≥ 2` then `∑ₘ (-1)ᵐ dim Hᵐ(X, ℱ) = dim H⁰(X, ℱ) - dim H¹(X, ℱ)`. -/
theorem finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero (F : X.Modules)
    (hvan : ∀ m, 2 ≤ m → IsZero (cohomologyOverField k f F m)) :
    (∑ᶠ m : ℕ, (-1 : ℤ) ^ m * (Module.finrank k (cohomologyOverField k f F m) : ℤ)) =
      (Module.finrank k (cohomologyOverField k f F 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f F 1) : ℤ) := by
  have hz : ∀ m, 2 ≤ m → Module.finrank k (cohomologyOverField k f F m) = 0 := fun m hm =>
    have := ModuleCat.subsingleton_of_isZero (hvan m hm)
    Module.finrank_zero_of_subsingleton
  rw [finsum_eq_sum_of_support_subset
    (f := fun m : ℕ => (-1 : ℤ) ^ m * (Module.finrank k (cohomologyOverField k f F m) : ℤ))
    (s := Finset.range 2) fun m hm => ?_]
  · rw [Finset.sum_range_succ, Finset.sum_range_one]
    ring
  · by_contra hn
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn
    simp [hz m hn] at hm

/-- **The Euler characteristic of a sheaf with cohomology only in degrees zero and one.** -/
theorem eulerCharacteristic_eq_sub_of_isZero [IsProper f] (F : X.Modules) [F.IsCoherent]
    (hvan : ∀ m, 2 ≤ m → IsZero (cohomologyOverField k f F m)) :
    eulerCharacteristic k f F =
      (Module.finrank k (cohomologyOverField k f F 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f F 1) : ℤ) :=
  finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f F hvan

/-- **The Euler characteristic is at most the dimension of `H⁰`** when the cohomology vanishes
above degree one. -/
theorem eulerCharacteristic_le_finrank_cohomologyOverField_zero [IsProper f] (F : X.Modules)
    [F.IsCoherent] (hvan : ∀ m, 2 ≤ m → IsZero (cohomologyOverField k f F m)) :
    eulerCharacteristic k f F ≤ (Module.finrank k (cohomologyOverField k f F 0) : ℤ) := by
  rw [eulerCharacteristic_eq_sub_of_isZero k f F hvan]
  simp

/-- **The degree of an invertible sheaf on a curve in terms of `h⁰` and `h¹`.** -/
theorem invertibleCurveDegree_eq_sub_of_isZero [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hvanL : ∀ m, 2 ≤ m → IsZero (cohomologyOverField k f L m))
    (hvanO : ∀ m, 2 ≤ m →
      IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m)) :
    invertibleCurveDegree k f hdim L =
      ((Module.finrank k (cohomologyOverField k f L 0) : ℤ) -
          (Module.finrank k (cohomologyOverField k f L 1) : ℤ)) -
        ((Module.finrank k
              (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) : ℤ) -
          (Module.finrank k
            (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) : ℤ)) := by
  rw [invertibleCurveDegree,
    finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f L hvanL,
    finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f _ hvanO]

end AlgebraicGeometry

end
