module

public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# Injectivity one degree up from vanishing of the quotient's cohomology

For a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on a scheme `X` over a field `k`,
the long exact sequence of cohomology makes the connecting map `Hⁿ(X, ℱ₃) ⟶ Hⁿ⁺¹(X, ℱ₁)` the
exact predecessor of `Hⁿ⁺¹(X, ℱ₁) ⟶ Hⁿ⁺¹(X, ℱ₂)`. So as soon as `Hⁿ(X, ℱ₃)` vanishes, the map
`Hⁿ⁺¹(X, ℱ₁) ⟶ Hⁿ⁺¹(X, ℱ₂)` is injective.

## Main results

* `AlgebraicGeometry.injective_cohomologyOverFieldMap_succ_of_isZero`: the injectivity.

## Implementation notes

The long exact sequence is `AlgebraicGeometry.exists_cohomologyOverField_longExactSequence`,
which quantifies the connecting maps existentially; only the last of its four exactness clauses
is used, and the vanishing hypothesis is used only to see that the connecting map out of
`Hⁿ(X, ℱ₃)` has trivial image.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Vanishing of `Hⁿ(X, ℱ₃)` makes `Hⁿ⁺¹(X, ℱ₁) ⟶ Hⁿ⁺¹(X, ℱ₂)` injective.** The connecting
map of the long exact sequence lands in the kernel of that map and exhausts it, and a map out of
a zero object has trivial image. -/
public theorem injective_cohomologyOverFieldMap_succ_of_isZero
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    (h : IsZero (cohomologyOverField k f S.X₃ n)) :
    Function.Injective (cohomologyOverFieldMap k f S.f (n + 1)) := by
  obtain ⟨d, -, -, -, hex⟩ := exists_cohomologyOverField_longExactSequence k f hS
  have hsub : Subsingleton (cohomologyOverField k f S.X₃ n) :=
    ModuleCat.subsingleton_of_isZero h
  have hzero : ∀ y : cohomologyOverField k f S.X₁ (n + 1),
      cohomologyOverFieldMap k f S.f (n + 1) y = 0 → y = 0 := by
    intro y hy
    obtain ⟨z, hz⟩ := (hex n y).1 hy
    rw [← hz, Subsingleton.elim z 0, map_zero]
  intro a b hab
  have hd : cohomologyOverFieldMap k f S.f (n + 1) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.1 (hzero _ hd)

end AlgebraicGeometry

end
