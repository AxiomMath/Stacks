module

public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# Additivity of the Euler characteristic from the two outer terms of a short exact sequence

`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional_of_isZero` states
Tag 08AA with the two facts that make `χ` well defined — finite dimensionality of each
`Hⁱ(X, ℱ)` (Tag 02O6) and vanishing of all but finitely many of them (Tag 01XJ) — carried as
hypotheses for **all three** modules of the short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0`.

Three of those six hypotheses are redundant. The long exact sequence of cohomology, which
`AlgebraicGeometry.exists_cohomologyOverField_longExactSequence` proves unconditionally, places
`Hⁿ(X, ℱ₂)` in an exact sequence between `Hⁿ(X, ℱ₁)` and `Hⁿ(X, ℱ₃)`, and both finite
dimensionality and vanishing propagate across such a sequence. This file proves that, and
restates Tag 08AA with hypotheses on `ℱ₁` and `ℱ₃` only. The finite-dimensionality hypothesis is
simultaneously weakened to the degrees below the vanishing bound, since a vanishing cohomology
group is finite-dimensional for free.

## Main results

* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_shortExact`: `Hⁿ(X, ℱ₂)` is
  finite-dimensional as soon as `Hⁿ(X, ℱ₁)` and `Hⁿ(X, ℱ₃)` are.
* `AlgebraicGeometry.isZero_cohomologyOverField_of_shortExact`: `Hⁿ(X, ℱ₂)` vanishes as soon as
  `Hⁿ(X, ℱ₁)` and `Hⁿ(X, ℱ₃)` do.
* `AlgebraicGeometry.finsum_alternating_finrank_cohomologyOverField_add_of_shortExact_of_outer`:
  additivity of the alternating sum of dimensions of cohomology, with the two cited inputs
  assumed for the outer two modules only.
* `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_outer`: the statement of Tag 08AA
  with the two cited inputs assumed for the outer two modules only, and the finite
  dimensionality only below the vanishing bound.
* `Module.finiteDimensional_of_exact` and `AlgebraicGeometry.finiteDimensional_of_isZero`: the
  two linear-algebra inputs of that propagation. They are public rather than private because
  `StacksFrontier/AlgebraicGeometry/CohomologyFinitenessDevissage/Basic.lean` runs the same
  propagation in the other two positions of the long exact sequence and in the degrees above the
  vanishing bound, and should share these proofs rather than restate them.

## Implementation notes

**What is proved and what is assumed.** Everything here is unconditional. No `@[stacks 08AA]`
attribute is attached here: what the last theorem below assumes is the content of Tags 02O6 and
01XJ, for two of the three modules instead of for all three. Both of those are theorems now, and
the tag is attached where they are discharged, on
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact` in
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/AdditivityUnconditional.lean`. The hypotheses
of properness and coherence are present only because
`AlgebraicGeometry.eulerCharacteristic` is defined under them, and are used nowhere.

**Finite dimensionality across an exact sequence.** Mathlib's `Module.Finite.of_exact` asks for
the second map to be surjective. The map `Hⁿ(X, ℱ₂) ⟶ Hⁿ(X, ℱ₃)` is not, so it is replaced by
its restriction to its range, which is finite-dimensional as a submodule of a
finite-dimensional space; exactness is unaffected because the inclusion of the range is
injective.

**Vanishing across an exact sequence** uses only the one exactness
`Hⁿ(X, ℱ₁) ⟶ Hⁿ(X, ℱ₂) ⟶ Hⁿ(X, ℱ₃)`, not the connecting maps: a class in `Hⁿ(X, ℱ₂)` maps to
zero because the target is zero, hence comes from `Hⁿ(X, ℱ₁)`, which is zero.

## References

* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace Module

variable {K : Type*} [Field K]

/-- A `K`-vector space sitting in an exact sequence between two finite-dimensional ones is
finite-dimensional. -/
theorem finiteDimensional_of_exact {A B C : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C] [FiniteDimensional K A]
    [FiniteDimensional K C] (a : A →ₗ[K] B) (b : B →ₗ[K] C) (hab : Function.Exact a b) :
    FiniteDimensional K B := by
  have hrange : Function.Exact a b.rangeRestrict := by
    intro y
    rw [← hab y]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  exact Module.Finite.of_exact hrange b.surjective_rangeRestrict

end Module

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A cohomology group that vanishes is finite-dimensional. -/
theorem finiteDimensional_of_isZero {M : ModuleCat.{u} k} (h : IsZero M) :
    FiniteDimensional k M :=
  have : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  have : Finite M := Finite.of_subsingleton
  inferInstance

/-- **Finite dimensionality of the middle cohomology of a short exact sequence.** If `Hⁿ(X, ℱ₁)`
and `Hⁿ(X, ℱ₃)` are finite-dimensional over `k`, so is `Hⁿ(X, ℱ₂)`: the three sit in an exact
sequence by `AlgebraicGeometry.exists_cohomologyOverField_longExactSequence`. There is no
hypothesis on `f` or on the modules. -/
theorem finiteDimensional_cohomologyOverField_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (n : ℕ) (h₁ : FiniteDimensional k (cohomologyOverField k f S.X₁ n))
    (h₃ : FiniteDimensional k (cohomologyOverField k f S.X₃ n)) :
    FiniteDimensional k (cohomologyOverField k f S.X₂ n) := by
  obtain ⟨_, _, hab, _, _⟩ := exists_cohomologyOverField_longExactSequence k f hS
  exact Module.finiteDimensional_of_exact (cohomologyOverFieldMap k f S.f n).hom
    (cohomologyOverFieldMap k f S.g n).hom (hab n)

/-- **Vanishing of the middle cohomology of a short exact sequence.** If `Hⁿ(X, ℱ₁)` and
`Hⁿ(X, ℱ₃)` vanish, so does `Hⁿ(X, ℱ₂)`. There is no hypothesis on `f` or on the modules. -/
theorem isZero_cohomologyOverField_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (n : ℕ) (h₁ : IsZero (cohomologyOverField k f S.X₁ n))
    (h₃ : IsZero (cohomologyOverField k f S.X₃ n)) :
    IsZero (cohomologyOverField k f S.X₂ n) := by
  obtain ⟨_, _, hab, _, _⟩ := exists_cohomologyOverField_longExactSequence k f hS
  have hs₁ := ModuleCat.subsingleton_of_isZero h₁
  have hs₃ := ModuleCat.subsingleton_of_isZero h₃
  have hz : ∀ z : cohomologyOverField k f S.X₂ n, z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (hab n z).1 (Subsingleton.elim _ _)
    rw [← hw, Subsingleton.elim w 0, map_zero]
  exact ModuleCat.isZero_iff_subsingleton.2 ⟨fun x y => by rw [hz x, hz y]⟩

/-- **Additivity of the alternating sum of dimensions of cohomology along a short exact
sequence, from the outer two terms.** The finite dimensionality of Tag 02O6 and the vanishing of
Tag 01XJ are assumed for `ℱ₁` and `ℱ₃` only, the finite dimensionality only in the degrees below
the vanishing bound; for `ℱ₂` both follow from the long exact sequence. -/
theorem finsum_alternating_finrank_cohomologyOverField_add_of_shortExact_of_outer
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (N : ℕ)
    (hfin₁ : ∀ n < N, FiniteDimensional k (cohomologyOverField k f S.X₁ n))
    (hfin₃ : ∀ n < N, FiniteDimensional k (cohomologyOverField k f S.X₃ n))
    (hvan₁ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f S.X₁ n))
    (hvan₃ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f S.X₃ n)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f S.X₂ n) : ℤ)) =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f S.X₁ n) : ℤ)) +
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f S.X₃ n) : ℤ) := by
  have hall₁ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₁ n) := fun n =>
    if h : n < N then hfin₁ n h else finiteDimensional_of_isZero k (hvan₁ n (by omega))
  have hall₃ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₃ n) := fun n =>
    if h : n < N then hfin₃ n h else finiteDimensional_of_isZero k (hvan₃ n (by omega))
  exact finsum_alternating_finrank_cohomologyOverField_add_of_shortExact k f hS hall₁
    (fun n => finiteDimensional_cohomologyOverField_of_shortExact k f hS n (hall₁ n) (hall₃ n))
    hall₃ N hvan₁
    (fun n hn => isZero_cohomologyOverField_of_shortExact k f hS n (hvan₁ n hn) (hvan₃ n hn))
    hvan₃

/-- **Tag 08AA with its two cited inputs assumed for the outer two terms only.** For a proper
scheme over a field and a short exact sequence of coherent modules,
`χ(X, ℱ₂) = χ(X, ℱ₁) + χ(X, ℱ₃)`, given the finite dimensionality of Tag 02O6 for `ℱ₁` and `ℱ₃`
below the vanishing bound and the vanishing of Tag 01XJ for `ℱ₁` and `ℱ₃`. Properness and
coherence are hypotheses of `AlgebraicGeometry.eulerCharacteristic` and are not used in the
proof. -/
theorem eulerCharacteristic_add_of_shortExact_of_outer [IsProper f]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent] (N : ℕ)
    (hfin₁ : ∀ n < N, FiniteDimensional k (cohomologyOverField k f S.X₁ n))
    (hfin₃ : ∀ n < N, FiniteDimensional k (cohomologyOverField k f S.X₃ n))
    (hvan₁ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f S.X₁ n))
    (hvan₃ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f S.X₃ n)) :
    eulerCharacteristic k f S.X₂ =
      eulerCharacteristic k f S.X₁ + eulerCharacteristic k f S.X₃ := by
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum]
  exact finsum_alternating_finrank_cohomologyOverField_add_of_shortExact_of_outer k f hS N
    hfin₁ hfin₃ hvan₁ hvan₃

end AlgebraicGeometry

end
