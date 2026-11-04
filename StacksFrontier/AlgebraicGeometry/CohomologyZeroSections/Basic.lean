module

public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# A global section of the middle term of a short exact sequence that is not a section of the sub

Let `X` be a scheme over a field `k` and let `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` be a short exact sequence
of modules on `X`. If `H¹(X, ℱ₁)` is finite-dimensional and `H⁰(X, ℱ₃)` contains more
`k`-linearly independent elements than the dimension of `H¹(X, ℱ₁)`, then
`H⁰(X, ℱ₁) ⟶ H⁰(X, ℱ₂)` is not surjective: there is a global section of `ℱ₂` which is not the
image of a global section of `ℱ₁`.

This is the counting step in the proof of [Stacks, Tag 0A27], applied there to the sequence
`0 ⟶ 𝒪_X ⟶ 𝒪_X(n·x) ⟶ 𝒪_{n·x} ⟶ 0`.

## Main results

* `AlgebraicGeometry.not_surjective_cohomologyOverFieldMap_zero_of_linearIndependent`: the
  counting step at the level of cohomology: `H⁰(X, ℱ₁) ⟶ H⁰(X, ℱ₂)` is not surjective.
* `AlgebraicGeometry.exists_forall_app_ne_of_linearIndependent`: the same conclusion as a
  statement about global sections.
* `AlgebraicGeometry.exists_forall_app_ne_of_le_finrank`: the dimension form, under the
  hypotheses `dim_k H¹(X, ℱ₁) < d` and `d ≤ dim_k H⁰(X, ℱ₃)`.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### The counting step -/

/-- **`H⁰(X, ℱ₁) ⟶ H⁰(X, ℱ₂)` is not surjective when `H⁰(X, ℱ₃)` is too big for
`H¹(X, ℱ₁)`.** Let `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` be a short exact sequence of modules on a scheme `X`
over `k`, with `H¹(X, ℱ₁)` finite-dimensional of dimension less than `d`, and suppose
`H⁰(X, ℱ₃)` contains `d` linearly independent elements. Then not every class in `H⁰(X, ℱ₂)`
comes from `H⁰(X, ℱ₁)`. -/
theorem not_surjective_cohomologyOverFieldMap_zero_of_linearIndependent
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 1)]
    {d : ℕ} (v : Fin d → cohomologyOverField k f S.X₃ 0) (hv : LinearIndependent k v)
    (hd : Module.finrank k (cohomologyOverField k f S.X₁ 1) < d) :
    ¬ Function.Surjective (cohomologyOverFieldMap k f S.f 0) := by
  obtain ⟨δ, -, hexf, hexg, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  intro hsurj
  have hgzero : ∀ y : cohomologyOverField k f S.X₂ 0, cohomologyOverFieldMap k f S.g 0 y = 0 :=
    fun y => (hexf 0 y).2 (hsurj y)
  have hker : ∀ z : cohomologyOverField k f S.X₃ 0, δ 0 z = 0 → z = 0 := by
    intro z hz
    obtain ⟨y, hy⟩ := (hexg 0 z).1 hz
    exact hy.symm.trans (hgzero y)
  have hinj₀ : Function.Injective (δ 0) := fun a b hab => by
    have h := hker (a - b) (by simp [map_sub, hab])
    linear_combination (norm := module) h
  let δ' : cohomologyOverField k f S.X₃ 0 ⟶ cohomologyOverField k f S.X₁ 1 := δ 0
  have hinj : Function.Injective δ' := hinj₀
  have hli : LinearIndependent k fun i => δ' (v i) :=
    hv.map' δ'.hom (by rwa [LinearMap.ker_eq_bot])
  have hcard := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

/-- **A global section of `ℱ₂` that is not a section of `ℱ₁`.** For a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on a scheme over `k` with `H¹(X, ℱ₁)` finite-dimensional of
dimension less than `d`, and `d` linearly independent elements of `H⁰(X, ℱ₃)`, there is a
global section of `ℱ₂` which is not the image of any global section of `ℱ₁`. -/
theorem exists_forall_app_ne_of_linearIndependent
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 1)]
    {d : ℕ} (v : Fin d → cohomologyOverField k f S.X₃ 0) (hv : LinearIndependent k v)
    (hd : Module.finrank k (cohomologyOverField k f S.X₁ 1) < d) :
    ∃ s : Γ(S.X₂, ⊤), ∀ t : Γ(S.X₁, ⊤), S.f.app ⊤ t ≠ s := by
  obtain ⟨a, ha⟩ := not_forall.1
    (not_surjective_cohomologyOverFieldMap_zero_of_linearIndependent k f hS v hv hd)
  refine ⟨cohomologyOverFieldZeroEquivSections k f S.X₂ a,
    fun t ht => ha ⟨(cohomologyOverFieldZeroEquivSections k f S.X₁).symm t, ?_⟩⟩
  refine (cohomologyOverFieldZeroEquivSections k f S.X₂).injective ?_
  rw [cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap, Equiv.apply_symm_apply, ht]

/-- **A global section of `ℱ₂` that is not a section of `ℱ₁`, dimension form.** For a short exact
sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on a scheme over `k`, if `H¹(X, ℱ₁)` is
finite-dimensional with `dim_k H¹(X, ℱ₁) < d ≤ dim_k H⁰(X, ℱ₃)`, then some global section of
`ℱ₂` is not the image of any global section of `ℱ₁`. -/
theorem exists_forall_app_ne_of_le_finrank
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 1)] {d : ℕ}
    (hd : Module.finrank k (cohomologyOverField k f S.X₁ 1) < d)
    (hd' : d ≤ Module.finrank k (cohomologyOverField k f S.X₃ 0)) :
    ∃ s : Γ(S.X₂, ⊤), ∀ t : Γ(S.X₁, ⊤), S.f.app ⊤ t ≠ s :=
  have ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hd'
  exists_forall_app_ne_of_linearIndependent k f hS v hv hd

end AlgebraicGeometry

end
