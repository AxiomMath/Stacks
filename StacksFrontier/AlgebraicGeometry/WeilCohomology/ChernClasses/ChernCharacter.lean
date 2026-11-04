module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClass

/-!
# The Chern character of a Weil cohomology theory

In the standing situation of Stacks Section 45.12, with `A(X)` a `𝐐`-algebra for every object
`X` of `𝒞`, Tag 0FI9 asserts that there is a unique rule assigning to every `X` a Chern character
`ch^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` which is a ring map, is compatible with pullback, and
sends an invertible module `ℒ` to `exp(c₁^A(ℒ))`. This file writes those three properties down
and proves the uniqueness half.

## Main definitions

* `Stacks.WeilCohomology.IsChernCharacter`: the three properties of Tag 0FI9 — that `ch^A` is a
  ring map, that it is compatible with pullback, and that its value on an invertible module is
  the exponential of the first Chern class — together with the requirement that the `n`-th
  component lie in `A^n(X)`.

## Main results

* `Stacks.WeilCohomology.IsChernCharacter.map_sum`: a Chern character is additive on a finite
  sum of classes, componentwise.
* `Stacks.WeilCohomology.eq_of_isChernCharacter`: **the uniqueness half of Tag 0FI9.** Two rules
  with the three properties agree on the class of every finite locally free module of constant
  rank.

## The uniqueness argument

The source omits the proof of uniqueness. It is the argument of Tag 0FI5's uniqueness, made
shorter by the fact that addition in `∏_{i ≥ 0} A^i(X)` is componentwise: for a module `ℰ` of
constant rank `r`, the splitting principle of Tag 0FI7 supplies `p : P ⟶ X` with `p^*` injective
on `A` and a filtration of `p^*ℰ` of length `r` with invertible successive quotients. In
`K₀(Vect(P))` the filtration gives `[p^*ℰ] = ∑_j [ℒ_j]`, so additivity writes `ch^A([p^*ℰ])` as
`∑_j ch^A([ℒ_j])`, each term pinned down by the value on an invertible module. Compatibility
with pullback identifies the result with `p^*ch^A([ℰ])`, and `p^*` is injective.

## What is covered of Tag 0FI9, and what is not

Covered: the uniqueness half, for the class of a finite locally free module of constant rank.

Not covered: the existence half. The source constructs `ch^A(ℰ)` as
`r^A(ℰ) + ∑_{i ≥ 1} (1/i!) P_i(c_1^A(ℰ), …, c_i^A(ℰ))`, with `P_i` the power-sum polynomials of
Chow Homology, Example 42.43.6 — `AlgebraicGeometry.powerSumPolynomial` in this repository — and
`r^A(ℰ) ∈ A^0(ℰ)` the locally constant rank, read through the decomposition of `X` into the open
and closed loci on which `ℰ` has constant rank. That rank is unavailable here: it is indexed by
condition (2) of the source's situation, the splitting `A(U ⨿ V) = A(U) × A(V)`, which
`Stacks.WeilCohomology.ChernSetup` does not transcribe, as is the finiteness of the
decomposition, which is clause (1), quasi-compactness of the objects of `𝒞`. The Chern classes
`c_i^A` the formula consumes are moreover those of the rule of Tag 0FI5 on all of `K₀`, whose
existence likewise rests on condition (5); what this repository has is the Chern classes of a
single module of constant rank,
`Stacks.WeilCohomology.ChernSetup.chernClass`.

Two further departures, both recorded in the attribute string:

* **Constant rank.** The source's `ch^A` is defined on the class of an arbitrary finite locally
  free module; the splitting principle used here, like the source's, needs a constant rank, and
  the source's reduction to that case is condition (2) again.
* **Compatibility with pullback on generators.** The source states `f^* ∘ ch^A = ch^A ∘ f^*` with
  the right-hand `f^*` the induced map on `K₀(Vect(-))`. That map does not exist in this
  repository: it needs the pullback of a short exact sequence of finite locally free modules to
  stay exact, which holds because such a sequence is locally split and is nowhere formalised.
  The property is therefore stated on the generators `[ℰ]`, which is the form the source's own
  proof uses; the two agree as soon as the `K₀`-level map exists, since both sides are additive.

## Implementation notes

`∏_{i ≥ 0} A^i(X)` is read as the family of components, `ℕ → A(X)` with the `n`-th component in
`A^n(X)`, exactly as for the total Chern class. Being a ring map is then: additivity
componentwise, the convolution `ch_n(αβ) = ∑_{i + j = n} ch_i(α) ch_j(β)` for the product, and
the value `1` in degree zero and `0` elsewhere on the unit `[𝒪_X]`. This avoids constructing the
completed graded ring, whose only role in the source is to carry that product.

`exp(c₁^A(ℒ))` is read coefficientwise, its `n`-th component being
`(1/n!) · c₁^A(ℒ)^n`; this is where `A(X)` being a `𝐐`-algebra is used, and that hypothesis is
carried as an instance on the family of rings `A`.

## References

* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **The three properties of Tag 0FI9's Chern character.** A rule `ch` assigns to every object
`X` of `𝒞` and every class `α` of `K₀(Vect(X))` the components `ch X α n` of its Chern
character, the `n`-th lying in `A^n(X)`; it is a ring map to `∏_{i ≥ 0} A^i(X)`, it is
compatible with pullback on the classes of modules, and it takes the value `exp(c₁^A(ℒ))` on an
invertible module. -/
structure IsChernCharacter (𝔄 : ChernSetup.{u, v, v₁, w} C S)
    [∀ X : C, Algebra ℚ (𝔄.A X)]
    (ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X) : Prop where
  /-- The `n`-th component lies in `A^n(X)`, so that `ch` lands in `∏_{i ≥ 0} A^i(X)`. -/
  mem_grade : ∀ (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ), ch X α n ∈ 𝔄.grade X n
  /-- **Property (1).** `ch^A` is additive, the addition of `∏_{i ≥ 0} A^i(X)` being
  componentwise. -/
  map_add : ∀ (X : C) (α β : VectorBundleKZero (S.obj X)) (n : ℕ),
    ch X (α + β) n = ch X α n + ch X β n
  /-- **Property (1).** `ch^A` is multiplicative, the multiplication of `∏_{i ≥ 0} A^i(X)` being
  the convolution. -/
  map_mul : ∀ (X : C) (α β : VectorBundleKZero (S.obj X)) (n : ℕ),
    ch X (α * β) n = ∑ p ∈ Finset.antidiagonal n, ch X α p.1 * ch X β p.2
  /-- **Property (1).** `ch^A` sends the unit `[𝒪_X]` of `K₀(Vect(X))` to the unit. -/
  map_one : ∀ (X : C) (n : ℕ), ch X 1 n = if n = 0 then 1 else 0
  /-- **Property (2).** `f^* ∘ ch^A = ch^A ∘ f^*`, on the class of a module. -/
  map_pull : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules) (n : ℕ),
    𝔄.pull f (ch Y (VectorBundleKZero.classOf (S.obj Y) E) n) =
      ch X (VectorBundleKZero.classOf (S.obj X)
        ((Scheme.Modules.pullback (S.map f)).obj E)) n
  /-- **Property (3).** `ch^A([ℒ]) = exp(c₁^A(ℒ))` for an invertible module `ℒ`, read
  coefficientwise. -/
  invertible : ∀ (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (n : ℕ),
    ch X (VectorBundleKZero.classOf (S.obj X) L) n =
      algebraMap ℚ (𝔄.A X) ((n.factorial : ℚ)⁻¹) *
        𝔄.c₁ X (picardClassOf (S.obj X) L hL) ^ n

namespace IsChernCharacter

variable {𝔄 : ChernSetup.{u, v, v₁, w} C S} [∀ X : C, Algebra ℚ (𝔄.A X)]
  {ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}

/-- The Chern character of the zero class vanishes in every degree. -/
theorem map_zero (h : IsChernCharacter 𝔄 ch) (X : C) (n : ℕ) : ch X 0 n = 0 := by
  simpa using h.map_add X 0 0 n

/-- **A Chern character is additive on a finite sum of classes**, componentwise. -/
theorem map_sum (h : IsChernCharacter 𝔄 ch) (X : C) {ι : Type*} (s : Finset ι)
    (α : ι → VectorBundleKZero (S.obj X)) (n : ℕ) :
    ch X (∑ i ∈ s, α i) n = ∑ i ∈ s, ch X (α i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_zero X n
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, h.map_add, ih, Finset.sum_insert ha]

end IsChernCharacter

/-- **The uniqueness half of Stacks Tag 0FI9.** Properties (1), (2) and (3) determine the Chern
character of the class of a finite locally free module of constant rank: any two rules with those
properties agree there.

The splitting principle of Tag 0FI7 supplies `p : P ⟶ X` with `p^*` injective on `A` and a
filtration of `p^*ℰ` with invertible successive quotients. That filtration writes `[p^*ℰ]` as a
sum of classes of invertible modules in `K₀(Vect(P))`, where additivity and the value on an
invertible module determine the Chern character; property (2) identifies the result with
`p^*ch^A([ℰ])`, and `p^*` is injective. -/
@[stacks 0FI9 "uniqueness, for the class of a module of constant rank; the existence half needs
the locally constant rank r^A, which is indexed by condition (2) of the situation, and the Chern
classes of Tag 0FI5 on all of K₀, and property (2) is stated on generators — see the module
documentation"]
theorem eq_of_isChernCharacter {𝔄 : ChernSetup.{u, v, v₁, w} C S}
    [∀ X : C, Algebra ℚ (𝔄.A X)]
    {ch ch' : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hch : IsChernCharacter 𝔄 ch) (hch' : IsChernCharacter 𝔄 ch') (X : C)
    (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (n : ℕ) :
    ch X (VectorBundleKZero.classOf (S.obj X) E) n =
      ch' X (VectorBundleKZero.classOf (S.obj X) E) n := by
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔄.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  refine hinj ?_
  rw [hch.map_pull p E n, hch'.map_pull p E n, hsum, hch.map_sum, hch'.map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [hch.invertible P (L j) (hL j) n, hch'.invertible P (L j) (hL j) n]

end Stacks.WeilCohomology

end
