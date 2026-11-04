module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionChernFormula
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.BoundedDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.ChernCharacterFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.CodimensionGrading
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SmoothComparison
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.TransportedProduct
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularSchemes
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksCore.Tactic.StacksAttribute

/-!
# The rational intersection product on a regular scheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a
quasi-compact regular scheme of finite type over `S` with affine diagonal and `δ_{X/S}` bounded.
Lemma 0FEY asserts that

  `Φ : K_0(Vect(X)) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`,   `α' ↦ ch(α') ∩ [X]`,

is bijective. Section 0FEX then defines the intersection product

  `α · β = ch(α') ∩ β`,   `α = ch(α') ∩ [X]`,

on `CH_*(X) ⊗ 𝐐`. This file proves Lemma 0FEY, from Proposition 0FEW and Lemma 0FEG, and develops
the product:

* the product is bilinear, the unique one with `(ch(α') ∩ [X]) · β = ch(α') ∩ β`, commutative and
  associative with unit `[X]`, because the operators `ch(α') ∩ -` pairwise commute
  ("Chern classes commute");
* it respects the codimension grading, `CH^i(X) ⊗ 𝐐 · CH^j(X) ⊗ 𝐐 ⊆ CH^{i+j}(X) ⊗ 𝐐`, and on
  `α ∈ CH^i(X) ⊗ 𝐐` it is `α · β = ch_i(α') ∩ β`: since `[X]` has codimension `0` and
  `ch_p(α') ∩ -` raises the codimension by `p`, the components `ch_p(α') ∩ [X]` of `α` with
  `p ≠ i` vanish, and with them the components `ch_p(α') ∩ β = ch(β') ∩ ch_p(α') ∩ [X]` of
  `α · β`;
* **Stacks 0FF9.** For `f : X ⟶ Y` a morphism of quasi-compact regular finite dimensional schemes
  with affine diagonal over `S`, `f` is a local complete intersection morphism (Stacks 0E9K), and
  if its Gysin map exists then `f^!(α · β) = f^!α · f^!β`: writing `α = c ∩ [Y]`, `β = c' ∩ [Y]`
  with `c = ch(α')`, the Gysin map commutes with `c` (Stacks 0FF6) and `f^![Y] = [X]`
  (Stacks 0FF7), so both sides are `ch(f^*α') ∩ f^!β`;
* **Stacks 0FFA.** If moreover `f` is proper, `f_*(α · f^!β) = f_*α · β`: writing
  `β = ch(β') ∩ [Y]`, `α · f^!β = ch(f^*β') ∩ α` and the projection formula gives
  `f_*(ch(f^*β') ∩ α) = ch(β') ∩ f_*α`;
* **Stacks 0FFF.** For `X` smooth and quasi-compact over a field `k` with affine diagonal, the
  intersection product of Section 0FC0 agrees after tensoring with `𝐐` with the product of
  Section 0FEX: on each part `X_d` of constant dimension `d`, Stacks 0FC2 gives
  `(c ∩ [X_d]) · β = c ∩ β`, so the product of Section 0FEX restricts on `X_d` to the product of
  Section 0FC0.

## Main definitions

* `Stacks.Chow.rationalIntersectionProduct` — the product `α · β = ch(Φ⁻¹ α) ∩ β` of
  Section 0FEX.
* `Stacks.Chow.rationalChernCharacterComponentCap` — the operator `ch_p(α') ∩ -`.
* `Stacks.Chow.codimensionToRationalChow` — the class in `CH_*(X) ⊗ 𝐐` of
  `α ∈ CH^i(X) = ∏_d CH_{d-i}(X_d)`, for `X` smooth and quasi-compact over `k`.
* `Stacks.Chow.codimensionRationalChowEquiv` — the identification
  `CH^*(X) ⊗ 𝐐 = (⨁_i CH^i(X)) ⊗ 𝐐 ≅ CH_*(X) ⊗ 𝐐` it induces.

## Main results

* `Stacks.Chow.bijective_rationalChernCharacterCapFundamentalClass` — Stacks 0FEY.
* `Stacks.Chow.rationalIntersectionProduct_rationalChernCharacterCap` —
  `(ch(α') ∩ [X]) · β = ch(α') ∩ β`; `Stacks.Chow.eq_rationalIntersectionProduct` — uniqueness.
* `Stacks.Chow.rationalIntersectionProduct_comm`, `Stacks.Chow.rationalIntersectionProduct_assoc`,
  `Stacks.Chow.rationalFundamentalClass_rationalIntersectionProduct`,
  `Stacks.Chow.rationalIntersectionProduct_rationalFundamentalClass` — commutative, associative,
  with unit `[X]`.
* `Stacks.Chow.rationalIntersectionProduct_mem_codimensionChowSubmodule` — the product is graded
  by codimension; `Stacks.Chow.rationalIntersectionProduct_eq_rationalChernCharacterComponentCap`
  — `α · β = ch_i(α') ∩ β` for `α ∈ CH^i(X) ⊗ 𝐐`.
* `isLocalCompleteIntersectionMorphism_and_lciGysinRational_rationalIntersectionProduct` —
  Stacks 0FF9.
* `Stacks.Chow.isLocalCompleteIntersectionMorphism_and_projectionFormula_rationalIntersection`
  — Stacks 0FFA.
* `Stacks.Chow.rationalRestrictPart_rationalIntersectionProduct` — on a part `X_d` the product of
  Section 0FEX is the product of Section 0FC0.
* `Stacks.Chow.codimensionRationalChowEquiv_codimensionIntersectionProduct` — Stacks 0FFF;
  `Stacks.Chow.rationalIntersectionProduct_codimensionToRationalChow`,
  `Stacks.Chow.rationalIntersectionProduct_of_one_tmul_codimensionToRationalChow` and
  `Stacks.Chow.rationalIntersectionProduct_of_one_tmul` — the same on classes graded by
  codimension or dimension.

## Implementation notes

"Quasi-compact of finite type over `S`" is expressed as `[CompactSpace X]` in the statements of the
lemmas of the source, and as `AlgebraicGeometry.IsNoetherian X` in the construction (the
fundamental class `[X] ∈ CH_*(X) ⊗ 𝐐` is defined for Noetherian `X`); for `X` locally of finite
type over `S` the two are equivalent (`Stacks.Chow.isNoetherian_of_compactSpace`). The product
`Stacks.Chow.rationalIntersectionProduct` takes the regularity of `X` and the bounds of
`δ_{X/S}` as arguments and is the transported product `Stacks.Chow.transportedProduct` along the
bijection of Lemma 0FEY. No multiplicativity of the Chern character enters (just the
commutativity of the operators `ch(α') ∩ -`). The source's reformulation, that `Φ` is a ring
isomorphism onto `CH^*(X) ⊗ 𝐐` for a unique such product, uses `ch(α'β') = ch(α') ch(β')`
(Stacks 0F9D) and is in
`StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.RationalIntersectionRing`.

The source picks `α' ∈ K_0(Vect(X)) ⊗ 𝐐` for `α ∈ CH^i(X)` and shows that only `ch_i(α')`
contributes by an Adams operation argument (Lemma 0FEN). Here the same conclusion is reached from
the codimension grading: `ch_p(α') ∩ [X] ∈ CH^p(X) ⊗ 𝐐`, so the components of `α ∈ CH^i(X) ⊗ 𝐐`
of codimension `p ≠ i` vanish.

The source states the product, Stacks 0FF9 and Stacks 0FFA in `CH^*(-) ⊗ 𝐐`; here they are stated
on `CH_*(-) ⊗ 𝐐 = ⨁_k CH_k(-) ⊗ 𝐐`, which for a regular scheme is the internal direct sum of the
codimension pieces `Stacks.Chow.codimensionChowSubmodule`
(`Stacks.Chow.isInternal_codimensionChowSubmodule_of_isRegular`).

For Stacks 0FFF the intersection product of Section 0FC0 is
`Stacks.Chow.codimensionIntersectionProduct`, on `CH^i(X) = ∏_d CH_{d-i}(X_d)`, the product over
the open and closed parts `X_d` of `X` of dimension `d`. Its classes are sent to
`CH_*(X) ⊗ 𝐐` by `α ↦ ∑_d (i_d)_*(1 ⊗ α_d)`, the sum over the finitely many nonempty parts; this
is an isomorphism `(⨁_i CH^i(X)) ⊗ 𝐐 ≅ CH_*(X) ⊗ 𝐐`, whose inverse sends `z ∈ CH_m(X)` to its
restrictions `z|_{X_d}` placed in codimension `d - m`.

## References

* [Stacks Project, Section 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
* [Stacks Project, Tag 0FEY](https://stacks.math.columbia.edu/tag/0FEY)
* [Stacks Project, Tag 0FF9](https://stacks.math.columbia.edu/tag/0FF9)
* [Stacks Project, Tag 0FFA](https://stacks.math.columbia.edu/tag/0FFA)
* [Stacks Project, Tag 0FFF](https://stacks.math.columbia.edu/tag/0FFF)
* [Stacks Project, Tag 0E9K](https://stacks.math.columbia.edu/tag/0E9K)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FEW](https://stacks.math.columbia.edu/tag/0FEW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

/-! ### Stacks 0FEY -/

section Isomorphism

/-- **A quasi-compact scheme locally of finite type over the base is Noetherian**, the base being
locally Noetherian. -/
theorem isNoetherian_of_compactSpace {C : ChowSituation.{u}} {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] [CompactSpace X] : IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  ⟨⟩

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The map `α' ↦ ch(α') ∩ [X]` of Stacks 0FEY, read as the operators `ch(α') ∩ -` evaluated at
`[X]`, is `Stacks.Chow.rationalChernCharacterCapFundamentalClass`. -/
theorem flip_rationalChernCharacterCap_rationalFundamentalClass [IsNoetherian X] :
    (rationalChernCharacterCap C sX).flip (rationalFundamentalClass C sX) =
      rationalChernCharacterCapFundamentalClass C sX :=
  LinearMap.ext fun x => (rationalChernCharacterCapFundamentalClass_apply C sX x).symm

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **Stacks Project, Tag 0FEY.** Let `(S, δ)` be as in Situation 42.7.1 and let `X` be a
quasi-compact regular scheme of finite type over `S` with affine diagonal and `δ_{X/S}` bounded.
Then the composition

  `K_0(Vect(X)) ⊗ 𝐐 ⟶ ∏_p A^p(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`,   `α ↦ ch(α) ∩ [X]`,

of the Chern character of Remark 0FEM and the map `c ↦ c ∩ [X]` is bijective.

The map is `Stacks.Chow.rationalChernCharacterCapFundamentalClass`, the sum over `p` of
`ch_p(α) ∩ [X]` (`Stacks.Chow.rationalChernCharacterCapFundamentalClass_eq_sum`). The proof is
`Stacks.Chow.bijective_rationalChernCharacterCapFundamentalClass_of_chernFormula` (Proposition 0FEW
for `X = Y`, Remark 0FEU) applied to Lemma 0FEG
(`Stacks.Chow.isRegularImmersionChernFormula_of_compactSpace`). -/
@[stacks 0FEY "the whole lemma: for X quasi-compact, regular, of finite type over S, with affine \
diagonal and δ_{X/S} bounded, α ↦ ch(α) ∩ [X], K_0(Vect(X)) ⊗ Q → A^*(X) ⊗ Q → CH_*(X) ⊗ Q, is \
bijective; ch is the ring map of 0FEM into ∏_p A^p(X) ⊗ Q, whose cap with [X] is a finite sum \
since δ_{X/S} is bounded"]
theorem bijective_rationalChernCharacterCapFundamentalClass [CompactSpace X] (hX : IsRegular X)
    (hb : ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
      relativeDimension C.dimensionFunction sX x ≤ hi) :
    haveI := isNoetherian_of_compactSpace sX
    Function.Bijective (rationalChernCharacterCapFundamentalClass C sX) := by
  have := isNoetherian_of_compactSpace sX
  obtain ⟨lo, _, hb⟩ := hb
  exact bijective_rationalChernCharacterCapFundamentalClass_of_chernFormula C sX
    (isRegularImmersionChernFormula_of_compactSpace C) hX
    ⟨lo, by rintro _ ⟨x, rfl⟩; exact (hb x).1⟩

variable [IsNoetherian X] {C sX}

/-- **Stacks 0FEY, read through the cap product operator**
`Stacks.Chow.rationalChernCharacterCap`: the form in which the product of Section 0FEX is built. -/
theorem bijective_flip_rationalChernCharacterCap (hX : IsRegular X)
    (hb : ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
      relativeDimension C.dimensionFunction sX x ≤ hi) :
    Function.Bijective ((rationalChernCharacterCap C sX).flip (rationalFundamentalClass C sX)) := by
  rw [flip_rationalChernCharacterCap_rationalFundamentalClass]
  exact bijective_rationalChernCharacterCapFundamentalClass C sX hX hb

end Isomorphism

/-! ### The product -/

section Product

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : IsRegular X)
  (hb : ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
    relativeDimension C.dimensionFunction sX x ≤ hi)

local notation "CHQ" => DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j

include hX hb in
/-- **The intersection product of Stacks Section 0FEX** on `CH_*(X) ⊗ 𝐐`, for `X` Noetherian
(equivalently quasi-compact), regular, of finite type over `S`, with affine diagonal and `δ_{X/S}`
bounded: `α · β = ch(α') ∩ β`, where `α' ∈ K_0(Vect(X)) ⊗ 𝐐` is the unique class with
`ch(α') ∩ [X] = α` (Stacks 0FEY, `Stacks.Chow.bijective_flip_rationalChernCharacterCap`). -/
@[stacks 0FEX "the construction of the section: for X as in 0FEY (Noetherian, equivalently \
quasi-compact, given locally of finite type over S), α · β = ch(α') ∩ β with α' the unique class \
with ch(α') ∩ [X] = α; CH^*(X) ⊗ Q is CH_*(X) ⊗ Q, the internal direct sum of the \
codimension pieces codimensionChowSubmodule"]
def rationalIntersectionProduct : CHQ →ₗ[ℚ] CHQ →ₗ[ℚ] CHQ :=
  transportedProduct (rationalChernCharacterCap C sX) (rationalFundamentalClass C sX)
    (bijective_flip_rationalChernCharacterCap hX hb)

/-- The product unfolded: `α · β = ch(α') ∩ β` with `ch(α') ∩ [X] = α`. -/
theorem rationalIntersectionProduct_apply (α β : CHQ) :
    rationalIntersectionProduct hX hb α β =
      rationalChernCharacterCap C sX
        ((LinearEquiv.ofBijective _ (bijective_flip_rationalChernCharacterCap hX hb)).symm α) β :=
  rfl

/-- **The defining property of the product:** `(ch(α') ∩ [X]) · β = ch(α') ∩ β`. -/
theorem rationalIntersectionProduct_rationalChernCharacterCap (a : ℚ ⊗[ℤ] VectorBundleKZero X)
    (β : CHQ) :
    rationalIntersectionProduct hX hb
        (rationalChernCharacterCap C sX a (rationalFundamentalClass C sX)) β =
      rationalChernCharacterCap C sX a β :=
  transportedProduct_apply_left _ _ (bijective_flip_rationalChernCharacterCap hX hb) a β

/-- If `α = ch(α') ∩ [X]` then `α · β = ch(α') ∩ β`. -/
theorem rationalIntersectionProduct_eq_rationalChernCharacterCap {α : CHQ}
    {a : ℚ ⊗[ℤ] VectorBundleKZero X}
    (ha : rationalChernCharacterCap C sX a (rationalFundamentalClass C sX) = α) (β : CHQ) :
    rationalIntersectionProduct hX hb α β = rationalChernCharacterCap C sX a β := by
  subst ha
  exact rationalIntersectionProduct_rationalChernCharacterCap hX hb a β

/-- **Uniqueness of the product:** a bilinear product with `(ch(α') ∩ [X]) · β = ch(α') ∩ β` for
all `α'` and `β` is the product of Section 0FEX. -/
theorem eq_rationalIntersectionProduct {μ : CHQ →ₗ[ℚ] CHQ →ₗ[ℚ] CHQ}
    (h : ∀ a β, μ (rationalChernCharacterCap C sX a (rationalFundamentalClass C sX)) β =
      rationalChernCharacterCap C sX a β) :
    μ = rationalIntersectionProduct hX hb :=
  eq_transportedProduct _ _ (bijective_flip_rationalChernCharacterCap hX hb) h

/-- **The product is commutative** (Section 0FEX: "this is a symmetric pairing"), the operators
`ch(α') ∩ -` pairwise commuting. -/
@[stacks 0FEX "the product of the section is symmetric: α · β = β · α, for X as in 0FEY"]
theorem rationalIntersectionProduct_comm (α β : CHQ) :
    rationalIntersectionProduct hX hb α β = rationalIntersectionProduct hX hb β α :=
  transportedProduct_comm _ _ (bijective_flip_rationalChernCharacterCap hX hb)
    (commute_rationalChernCharacterCap C sX) α β

/-- **The product is associative** (Section 0FEX): both bracketings of `α · β · γ` are
`ch(α') ∩ ch(β') ∩ ch(γ') ∩ [X]`, up to reordering the commuting operators. -/
@[stacks 0FEX "the product of the section is associative: (α · β) · γ = α · (β · γ), for X as \
in 0FEY"]
theorem rationalIntersectionProduct_assoc (α β γ : CHQ) :
    rationalIntersectionProduct hX hb (rationalIntersectionProduct hX hb α β) γ =
      rationalIntersectionProduct hX hb α (rationalIntersectionProduct hX hb β γ) :=
  transportedProduct_assoc _ _ (bijective_flip_rationalChernCharacterCap hX hb)
    (commute_rationalChernCharacterCap C sX) α β γ

/-- `[X]` is a right unit: `α · [X] = α`. -/
theorem rationalIntersectionProduct_rationalFundamentalClass (α : CHQ) :
    rationalIntersectionProduct hX hb α (rationalFundamentalClass C sX) = α :=
  transportedProduct_apply_base _ _ (bijective_flip_rationalChernCharacterCap hX hb) α

/-- `[X]` is a left unit: `[X] · β = β`. -/
theorem rationalFundamentalClass_rationalIntersectionProduct (β : CHQ) :
    rationalIntersectionProduct hX hb (rationalFundamentalClass C sX) β = β :=
  transportedProduct_base_apply _ _ (bijective_flip_rationalChernCharacterCap hX hb)
    (commute_rationalChernCharacterCap C sX) β

end Product

/-! ### The components of the Chern character -/

section Components

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

local notation "CHQ" => DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j

/-- **The operator `ch_p(α') ∩ -`** on `CH_*(X) ⊗ 𝐐` of `α' ∈ K_0(Vect(X)) ⊗ 𝐐`: the cap operation
of the degree `p` component of the Chern character, `𝐐`-linear in `α'`. -/
def rationalChernCharacterComponentCap (p : ℕ) :
    ℚ ⊗[ℤ] VectorBundleKZero X →ₗ[ℚ] Module.End ℚ CHQ :=
  rationalChowCap C (gysinSystemOfInvertible C) sX p ∘ₗ
    LinearMap.proj (R := ℚ)
      (φ := fun q : ℕ => rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX q) p ∘ₗ
    rationalChernCharacterVectorBundle C sX

/-- `ch_p(α') ∩ -` is the cap operation of the degree `p` component of `ch(α')`. -/
theorem rationalChernCharacterComponentCap_apply (p : ℕ) (a : ℚ ⊗[ℤ] VectorBundleKZero X) :
    rationalChernCharacterComponentCap C sX p a =
      rationalChowCap C (gysinSystemOfInvertible C) sX p
        (rationalChernCharacterVectorBundle C sX a p) :=
  rfl

/-- `ch_p(r ⊗ α) ∩ - = r (ch_p(α) ∩ -)`. -/
theorem rationalChernCharacterComponentCap_tmul (p : ℕ) (r : ℚ) (a : VectorBundleKZero X) :
    rationalChernCharacterComponentCap C sX p (r ⊗ₜ[ℤ] a) =
      r • rationalChowCap C (gysinSystemOfInvertible C) sX p
        (chernCharacterVectorBundle C sX a p) := by
  rw [rationalChernCharacterComponentCap_apply, rationalChernCharacterVectorBundle_tmul,
    Pi.smul_apply, map_smul]

/-- **The operators `ch_p(α') ∩ -` and `ch_q(β') ∩ -` commute**, for all
`α', β' ∈ K_0(Vect(X)) ⊗ 𝐐` and all `p`, `q`. -/
theorem commute_rationalChernCharacterComponentCap (p q : ℕ)
    (x y : ℚ ⊗[ℤ] VectorBundleKZero X) :
    Commute (rationalChernCharacterComponentCap C sX p x)
      (rationalChernCharacterComponentCap C sX q y) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Commute.zero_left _
  | add x x' hx hx' => rw [map_add]; exact hx.add_left hx'
  | tmul r a =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Commute.zero_right _
    | add y y' hy hy' => rw [map_add]; exact hy.add_right hy'
    | tmul r' b =>
      rw [rationalChernCharacterComponentCap_tmul, rationalChernCharacterComponentCap_tmul]
      exact ((commute_rationalChowCap_chernCharacterVectorBundle C sX a b p q).smul_left
        r).smul_right r'

/-- **`ch(α') ∩ - = ∑_{p ≤ N} ch_p(α') ∩ -`** when `δ_{X/S}` takes values in `[lo, hi]` and
`hi - lo ≤ N`: on `CH_k(X) ⊗ 𝐐` the terms with `k - p < lo` vanish, and `CH_k(X) = 0` for
`k > hi`. -/
theorem rationalChernCharacterCap_eq_sum {lo hi : ℤ}
    (hb : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
      relativeDimension C.dimensionFunction sX x ≤ hi) {N : ℕ} (hN : hi - lo ≤ N) :
    rationalChernCharacterCap C sX =
      ∑ p ∈ Finset.range (N + 1), rationalChernCharacterComponentCap C sX p := by
  refine LinearMap.ext fun a => DirectSum.linearMap_ext ℚ fun k => LinearMap.ext fun t => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply]
  by_cases hk : k ≤ hi
  · exact totalRationalChowCap_lof_eq_sum C _ sX lo (fun x => (hb x).1) _ k t _ fun p hp => by
      rw [Finset.mem_range]
      omega
  · have ht : t = 0 := by
      induction t using TensorProduct.induction_on with
      | zero => rfl
      | tmul q y =>
        rw [chowGroup_eq_zero C sX (fun x hx => hk (by have := (hb x).2; omega)) y,
          TensorProduct.tmul_zero]
      | add t t' ht ht' => rw [ht, ht', add_zero]
    simp only [ht, map_zero, Finset.sum_const_zero]

/-- **Capping with a rational class of degree `p` raises the codimension by `p`**: for `X`
Cohen–Macaulay and Noetherian and `c ∈ A^p(X) ⊗ 𝐐`, the operator `c ∩ -` maps `CH^i(X) ⊗ 𝐐` into
`CH^{i+p}(X) ⊗ 𝐐`. -/
theorem rationalChowCap_mem_codimensionChowSubmodule_add [IsNoetherian X]
    (G : GysinSystem C) (hX : IsCohenMacaulay X) (p : ℕ)
    (c : rationalChowCohomologyComponent C G sX p) {i : ℕ} {v : CHQ}
    (hv : v ∈ codimensionChowSubmodule C sX i) :
    rationalChowCap C G sX p c v ∈ codimensionChowSubmodule C sX (i + p) := by
  induction c using TensorProduct.induction_on with
  | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
  | add c c' hc hc' => rw [map_add, LinearMap.add_apply]; exact add_mem hc hc'
  | tmul r c =>
    refine apply_mem_codimensionChowSubmodule_add C sX G hX p c r _ (fun k α => ?_) hv
    rw [rationalChowCap_of_tmul, mul_one]

end Components

/-! ### The grading by codimension -/

section Grading

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : IsRegular X)
  (hb : ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
    relativeDimension C.dimensionFunction sX x ≤ hi)

local notation "CHQ" => DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j

/-- **The product of a class of codimension `i` is computed by `ch_i`** (Section 0FEX). If
`α = ch(α') ∩ [X]` lies in `CH^i(X) ⊗ 𝐐` then `α · β = ch_i(α') ∩ β`, the definition of the
source. -/
@[stacks 0FEX "the defining formula of the section: for α ∈ CH^i(X) ⊗ Q with ch(α') ∩ [X] = α, \
α · β = ch(α') ∩ β = ch_i(α') ∩ β, for X as in 0FEY"]
theorem rationalIntersectionProduct_eq_rationalChernCharacterComponentCap
    {i : ℕ} {α : CHQ} (hα : α ∈ codimensionChowSubmodule C sX i)
    {a : ℚ ⊗[ℤ] VectorBundleKZero X}
    (ha : rationalChernCharacterCap C sX a (rationalFundamentalClass C sX) = α) (β : CHQ) :
    rationalIntersectionProduct hX hb α β = rationalChernCharacterComponentCap C sX i a β := by
  classical
  have hT := bijective_flip_rationalChernCharacterCap hX hb
  obtain ⟨lo, hi, hb'⟩ := id hb
  have hsum := rationalChernCharacterCap_eq_sum C sX hb' (N := max (hi - lo).toNat i)
    (by omega)
  have hrange : i ∈ Finset.range (max (hi - lo).toNat i + 1) := by
    rw [Finset.mem_range]
    omega
  rw [rationalIntersectionProduct, transportedProduct_apply_eq_component _ _ hT
    (isInternal_codimensionChowSubmodule_of_isRegular C sX hX).submodule_iSupIndep hsum
    (fun p _ q _ => commute_rationalChernCharacterComponentCap C sX p q)
    (fun p _ a j x hx => rationalChowCap_mem_codimensionChowSubmodule_add C sX _
      (isCohenMacaulay_of_isRegular hX) p _ hx)
    (directSumRight_one_tmul_totalFundamentalClass_mem_codimensionChowSubmodule_zero C sX) hα,
    ite_eq_left hrange]
  congr 2
  rw [← ha]
  exact (LinearEquiv.ofBijective _ hT).symm_apply_apply a

/-- **The product is graded by codimension** (Section 0FEX: `α · β ∈ CH^{i+j}(X) ⊗ 𝐐`):
`CH^i(X) ⊗ 𝐐 · CH^j(X) ⊗ 𝐐 ⊆ CH^{i+j}(X) ⊗ 𝐐`. -/
@[stacks 0FEX "the product of the section is graded: CH^i(X) ⊗ Q · CH^j(X) ⊗ Q ⊆ \
CH^{i+j}(X) ⊗ Q, for X as in 0FEY"]
theorem rationalIntersectionProduct_mem_codimensionChowSubmodule
    {i j : ℕ} {α β : CHQ} (hα : α ∈ codimensionChowSubmodule C sX i)
    (hβ : β ∈ codimensionChowSubmodule C sX j) :
    rationalIntersectionProduct hX hb α β ∈ codimensionChowSubmodule C sX (i + j) := by
  obtain ⟨a, ha⟩ := (bijective_flip_rationalChernCharacterCap hX hb).2 α
  rw [rationalIntersectionProduct_eq_rationalChernCharacterComponentCap hX hb hα ha, add_comm]
  exact rationalChowCap_mem_codimensionChowSubmodule_add C sX _ (isCohenMacaulay_of_isRegular hX) i
    _ hβ

end Grading

/-! ### Stacks 0FF9 and Stacks 0FFA -/

section Gysin

/-- A morphism `f : X ⟶ Y` over `S` with `X` locally of finite type over `S` is locally of finite
type. -/
theorem locallyOfFiniteType_of_comp_eq {X Y S : Scheme.{u}} {f : X ⟶ Y} {sY : Y ⟶ S}
    {sX : X ⟶ S} (hf : f ≫ sY = sX) [LocallyOfFiniteType sX] : LocallyOfFiniteType f := by
  subst hf
  exact locallyOfFiniteType_of_comp f sY

/-- **Stacks 0FF9, first assertion.** A morphism `f : X ⟶ Y` of schemes locally of finite type over
`S` with `X` and `Y` regular is a local complete intersection morphism (Stacks 0E9K). -/
theorem isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular {X Y S : Scheme.{u}}
    {f : X ⟶ Y} {sY : Y ⟶ S} {sX : X ⟶ S} (hf : f ≫ sY = sX) [LocallyOfFiniteType sX]
    (hX : IsRegular X) (hY : IsRegular Y) : IsLocalCompleteIntersectionMorphism f :=
  have := locallyOfFiniteType_of_comp_eq hf
  isLocalCompleteIntersectionMorphism_of_isRegular f hX hY

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y} (hf : f ≫ sY = sX)

/-- A Noetherian scheme of finite dimension has `δ_{X/S}` bounded below. -/
theorem bddBelow_range_relativeDimension [IsNoetherian X] (hdim : topologicalKrullDim X ≠ ⊤) :
    BddBelow (Set.range (relativeDimension C.dimensionFunction sX)) := by
  obtain ⟨lo, hi, hb⟩ := exists_bounds_relativeDimension C sX hdim
  exact ⟨lo, by rintro _ ⟨x, rfl⟩; exact (hb x).1⟩

variable [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))]

/-- **The Gysin map is multiplicative** (the second assertion of Stacks 0FF9, for Noetherian `X`
and `Y`). Let `f : X ⟶ Y` be a morphism of schemes over `S`, with `X` and `Y` Noetherian, regular,
of finite dimension and with affine diagonal, so that `f` is a local complete intersection
morphism (Stacks 0E9K), and suppose that the Gysin map of `f` exists. Then

  `f^!(α · β) = f^!α · f^!β`

for the products of Section 0FEX: writing `α = ch(α') ∩ [Y]`, the Gysin map commutes with
`ch(α') ∩ -` (Stacks 0FF6) and `f^![Y] = [X]` (Stacks 0FF7). -/
theorem lciGysinRational_rationalIntersectionProduct [IsNoetherian X] [IsNoetherian Y]
    (hXreg : IsRegular X) (hYreg : IsRegular Y) (hXdim : topologicalKrullDim X ≠ ⊤)
    (hYdim : topologicalKrullDim Y ≠ ⊤) (h : GysinMapExists f)
    (α β : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) :
    haveI := locallyOfFiniteType_of_comp_eq hf
    lciGysinRational C sX sY hf
        (isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg) h
        (rationalIntersectionProduct hYreg (exists_bounds_relativeDimension C sY hYdim) α β) =
      rationalIntersectionProduct hXreg (exists_bounds_relativeDimension C sX hXdim)
        (lciGysinRational C sX sY hf
          (isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg) h α)
        (lciGysinRational C sX sY hf
          (isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg) h β) := by
  have := locallyOfFiniteType_of_comp_eq hf
  have : Finite (_root_.ConnectedComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_connectedComponents X
  set hlci := isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg
  have hXb := bddBelow_range_relativeDimension (sX := sX) hXdim
  have hYb := bddBelow_range_relativeDimension (sX := sY) hYdim
  obtain ⟨a, rfl⟩ := (bijective_flip_rationalChernCharacterCap hYreg
    (exists_bounds_relativeDimension C sY hYdim)).2 α
  rw [LinearMap.flip_apply, rationalIntersectionProduct_rationalChernCharacterCap,
    lciGysinRational_rationalChernCharacterCap C sX sY hf hlci h hXb hYb,
    lciGysinRational_rationalChernCharacterCap C sX sY hf hlci h hXb hYb,
    lciGysinRational_rationalFundamentalClass_of_isRegular C sX sY hf hlci h hXreg hYreg,
    rationalIntersectionProduct_rationalChernCharacterCap]

/-- **Stacks Project, Tag 0FF9.** Let `(S, δ)` be as in Situation 42.7.1 and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S` such that both `X` and `Y` are quasi-compact,
regular, have affine diagonal, and finite dimension. Then `f` is a local complete intersection
morphism, and if moreover the Gysin map exists for `f`, then

  `f^!(α · β) = f^!α · f^!β`

for the intersection products of Section 0FEX, on `CH^*(-) ⊗ 𝐐 = CH_*(-) ⊗ 𝐐`. -/
@[stacks 0FF9 "the whole lemma: for f : X → Y over S with X, Y quasi-compact, regular, of finite \
dimension, with affine diagonal, f is a local complete intersection morphism, and if the Gysin map \
of f exists then f^!(α · β) = f^!α · f^!β for the products of 0FEX on CH^*(-) ⊗ Q = CH_*(-) ⊗ Q"]
theorem isLocalCompleteIntersectionMorphism_and_lciGysinRational_rationalIntersectionProduct
    [CompactSpace X] [CompactSpace Y] (hXreg : IsRegular X) (hYreg : IsRegular Y)
    (hXdim : topologicalKrullDim X ≠ ⊤) (hYdim : topologicalKrullDim Y ≠ ⊤) :
    IsLocalCompleteIntersectionMorphism f ∧
      ∀ (h : GysinMapExists f) (α β : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j),
        haveI := isNoetherian_of_compactSpace sX
        haveI := isNoetherian_of_compactSpace sY
        haveI := locallyOfFiniteType_of_comp_eq hf
        lciGysinRational C sX sY hf
            (isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg) h
            (rationalIntersectionProduct hYreg (exists_bounds_relativeDimension C sY hYdim) α β) =
          rationalIntersectionProduct hXreg (exists_bounds_relativeDimension C sX hXdim)
            (lciGysinRational C sX sY hf
              (isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg) h α)
            (lciGysinRational C sX sY hf
              (isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg) h
              β) :=
  have := isNoetherian_of_compactSpace sX
  have := isNoetherian_of_compactSpace sY
  ⟨isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg,
    lciGysinRational_rationalIntersectionProduct hf hXreg hYreg hXdim hYdim⟩

/-- **The projection formula** (the second assertion of Stacks 0FFA, for Noetherian `X` and `Y`).
Let `f : X ⟶ Y` be a proper morphism of schemes over `S`, with `X` and `Y` Noetherian, regular, of
finite dimension and with affine diagonal, so that `f` is a local complete intersection morphism
(Stacks 0E9K), and suppose that the Gysin map of `f` exists. Then

  `f_*(α · f^!β) = f_*α · β`

for the products of Section 0FEX: writing `β = ch(β') ∩ [Y]`, `α · f^!β = ch(f^*β') ∩ α` and the
projection formula gives `f_*(ch(f^*β') ∩ α) = ch(β') ∩ f_*α`. -/
theorem rationalProperChowPushforward_rationalIntersectionProduct_lciGysinRational [IsProper f]
    [IsNoetherian X] [IsNoetherian Y]
    (hXreg : IsRegular X) (hYreg : IsRegular Y) (hXdim : topologicalKrullDim X ≠ ⊤)
    (hYdim : topologicalKrullDim Y ≠ ⊤) (h : GysinMapExists f)
    (α : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j)
    (β : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) :
    rationalProperChowPushforward C sX sY hf
        (rationalIntersectionProduct hXreg (exists_bounds_relativeDimension C sX hXdim) α
          (lciGysinRational C sX sY hf
            (isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg) h β)) =
      rationalIntersectionProduct hYreg (exists_bounds_relativeDimension C sY hYdim)
        (rationalProperChowPushforward C sX sY hf α) β := by
  have : Finite (_root_.ConnectedComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_connectedComponents X
  set hlci := isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg
  have hXb := bddBelow_range_relativeDimension (sX := sX) hXdim
  have hYb := bddBelow_range_relativeDimension (sX := sY) hYdim
  obtain ⟨b, rfl⟩ := (bijective_flip_rationalChernCharacterCap hYreg
    (exists_bounds_relativeDimension C sY hYdim)).2 β
  rw [LinearMap.flip_apply, lciGysinRational_rationalChernCharacterCap C sX sY hf hlci h hXb hYb,
    lciGysinRational_rationalFundamentalClass_of_isRegular C sX sY hf hlci h hXreg hYreg,
    rationalIntersectionProduct_comm hXreg, rationalIntersectionProduct_rationalChernCharacterCap,
    rationalProperChowPushforward_rationalChernCharacterCap C sX sY hf hXb hYb,
    rationalIntersectionProduct_comm hYreg, rationalIntersectionProduct_rationalChernCharacterCap]

/-- **Stacks Project, Tag 0FFA.** Let `(S, δ)` be as in Situation 42.7.1 and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S` such that both `X` and `Y` are quasi-compact,
regular, have affine diagonal, and finite dimension. Then `f` is a local complete intersection
morphism, and if moreover the Gysin map exists for `f` and `f` is proper, then

  `f_*(α · f^!β) = f_*α · β`

for the intersection products of Section 0FEX, on `CH^*(-) ⊗ 𝐐 = CH_*(-) ⊗ 𝐐`. -/
@[stacks 0FFA "the whole lemma: for f : X → Y over S with X, Y quasi-compact, regular, of finite \
dimension, with affine diagonal, f is a local complete intersection morphism, and if the Gysin map \
of f exists and f is proper then f_*(α · f^!β) = f_*α · β for the products of 0FEX on \
CH^*(-) ⊗ Q = CH_*(-) ⊗ Q"]
theorem isLocalCompleteIntersectionMorphism_and_projectionFormula_rationalIntersection
    [CompactSpace X] [CompactSpace Y] (hXreg : IsRegular X) (hYreg : IsRegular Y)
    (hXdim : topologicalKrullDim X ≠ ⊤) (hYdim : topologicalKrullDim Y ≠ ⊤) :
    IsLocalCompleteIntersectionMorphism f ∧
      ∀ [IsProper f] (h : GysinMapExists f)
        (α : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j)
        (β : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j),
        haveI := isNoetherian_of_compactSpace sX
        haveI := isNoetherian_of_compactSpace sY
        rationalProperChowPushforward C sX sY hf
            (rationalIntersectionProduct hXreg (exists_bounds_relativeDimension C sX hXdim) α
              (lciGysinRational C sX sY hf
                (isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg) h
                β)) =
          rationalIntersectionProduct hYreg (exists_bounds_relativeDimension C sY hYdim)
            (rationalProperChowPushforward C sX sY hf α) β :=
  have := isNoetherian_of_compactSpace sX
  have := isNoetherian_of_compactSpace sY
  ⟨isLocalCompleteIntersectionMorphism_of_comp_eq_of_isRegular hf hXreg hYreg, fun h α β =>
    rationalProperChowPushforward_rationalIntersectionProduct_lciGysinRational hf hXreg hYreg hXdim
      hYdim h α β⟩

end Gysin

/-! ### The hypotheses of Stacks 0FEY over a field -/

section Field

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)

/-- **Over a field `δ` is bounded on a Noetherian scheme**: it takes values in `[0, hi]`, being
the dimension of the closure of a point. -/
theorem exists_bounds_relativeDimension_fieldChowSituation [LocallyOfFiniteType sX]
    [IsNoetherian X] :
    ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension (fieldChowSituation k).dimensionFunction sX x ∧
      relativeDimension (fieldChowSituation k).dimensionFunction sX x ≤ hi := by
  obtain ⟨hi, hhi⟩ := exists_relativeDimension_le (fieldChowSituation k) sX
  exact ⟨0, hi, fun x => ⟨relativeDimension_fieldChowSituation_nonneg k sX x, hhi x⟩⟩

end Field

/-! ### Stacks 0FFF -/

section Smooth

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart)

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX]

local notation "CHQ(" s ")" =>
  DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) s j

/-- **The class in `CH_*(X) ⊗ 𝐐` of a class of codimension `i`**, for `X` smooth and quasi-compact
over `k`: `α ∈ CH^i(X) = ∏_d CH_{d-i}(X_d)` goes to `∑_d (i_d)_*(1 ⊗ α_d)`, the sum over the
finitely many nonempty parts `X_d` of dimension `d`. -/
def codimensionToRationalChow [CompactSpace X] (i : ℤ) :
    codimensionChowGroup k sX i →+ CHQ(sX) where
  toFun a := ∑ d ∈ nonemptyDimParts k sX, rationalIncludePart k sX d
    (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase sX d) j)
      ((d : ℤ) - i) ((1 : ℚ) ⊗ₜ[ℤ] a d))
  map_zero' := by
    simp only [Pi.zero_apply, TensorProduct.tmul_zero, map_zero, Finset.sum_const_zero]
  map_add' a b := by
    simp only [Pi.add_apply, TensorProduct.tmul_add, map_add, Finset.sum_add_distrib]

/-- The class of `α ∈ CH^i(X)` in `CH_*(X) ⊗ 𝐐`, unfolded. -/
theorem codimensionToRationalChow_apply [CompactSpace X] (i : ℤ) (a : codimensionChowGroup k sX i) :
    codimensionToRationalChow k sX i a = ∑ d ∈ nonemptyDimParts k sX, rationalIncludePart k sX d
      (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase sX d) j)
        ((d : ℤ) - i) ((1 : ℚ) ⊗ₜ[ℤ] a d)) :=
  rfl

/-- The restriction to a nonempty part `X_d` of the class of `α ∈ CH^i(X)` is `1 ⊗ α_d`, in
degree `d - i`. -/
theorem rationalRestrictPart_codimensionToRationalChow [CompactSpace X] (i : ℤ)
    (a : codimensionChowGroup k sX i) {d : ℕ} (hd : d ∈ nonemptyDimParts k sX) :
    rationalRestrictPart k sX d (codimensionToRationalChow k sX i a) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase sX d) j)
        ((d : ℤ) - i) ((1 : ℚ) ⊗ₜ[ℤ] a d) := by
  rw [codimensionToRationalChow_apply, map_sum, Finset.sum_eq_single_of_mem d hd
    fun d' _ hd' => rationalRestrictPart_rationalIncludePart_of_ne k sX hd' _,
    rationalRestrictPart_rationalIncludePart]

/-- **Restriction to a part carries the product of Section 0FEX to the product of Section 0FC0.**
For `X` smooth and quasi-compact over `k` with affine diagonal and a nonempty part `X_d`,

  `(α · β)|_{X_d} = α|_{X_d} · β|_{X_d}`,

the product on the left being that of Section 0FEX on `X`, the one on the right that of
Section 0FC0 on `X_d` (formed with the Gysin class of the diagonal of `X_d`), tensored with `𝐐`.
Writing `α = ch(α') ∩ [X]`, the left side is `(ch(α') ∩ β)|_{X_d}`, and the identity is Stacks 0FC2
on `X_d`
(`Stacks.Chow.rationalRestrictPart_totalRationalChowCap_eq_canonicalRationalIntersectionProduct`).
-/
theorem rationalRestrictPart_rationalIntersectionProduct [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] {d : ℕ}
    (hd : d ∈ nonemptyDimParts k sX) (x y : CHQ(sX)) :
    rationalRestrictPart k sX d (rationalIntersectionProduct (isRegular_of_smooth_over_field sX)
        (exists_bounds_relativeDimension_fieldChowSituation k sX) x y) =
      canonicalRationalIntersectionProduct k (partBase sX d) d (relativeDimension_partBase sX d)
        (rationalRestrictPart k sX d x) (rationalRestrictPart k sX d y) := by
  obtain ⟨a, rfl⟩ := (bijective_flip_rationalChernCharacterCap (isRegular_of_smooth_over_field sX)
    (exists_bounds_relativeDimension_fieldChowSituation k sX)).2 x
  rw [LinearMap.flip_apply, rationalIntersectionProduct_rationalChernCharacterCap]
  exact rationalRestrictPart_totalRationalChowCap_eq_canonicalRationalIntersectionProduct k sX hd
    _ y

/-- **The product of Section 0FC0 on `CH^*(X)` is the product of Section 0FEX.** For `X` smooth
and quasi-compact over `k` with affine diagonal, `α ∈ CH^i(X)` and `β ∈ CH^j(X)`, the product of
Section 0FEX of their classes in `CH_*(X) ⊗ 𝐐` is the class of their product
`α · β ∈ CH^{i+j}(X)` of Section 0FC0 (`Stacks.Chow.codimensionIntersectionProduct`): both sides
restrict on each nonempty part `X_d` to `α_d · β_d`
(`Stacks.Chow.rationalRestrictPart_rationalIntersectionProduct`). -/
theorem rationalIntersectionProduct_codimensionToRationalChow [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (i j : ℤ)
    (a : codimensionChowGroup k sX i) (b : codimensionChowGroup k sX j) :
    rationalIntersectionProduct (isRegular_of_smooth_over_field sX)
        (exists_bounds_relativeDimension_fieldChowSituation k sX)
        (codimensionToRationalChow k sX i a) (codimensionToRationalChow k sX j b) =
      codimensionToRationalChow k sX (i + j) (codimensionIntersectionProduct k sX i j a b) := by
  refine (sum_rationalIncludePart_rationalRestrictPart k sX _).symm.trans ?_
  rw [codimensionToRationalChow_apply k sX (i + j)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [rationalRestrictPart_rationalIntersectionProduct k sX hd,
    rationalRestrictPart_codimensionToRationalChow k sX i a hd,
    rationalRestrictPart_codimensionToRationalChow k sX j b hd,
    rationalSelfIntersectionProduct_of_tmul, mul_one, codimensionIntersectionProduct_apply]
  congr 1
  exact of_tmul_eq_of_tmul_of_heq _ _ (by ring) 1 (chowGroupDegreeEquiv_heq _ _ _ _).symm

/-- **The product of a dimension class with a codimension class.** For `X` smooth and
quasi-compact over `k` with affine diagonal, `α ∈ CH_n(X)` and `β ∈ CH^j(X)`, the product of
Section 0FEX of `1 ⊗ α` with the class of `β` is `1 ⊗ (α · β)`, with `α · β ∈ CH_{n-j}(X)` the
integral product of Section 0FC0, `Stacks.Chow.dimensionCodimensionIntersectionProduct`. -/
theorem rationalIntersectionProduct_of_one_tmul_codimensionToRationalChow [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (n j : ℤ)
    (a : chowGroup (fieldChowSituation k) sX n) (b : codimensionChowGroup k sX j) :
    rationalIntersectionProduct (isRegular_of_smooth_over_field sX)
        (exists_bounds_relativeDimension_fieldChowSituation k sX)
        (DirectSum.of (fun l : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX l) n (1 ⊗ₜ a))
        (codimensionToRationalChow k sX j b) =
      DirectSum.of (fun l : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX l) (n - j)
        ((1 : ℚ) ⊗ₜ dimensionCodimensionIntersectionProduct k sX n j a b) := by
  refine (sum_rationalIncludePart_rationalRestrictPart k sX _).symm.trans ?_
  conv_rhs => rw [← sum_rationalIncludePart_rationalRestrictPart k sX (DirectSum.of
    (fun l : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX l) (n - j)
      ((1 : ℚ) ⊗ₜ dimensionCodimensionIntersectionProduct k sX n j a b))]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [rationalRestrictPart_rationalIntersectionProduct k sX hd,
    rationalRestrictPart_codimensionToRationalChow k sX j b hd, rationalChowMap_of_tmul,
    rationalChowMap_of_tmul, rationalSelfIntersectionProduct_of_tmul, mul_one,
    chowGroupRestrict_dimensionCodimensionIntersectionProduct]
  congr 1
  exact of_tmul_eq_of_tmul_of_heq _ _ (by ring) 1 (chowGroupDegreeEquiv_heq _ _ _ _).symm

/-- **The product of two dimension classes.** For `X` smooth and quasi-compact over `k` with
affine diagonal, `α ∈ CH_n(X)` and `β ∈ CH_m(X)`, the product of Section 0FEX of `1 ⊗ α` and
`1 ⊗ β` is `1` tensored with the sum over the parts `X_d` of the pushforwards of the integral
products `α|_{X_d} · β|_{X_d} ∈ CH_{n+m-d}(X_d)` of Section 0FC0. -/
theorem rationalIntersectionProduct_of_one_tmul [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (n m : ℤ)
    (α : chowGroup (fieldChowSituation k) sX n) (β : chowGroup (fieldChowSituation k) sX m) :
    rationalIntersectionProduct (isRegular_of_smooth_over_field sX)
        (exists_bounds_relativeDimension_fieldChowSituation k sX)
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) n (1 ⊗ₜ α))
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) m (1 ⊗ₜ β)) =
      ∑ d ∈ nonemptyDimParts k sX,
        haveI := (isClopenDecomposition_dimPart sX).isProper_ι d
        DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) (n + m - d)
          ((1 : ℚ) ⊗ₜ properChowPushforward (fieldChowSituation k) (partBase sX d) sX
            (dimPart sX d).ι rfl (n + m - d) (properPushforwardDescends _ _ _ _ _ _)
            (dimPartIntersectionProduct k sX d n m
              (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl
                n α)
              (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl
                m β))) := by
  refine (sum_rationalIncludePart_rationalRestrictPart k sX _).symm.trans
    (Finset.sum_congr rfl fun d hd => ?_)
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  rw [rationalRestrictPart_rationalIntersectionProduct k sX hd, rationalChowMap_of_tmul,
    rationalChowMap_of_tmul, rationalSelfIntersectionProduct_of_tmul,
    rationalProperChowPushforward_of_tmul, mul_one]

/-! ### The identification `CH^*(X) ⊗ 𝐐 = CH_*(X) ⊗ 𝐐` -/

/-- **The class of `α_d ∈ CH_{d-i}(X_d)`, extended by zero to the other parts**, is
`(i_d)_*(1 ⊗ α_d)`, for `X_d` nonempty. -/
theorem codimensionToRationalChow_single [CompactSpace X] (i : ℤ) {d : ℕ}
    (hd : d ∈ nonemptyDimParts k sX)
    (y : chowGroup (fieldChowSituation k) (partBase sX d) (d - i)) :
    codimensionToRationalChow k sX i
        (Pi.single (M := fun d' : ℕ => chowGroup (fieldChowSituation k) (partBase sX d') (d' - i))
          d y) =
      rationalIncludePart k sX d
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase sX d) j)
          ((d : ℤ) - i) ((1 : ℚ) ⊗ₜ[ℤ] y)) := by
  rw [codimensionToRationalChow_apply, Finset.sum_eq_single_of_mem d hd fun d' _ hd' => by
    rw [Pi.single_eq_of_ne hd', TensorProduct.tmul_zero, map_zero, map_zero], Pi.single_eq_same]

/-- A class of `CH^i(X)` is the sum of its components on the finitely many nonempty parts, the
Chow groups of the empty parts vanishing. -/
theorem sum_single_codimensionChowGroup [CompactSpace X] (i : ℤ)
    (a : codimensionChowGroup k sX i) :
    ∑ d ∈ nonemptyDimParts k sX,
      Pi.single (M := fun d' : ℕ => chowGroup (fieldChowSituation k) (partBase sX d') (d' - i)) d
        (a d) = a := by
  funext d'
  rw [Finset.sum_apply, Finset.sum_pi_single]
  split_ifs with hd'
  · rfl
  · refine (chowGroup_eq_zero _ _ (fun x _ => hd' ?_) (a d')).symm
    exact (mem_nonemptyDimParts k sX).2 ⟨_, x.2⟩

/-- A component placed in codimension `i'` after transport along `d - i = d - i'` is the same
component placed in codimension `i`. -/
theorem directSum_of_single_chowGroupDegreeEquiv {i i' : ℤ} (h : i' = i) (d : ℕ)
    (h' : (d : ℤ) - i = d - i') (y : chowGroup (fieldChowSituation k) (partBase sX d) (d - i)) :
    DirectSum.of (codimensionChowGroup k sX) i'
        (Pi.single (M := fun d' : ℕ => chowGroup (fieldChowSituation k) (partBase sX d') (d' - i'))
          d (chowGroupDegreeEquiv _ _ h' y)) =
      DirectSum.of (codimensionChowGroup k sX) i
        (Pi.single (M := fun d' : ℕ => chowGroup (fieldChowSituation k) (partBase sX d') (d' - i))
          d y) := by
  subst h
  rfl

/-- **The map `CH^*(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`**, `q ⊗ α ↦ q (∑_d (i_d)_*(1 ⊗ α_d))` on
`α ∈ CH^i(X)`, for `X` smooth and quasi-compact over `k`. -/
def codimensionRationalChowMap [CompactSpace X] :
    ℚ ⊗[ℤ] DirectSum ℤ (codimensionChowGroup k sX) →ₗ[ℚ] CHQ(sX) :=
  LinearMap.liftBaseChange ℚ
    (DirectSum.toAddMonoid fun i => codimensionToRationalChow k sX i).toIntLinearMap

/-- The map `CH^*(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐` on `q ⊗ α`, `α ∈ CH^i(X)`. -/
theorem codimensionRationalChowMap_tmul_of [CompactSpace X] (q : ℚ) (i : ℤ)
    (a : codimensionChowGroup k sX i) :
    codimensionRationalChowMap k sX (q ⊗ₜ[ℤ] DirectSum.of (codimensionChowGroup k sX) i a) =
      q • codimensionToRationalChow k sX i a := by
  rw [codimensionRationalChowMap, LinearMap.liftBaseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
    DirectSum.toAddMonoid_of]

/-- The map `CH_*(X_d) ⊗ 𝐐 ⟶ CH^*(X) ⊗ 𝐐` placing `z ∈ CH_m(X_d)` in codimension `d - m`, on the
part `X_d`. -/
def rationalPartToCodimension (d : ℕ) :
    CHQ(partBase sX d) →ₗ[ℚ] ℚ ⊗[ℤ] DirectSum ℤ (codimensionChowGroup k sX) :=
  DirectSum.toModule ℚ ℤ _ fun m =>
    (((DirectSum.of (codimensionChowGroup k sX) ((d : ℤ) - m)).comp
      ((AddMonoidHom.single
          (fun d' : ℕ => chowGroup (fieldChowSituation k) (partBase sX d') (d' - (d - m))) d).comp
        (chowGroupDegreeEquiv _ _ (by ring : m = (d : ℤ) - (d - m))).toAddMonoidHom)).toIntLinearMap
      ).baseChange ℚ

/-- The map `CH_*(X_d) ⊗ 𝐐 ⟶ CH^*(X) ⊗ 𝐐` on `q ⊗ z`, `z ∈ CH_m(X_d)`. -/
theorem rationalPartToCodimension_of_tmul (d : ℕ) (m : ℤ) (q : ℚ)
    (z : chowGroup (fieldChowSituation k) (partBase sX d) m) :
    rationalPartToCodimension k sX d
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase sX d) j) m
          (q ⊗ₜ[ℤ] z)) =
      q ⊗ₜ[ℤ] DirectSum.of (codimensionChowGroup k sX) ((d : ℤ) - m)
        (Pi.single (M := fun d' : ℕ =>
            chowGroup (fieldChowSituation k) (partBase sX d') (d' - (d - m)))
          d (chowGroupDegreeEquiv _ _ (by ring : m = (d : ℤ) - (d - m)) z)) := by
  rw [rationalPartToCodimension, ← DirectSum.lof_eq_of ℚ, DirectSum.toModule_lof,
    LinearMap.baseChange_tmul]
  rfl

/-- On a nonempty part, `CH_*(X_d) ⊗ 𝐐 ⟶ CH^*(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐` is the pushforward. -/
theorem codimensionRationalChowMap_comp_rationalPartToCodimension [CompactSpace X] {d : ℕ}
    (hd : d ∈ nonemptyDimParts k sX) :
    codimensionRationalChowMap k sX ∘ₗ rationalPartToCodimension k sX d =
      rationalIncludePart k sX d := by
  refine rationalChowHomology_linearMap_ext _ _ fun m q z => ?_
  rw [LinearMap.comp_apply, rationalPartToCodimension_of_tmul, codimensionRationalChowMap_tmul_of,
    codimensionToRationalChow_single k sX _ hd,
    of_tmul_eq_of_tmul_of_heq _ _ (by ring : (d : ℤ) - (d - m) = m) 1
      (chowGroupDegreeEquiv_heq _ _ _ _), ← map_smul, ← DirectSum.lof_eq_of ℚ, ← map_smul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, DirectSum.lof_eq_of]

/-- **The identification `CH^*(X) ⊗ 𝐐 = CH_*(X) ⊗ 𝐐`** for `X` smooth and quasi-compact over `k`:
`q ⊗ α ↦ q (∑_d (i_d)_*(1 ⊗ α_d))` on `α ∈ CH^i(X) = ∏_d CH_{d-i}(X_d)`. Its inverse sends
`z ∈ CH_m(X)` to the family of its restrictions `z|_{X_d}`, placed in codimension `d - m`. -/
def codimensionRationalChowEquiv [CompactSpace X] :
    ℚ ⊗[ℤ] DirectSum ℤ (codimensionChowGroup k sX) ≃ₗ[ℚ] CHQ(sX) :=
  LinearEquiv.ofLinearMap (codimensionRationalChowMap k sX)
    (∑ d ∈ nonemptyDimParts k sX, rationalPartToCodimension k sX d ∘ₗ rationalRestrictPart k sX d)
    (by
      refine LinearMap.ext fun y => ?_
      rw [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, LinearMap.id_apply]
      conv_rhs => rw [← sum_rationalIncludePart_rationalRestrictPart k sX y]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [LinearMap.comp_apply, ← LinearMap.comp_apply (codimensionRationalChowMap k sX),
        codimensionRationalChowMap_comp_rationalPartToCodimension k sX hd])
    (by
      refine LinearMap.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add z z' hz hz' => rw [map_add, map_add, hz, hz']
      | tmul q x =>
        induction x using DirectSum.induction_on with
        | zero => simp only [TensorProduct.tmul_zero, map_zero]
        | add x x' hx hx' => rw [TensorProduct.tmul_add, map_add, map_add, hx, hx']
        | of i a =>
          rw [LinearMap.comp_apply, codimensionRationalChowMap_tmul_of, map_smul,
            LinearMap.sum_apply, LinearMap.id_apply]
          have h : ∀ d ∈ nonemptyDimParts k sX,
              (rationalPartToCodimension k sX d ∘ₗ rationalRestrictPart k sX d)
                (codimensionToRationalChow k sX i a) =
              (1 : ℚ) ⊗ₜ[ℤ] DirectSum.of (codimensionChowGroup k sX) i
                (Pi.single (M := fun d' : ℕ =>
                  chowGroup (fieldChowSituation k) (partBase sX d') (d' - i)) d (a d)) :=
            fun d hd => by
              rw [LinearMap.comp_apply, rationalRestrictPart_codimensionToRationalChow k sX i a hd,
                rationalPartToCodimension_of_tmul,
                directSum_of_single_chowGroupDegreeEquiv k sX (by ring) d]
          rw [Finset.sum_congr rfl h, ← TensorProduct.tmul_sum, ← map_sum,
            sum_single_codimensionChowGroup, TensorProduct.smul_tmul', smul_eq_mul, mul_one])

/-- The identification `CH^*(X) ⊗ 𝐐 = CH_*(X) ⊗ 𝐐` on `q ⊗ α`, `α ∈ CH^i(X)`. -/
theorem codimensionRationalChowEquiv_tmul_of [CompactSpace X] (q : ℚ) (i : ℤ)
    (a : codimensionChowGroup k sX i) :
    codimensionRationalChowEquiv k sX (q ⊗ₜ[ℤ] DirectSum.of (codimensionChowGroup k sX) i a) =
      q • codimensionToRationalChow k sX i a :=
  codimensionRationalChowMap_tmul_of k sX q i a

/-- **Stacks Project, Tag 0FFF.** Let `k` be a field and let `X` be a smooth scheme over `k`
which is quasi-compact and has affine diagonal. Then the intersection product of Section 0FC0 on
`CH^*(X)` agrees after tensoring with `𝐐` with the intersection product of Section 0FEX: the
identification `CH^*(X) ⊗ 𝐐 = (⨁_i CH^i(X)) ⊗ 𝐐 ≅ CH_*(X) ⊗ 𝐐`
(`Stacks.Chow.codimensionRationalChowEquiv`) carries the product
`(q ⊗ α) · (q' ⊗ β) = qq' ⊗ α · β` of `CH^*(X) ⊗ 𝐐`, with `α · β ∈ CH^{i+j}(X)` the product of
Section 0FC0 (`Stacks.Chow.codimensionIntersectionProduct`) for `α ∈ CH^i(X)` and `β ∈ CH^j(X)`,
to the product of Section 0FEX. -/
@[stacks 0FFF "the whole lemma: for X smooth over k, quasi-compact, with affine diagonal, the \
identification CH^*(X) ⊗ Q ≅ CH_*(X) ⊗ Q carries the product of 0FC0 tensored with Q, \
(q ⊗ α)(q' ⊗ β) = qq' ⊗ α · β, to the product of 0FEX"]
theorem codimensionRationalChowEquiv_codimensionIntersectionProduct [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (i j : ℤ) (q q' : ℚ)
    (a : codimensionChowGroup k sX i) (b : codimensionChowGroup k sX j) :
    haveI := isNoetherian_of_compactSpace sX
    codimensionRationalChowEquiv k sX ((q * q') ⊗ₜ[ℤ]
        DirectSum.of (codimensionChowGroup k sX) (i + j)
          (codimensionIntersectionProduct k sX i j a b)) =
      rationalIntersectionProduct (isRegular_of_smooth_over_field sX)
        (exists_bounds_relativeDimension_fieldChowSituation k sX)
        (codimensionRationalChowEquiv k sX (q ⊗ₜ[ℤ] DirectSum.of (codimensionChowGroup k sX) i a))
        (codimensionRationalChowEquiv k sX
          (q' ⊗ₜ[ℤ] DirectSum.of (codimensionChowGroup k sX) j b)) := by
  have := isNoetherian_of_compactSpace sX
  rw [codimensionRationalChowEquiv_tmul_of, codimensionRationalChowEquiv_tmul_of,
    codimensionRationalChowEquiv_tmul_of, LinearMap.map_smul₂, map_smul,
    rationalIntersectionProduct_codimensionToRationalChow, mul_smul, smul_comm q q']

end Smooth

end Stacks.Chow

end
