module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernSetup
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGrading
public import StacksCore.Tactic.StacksAttribute

/-!
# The total localized Chern class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `Z ⟶ X`, `E` and
`p` be as in the situation for localized Chern classes. The Stacks Project writes

  `c⁽ᵖ⁾(Z ⟶ X, E) = 1 + c₁(E) + … + c_{p-1}(E) + c_p(Z ⟶ X, E) + c_{p+1}(Z ⟶ X, E) + …`

for the element of `A⁽ᵖ⁾(Z ⟶ X)` whose component in a degree `i < p` is the ordinary Chern class
`c_i(E) ∈ Aⁱ(X)` and whose component in a degree `i ≥ p` is the localized Chern class
`c_i(Z ⟶ X, E) ∈ Aⁱ(Z ⟶ X)`. This file defines that element and computes its components.

## Main definitions

* `Stacks.Chow.LocalizedChernSituation.ofLe` — the same situation at a larger cutoff.
* `Stacks.Chow.totalLocalizedChernClass` — the class `c⁽ᵖ⁾(Z ⟶ X, E)`, Stacks 0FBC.

## Main results

* `Stacks.Chow.IsFiniteLocallyFreeOfRankLT.mono` — a rank bound weakens as the bound grows.
* `Stacks.Chow.totalLocalizedChernClass_fst_of_nonneg`,
  `Stacks.Chow.totalLocalizedChernClass_fst_of_neg`,
  `Stacks.Chow.totalLocalizedChernClass_snd` — the graded pieces of `c⁽ᵖ⁾(Z ⟶ X, E)`.

## Implementation notes

The Chern classes of a perfect object, ordinary and localized, are not in this repository, so
they are parameters: `c i` is `c_i(E) ∈ Aⁱ(X)` and `cloc i` is `c_i(Z ⟶ X, E) ∈ Aⁱ(Z ⟶ X)`.
Each family is taken on exactly the degrees where the source defines it — `i ≥ 0` for the
ordinary classes and `i ≥ p` for the localized ones — so the two are indexed by subtypes of `ℤ`
and not by `ℤ`. The leading `1` of the display above is the degree-`0` ordinary Chern class
`c₀(E)`, which is the unit of `A⁰(X)`. The grading of Stacks 0FA0 runs over all of `ℤ`, and in
the negative degrees, where the display has no term, the component is zero; that is the only
choice the construction makes.

That the localized classes are available in every degree `i ≥ p`, and not merely in degree `p`,
is `Stacks.Chow.LocalizedChernSituation.ofLe`: the cutoff enters the situation only through the
rank bound on the restriction of `E` to the complement of the closed subscheme, and a bound of
`< p` is a bound of `< i` for every `i ≥ p`.

At the cutoff `p = 0` the first factor of the grading contributes negative degrees only, so the
class is localized in every degree and its degree-`0` component is `c₀(Z ⟶ X, E)` rather than
the unit of `A⁰(X)`; the definition covers that case with no special provision.

## References

* [Stacks Project, Tag 0FBC](https://stacks.math.columbia.edu/tag/0FBC)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory StrictlyPerfect

universe u

namespace Stacks.Chow

/-- A rank bound on a finite locally free module weakens as the bound grows. -/
theorem IsFiniteLocallyFreeOfRankLT.mono {X : RingedSpace.{u, u}} {M : OXMod.{u, u, u} X}
    {p q : ℕ} (h : IsFiniteLocallyFreeOfRankLT M p) (hpq : p ≤ q) :
    IsFiniteLocallyFreeOfRankLT M q := by
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨U, hxU, r, hr, hMr⟩ := h.2 x
  exact ⟨U, hxU, r, hr.trans_le hpq, hMr⟩

/-- The situation for localized Chern classes read at a larger cutoff. The cutoff enters only
through the rank bound on the restriction of `E` to the complement of the closed subscheme, so a
situation at `p` is a situation at every `q ≥ p`, with the same scheme, closed subscheme and
perfect object. -/
def LocalizedChernSituation.ofLe (T : LocalizedChernSituation.{u}) {q : ℕ} (hq : T.p ≤ q) :
    LocalizedChernSituation.{u} :=
  { T with
    p := q
    restriction := by
      refine T.restriction.imp_right fun h => ?_
      obtain ⟨M, hM, e⟩ := h
      exact ⟨M, hM.mono hq, e⟩ }

variable (T : LocalizedChernSituation.{u}) (G : GysinSystem T.base)
  (c : (i : {i : ℤ // 0 ≤ i}) →
    BivariantClass T.base G T.a T.a (𝟙 T.X) (Category.id_comp T.a) i.1)
  (cloc : (i : {i : ℤ // (T.p : ℤ) ≤ i}) →
    BivariantClass T.base G (T.i ≫ T.a) T.a T.i rfl i.1)

/-- **Stacks 0FBC.** The total localized Chern class

  `c⁽ᵖ⁾(Z ⟶ X, E) = 1 + c₁(E) + … + c_{p-1}(E) + c_p(Z ⟶ X, E) + c_{p+1}(Z ⟶ X, E) + …`

of a situation for localized Chern classes: the element of `A⁽ᵖ⁾(Z ⟶ X)` whose component in a
degree `0 ≤ i < p` is the ordinary Chern class `c i` of `E`, whose component in a degree `i ≥ p`
is the localized Chern class `cloc i`, and whose components in the negative degrees vanish. -/
@[stacks 0FBC]
def totalLocalizedChernClass :
    localizedBivariantGrading T.base G (T.i ≫ T.a) T.a T.i rfl T.p :=
  ⟨fun i => if h : 0 ≤ i.1 then c ⟨i.1, h⟩ else 0, cloc⟩

/-- In a degree `0 ≤ i < p` the component of `c⁽ᵖ⁾(Z ⟶ X, E)` is the ordinary Chern class
`c_i(E)` of `E`; in degree `0` that is `c₀(E) = 1`. -/
@[stacks 0FBC "the graded pieces in the degrees below the cutoff"]
theorem totalLocalizedChernClass_fst_of_nonneg {i : ℤ} (hi : i < (T.p : ℤ)) (h0 : 0 ≤ i) :
    (totalLocalizedChernClass T G c cloc).1 ⟨i, hi⟩ = c ⟨i, h0⟩ :=
  dite_eq_left h0

/-- In a negative degree the component of `c⁽ᵖ⁾(Z ⟶ X, E)` vanishes, the source's display having
no term there. -/
@[stacks 0FBC "the vanishing of the graded pieces in the negative degrees"]
theorem totalLocalizedChernClass_fst_of_neg {i : ℤ} (hi : i < (T.p : ℤ)) (h0 : i < 0) :
    (totalLocalizedChernClass T G c cloc).1 ⟨i, hi⟩ = 0 :=
  dite_eq_right (not_le.mpr h0)

/-- In a degree `i ≥ p` the component of `c⁽ᵖ⁾(Z ⟶ X, E)` is the localized Chern class
`c_i(Z ⟶ X, E)`. -/
@[stacks 0FBC "the graded pieces in the degrees from the cutoff onward"]
theorem totalLocalizedChernClass_snd (i : {i : ℤ // (T.p : ℤ) ≤ i}) :
    (totalLocalizedChernClass T G c cloc).2 i = cloc i :=
  rfl

end Stacks.Chow

end
