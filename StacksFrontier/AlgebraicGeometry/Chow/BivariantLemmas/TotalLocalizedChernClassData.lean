module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.TotalLocalizedChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernData

/-!
# The total localized Chern class of the data of a localized Chern class

`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.TotalLocalizedChernClass` builds the class
`c⁽ᵖ⁾(Z ⟶ X, E) ∈ A⁽ᵖ⁾(Z ⟶ X)` of Stacks 0FBC for a `Stacks.Chow.LocalizedChernSituation`. The
construction uses nothing of the finiteness condition of a situation, so it is stated here for
the bare data `Stacks.Chow.LocalizedChernData`.

## Main definitions

* `Stacks.Chow.LocalizedChernData.ofLe`, `Stacks.Chow.LocalizedSituation.ofLe` — the same data,
  resp. situation, at a larger cutoff.
* `Stacks.Chow.LocalizedChernData.totalLocalizedChernClass` — the class `c⁽ᵖ⁾(Z ⟶ X, E)`,
  Stacks 0FBC, for the data of a localized Chern class.

## References

* [Stacks Project, Tag 0FBC](https://stacks.math.columbia.edu/tag/0FBC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory StrictlyPerfect

universe u

namespace Stacks.Chow

/-- The data of a localized Chern class read at a larger cutoff. The cutoff enters only through
the rank bound on the restriction of `E` to the complement of the closed subscheme, so data at `p`
are data at every `q ≥ p`, with the same scheme, closed subscheme and perfect object. -/
def LocalizedChernData.ofLe (T : LocalizedChernData.{u}) {q : ℕ} (hq : T.p ≤ q) :
    LocalizedChernData.{u} :=
  { T with
    p := q
    restriction := by
      refine T.restriction.imp_right fun h => ?_
      obtain ⟨M, hM, e⟩ := h
      exact ⟨M, hM.mono hq, e⟩ }

/-- The situation for localized Chern classes read at a larger cutoff: the data
`Stacks.Chow.LocalizedChernData.ofLe`, with the same finiteness condition. -/
def LocalizedSituation.ofLe (T : LocalizedSituation.{u}) {q : ℕ} (hq : T.p ≤ q) :
    LocalizedSituation.{u} :=
  { T.toLocalizedChernData.ofLe hq with finiteness := T.finiteness }

/-- The total localized Chern class

  `c⁽ᵖ⁾(Z ⟶ X, E) = 1 + c₁(E) + … + c_{p-1}(E) + c_p(Z ⟶ X, E) + c_{p+1}(Z ⟶ X, E) + …`

of the data of a localized Chern class: the element of `A⁽ᵖ⁾(Z ⟶ X)` whose component in a
degree `0 ≤ i < p` is the ordinary Chern class `c i` of `E`, whose component in a degree `i ≥ p`
is the localized Chern class `cloc i`, and whose components in the negative degrees vanish. -/
@[stacks 0FBC]
def LocalizedChernData.totalLocalizedChernClass (T : LocalizedChernData.{u})
    (G : GysinSystem T.base)
    (c : (i : {i : ℤ // 0 ≤ i}) →
      BivariantClass T.base G T.a T.a (𝟙 T.X) (Category.id_comp T.a) i.1)
    (cloc : (i : {i : ℤ // (T.p : ℤ) ≤ i}) →
      BivariantClass T.base G (T.i ≫ T.a) T.a T.i rfl i.1) :
    localizedBivariantGrading T.base G (T.i ≫ T.a) T.a T.i rfl T.p :=
  ⟨fun i => if h : 0 ≤ i.1 then c ⟨i.1, h⟩ else 0, cloc⟩

variable (T : LocalizedChernData.{u}) (G : GysinSystem T.base)
  (c : (i : {i : ℤ // 0 ≤ i}) →
    BivariantClass T.base G T.a T.a (𝟙 T.X) (Category.id_comp T.a) i.1)
  (cloc : (i : {i : ℤ // (T.p : ℤ) ≤ i}) →
    BivariantClass T.base G (T.i ≫ T.a) T.a T.i rfl i.1)

/-- In a degree `0 ≤ i < p` the component of `c⁽ᵖ⁾(Z ⟶ X, E)` is the ordinary Chern class
`c_i(E)` of `E`; in degree `0` that is `c₀(E) = 1`. -/
@[stacks 0FBC "the graded pieces in the degrees below the cutoff"]
theorem LocalizedChernData.totalLocalizedChernClass_fst_of_nonneg {i : ℤ} (hi : i < (T.p : ℤ))
    (h0 : 0 ≤ i) :
    (LocalizedChernData.totalLocalizedChernClass T G c cloc).1 ⟨i, hi⟩ = c ⟨i, h0⟩ :=
  dite_eq_left h0

/-- In a negative degree the component of `c⁽ᵖ⁾(Z ⟶ X, E)` vanishes. -/
@[stacks 0FBC "the vanishing of the graded pieces in the negative degrees"]
theorem LocalizedChernData.totalLocalizedChernClass_fst_of_neg {i : ℤ} (hi : i < (T.p : ℤ))
    (h0 : i < 0) :
    (LocalizedChernData.totalLocalizedChernClass T G c cloc).1 ⟨i, hi⟩ = 0 :=
  dite_eq_right (not_le.mpr h0)

/-- In a degree `i ≥ p` the component of `c⁽ᵖ⁾(Z ⟶ X, E)` is the localized Chern class
`c_i(Z ⟶ X, E)`. -/
@[stacks 0FBC "the graded pieces in the degrees from the cutoff onward"]
theorem LocalizedChernData.totalLocalizedChernClass_snd (i : {i : ℤ // (T.p : ℤ) ≤ i}) :
    (LocalizedChernData.totalLocalizedChernClass T G c cloc).2 i = cloc i :=
  rfl

end Stacks.Chow

end
