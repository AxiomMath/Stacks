module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.NegativeDegree
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGrading
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ClosedCoverProduct

/-!
# The multiplication of the localized grading

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S`. For `p ≥ 0` Stacks 0FA0 puts

  `A⁽ᵖ⁾(Z ⟶ X) = ∏_{i ≤ p - 1} Aⁱ(X) × ∏_{i ≥ p} Aⁱ(Z ⟶ X)`

(`Stacks.Chow.localizedBivariantGrading`) and defines, for `p, q ≥ 0`, a multiplication

  `A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ᵖ⁺ᑫ⁾(Z ⟶ X)`.

Its degree-`n` component is a sum over `i + j = n` of products of the degree-`i` component `aᵢ`
of the first factor with the degree-`j` component `bⱼ` of the second:

* for `n < p + q`, push every factor lying in `A^*(Z ⟶ X)` forward to `A^*(X)` (Stacks 0EPK,
  `Stacks.Chow.properPushforwardChowCohomology`) and multiply in `A^*(X)`;
* for `n ≥ p + q` one has `i ≥ p` or `j ≥ q`, and one of three maps applies: `res(aᵢ) ∘ bⱼ` if
  `i ≥ p` and `j ≥ q` (`Stacks.Chow.supportedMul`), `aᵢ ∘ bⱼ` if `i ≥ p` and `j < q`
  (`Stacks.Chow.supportedRightComp`), and `res(aᵢ) ∘ bⱼ` with `res` the restriction to `Z` of
  Chow cohomology if `i < p` (`Stacks.Chow.ambientSupportedMul`).

## Main definitions

* `Stacks.Chow.localizedGradingPush` — the component of degree `i` of an element of
  `A⁽ᵖ⁾(Z ⟶ X)`, pushed forward to `Aⁱ(X)` when `i ≥ p`.
* `Stacks.Chow.localizedGradingTerm` — the product `aᵢ bⱼ ∈ A^{i+j}(Z ⟶ X)` of the summand
  `(i, j = n - i)` of a component of degree `n ≥ p + q - 1`, and
  `Stacks.Chow.localizedGradingHighTerm`, the same in degrees `n ≥ p + q`.
* `Stacks.Chow.localizedGradingCutoffMul` — the multiplication
  `A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ʳ⁾(Z ⟶ X)` with output cutoff `r ≥ p + q - 1`.
* `Stacks.Chow.localizedGradingMul` — the multiplication of Stacks 0FA0, the cutoff `r = p + q`.

## Main results

* `Stacks.Chow.localizedGradingMul_fst`, `Stacks.Chow.localizedGradingMul_snd`,
  `Stacks.Chow.localizedGradingCutoffMul_fst`, `Stacks.Chow.localizedGradingCutoffMul_snd` — the
  components of a product, as the displayed sums.
* `Stacks.Chow.localizedGradingTerm_of_le_of_le`, `Stacks.Chow.localizedGradingTerm_of_le_of_lt`,
  `Stacks.Chow.localizedGradingTerm_of_lt` and their `HighTerm` forms — the three cases of a
  summand.

## Implementation notes

The source sums over all `i + j = n` with `i, j ∈ ℤ`, and observes that the sums are finite
because the groups of negative degree vanish for a closed immersion: `Aⁱ(Z ⟶ X) = 0` and
`Aⁱ(X) = 0` for `i < 0` (`Stacks.Chow.BivariantClass.eq_zero_of_isClosedImmersion_of_neg` and
`Stacks.Chow.chowCohomologyComponent_eq_zero_of_neg`). Here the sum runs over `0 ≤ i ≤ n`
(`Finset.Icc 0 n`), with `j = n - i`; the omitted summands are exactly those with `i < 0` or
`j < 0`, which are products with a factor of negative degree and hence zero by that vanishing. In
particular the components of negative degree are empty sums.

The summands live in `A^{i + (n - i)}`, and are moved to `Aⁿ` by
`Stacks.Chow.bivariantClassDegreeCongr`.

The closed immersion is `f : Z ⟶ X` with an arbitrary structure morphism `sZ` of `Z` satisfying
`f ≫ sX = sZ`, as in `Stacks.Chow.localizedBivariantGrading`. All classes are taken at the Gysin
system of the first Chern class rule, `Stacks.Chow.gysinSystemOfInvertible`, where composition
of bivariant classes is available.

The recipe makes sense for every output cutoff `r` with `p + q ≤ r + 1`: below `r` the factors are
pushed to `A^*(X)`, and in a degree `n ≥ r` one of `i ≥ p` and `j ≥ q` holds for `i + j = n`. The
source's product is the cutoff `r = p + q`.

## References

* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0FA1](https://stacks.math.columbia.edu/tag/0FA1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hf : f ≫ sX = sZ) {p q : ℕ}

/-- **The pushed component of an element of `A⁽ᵖ⁾(Z ⟶ X)`** in degree `i`, the factor used by the
multiplication of Stacks 0FA0 in the degrees below the cutoff: the component `aᵢ ∈ Aⁱ(X)` itself
when `i < p`, and its pushforward `f_* ∘ aᵢ ∈ Aⁱ(X)` of Stacks 0EPK when `i ≥ p`. -/
def localizedGradingPush
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p) (i : ℤ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX i :=
  if h : i < (p : ℤ) then a.1 ⟨i, h⟩
  else properPushforwardChowCohomology C sX sZ f hf (a.2 ⟨i, not_lt.mp h⟩)

variable {C sZ sX f hf} in
/-- Below the cutoff the pushed component is the component. -/
theorem localizedGradingPush_of_lt
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p) {i : ℤ}
    (h : i < (p : ℤ)) : localizedGradingPush C sZ sX f hf a i = a.1 ⟨i, h⟩ :=
  dif_pos h

variable {C sZ sX f hf} in
/-- From the cutoff on the pushed component is the pushforward `f_* ∘ aᵢ` of the component. -/
theorem localizedGradingPush_of_le
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p) {i : ℤ}
    (h : (p : ℤ) ≤ i) :
    localizedGradingPush C sZ sX f hf a i =
      properPushforwardChowCohomology C sX sZ f hf (a.2 ⟨i, h⟩) :=
  dif_neg (not_lt.mpr h)

/-- **A summand of a component of degree `n ≥ p + q - 1` of a product of Stacks 0FA0.** For
`a ∈ A⁽ᵖ⁾(Z ⟶ X)`, `b ∈ A⁽ᑫ⁾(Z ⟶ X)` and `i ∈ ℤ`, with `j = n - i`, the product
`aᵢ bⱼ ∈ A^{i+j}(Z ⟶ X)` given by the map that applies: `res(aᵢ) ∘ bⱼ` if `i ≥ p` and `j ≥ q`,
`aᵢ ∘ bⱼ` if `i ≥ p` and `j < q`, and `res(aᵢ) ∘ bⱼ` if `i < p`, in which case `j ≥ q` since
`n ≥ p + q - 1`. -/
def localizedGradingTerm
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q) {n : ℤ}
    (hn : ((p + q : ℕ) : ℤ) ≤ n + 1) (i : ℤ) :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf (i + (n - i)) :=
  if hi : (p : ℤ) ≤ i then
    if hj : (q : ℤ) ≤ n - i then supportedMul C sZ sX f hf (a.2 ⟨i, hi⟩) (b.2 ⟨n - i, hj⟩)
    else supportedRightComp C sZ sX f hf (a.2 ⟨i, hi⟩) (b.1 ⟨n - i, not_le.mp hj⟩)
  else ambientSupportedMul C sZ sX f hf (a.1 ⟨i, not_le.mp hi⟩)
    (b.2 ⟨n - i, by push_cast at hn; omega⟩)

/-- **A summand of a component of degree `n ≥ p + q` of the product of Stacks 0FA0**: the
summand `aᵢ bₙ₋ᵢ` of `Stacks.Chow.localizedGradingTerm`, in the degrees from the cutoff `p + q` of
the product `A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ᵖ⁺ᑫ⁾(Z ⟶ X)` on. -/
def localizedGradingHighTerm
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q) {n : ℤ}
    (hn : ((p + q : ℕ) : ℤ) ≤ n) (i : ℤ) :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf (i + (n - i)) :=
  localizedGradingTerm C sZ sX f hf a b (by omega) i

variable {C sZ sX f hf}

/-- The summand `(i, j)` with `i ≥ p` and `j ≥ q` is `res(aᵢ) ∘ bⱼ`. -/
theorem localizedGradingTerm_of_le_of_le
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q) {n : ℤ}
    (hn : ((p + q : ℕ) : ℤ) ≤ n + 1) {i : ℤ} (hi : (p : ℤ) ≤ i) (hj : (q : ℤ) ≤ n - i) :
    localizedGradingTerm C sZ sX f hf a b hn i =
      supportedMul C sZ sX f hf (a.2 ⟨i, hi⟩) (b.2 ⟨n - i, hj⟩) := by
  rw [localizedGradingTerm, dif_pos hi, dif_pos hj]

/-- The summand `(i, j)` with `i ≥ p` and `j < q` is `aᵢ ∘ bⱼ`. -/
theorem localizedGradingTerm_of_le_of_lt
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q) {n : ℤ}
    (hn : ((p + q : ℕ) : ℤ) ≤ n + 1) {i : ℤ} (hi : (p : ℤ) ≤ i) (hj : n - i < (q : ℤ)) :
    localizedGradingTerm C sZ sX f hf a b hn i =
      supportedRightComp C sZ sX f hf (a.2 ⟨i, hi⟩) (b.1 ⟨n - i, hj⟩) := by
  rw [localizedGradingTerm, dif_pos hi, dif_neg (not_le.mpr hj)]

/-- The summand `(i, j)` with `i < p` is `res(aᵢ) ∘ bⱼ`, restricting `aᵢ ∈ Aⁱ(X)` to `Z`. -/
theorem localizedGradingTerm_of_lt
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q) {n : ℤ}
    (hn : ((p + q : ℕ) : ℤ) ≤ n + 1) {i : ℤ} (hi : i < (p : ℤ)) (hj : (q : ℤ) ≤ n - i) :
    localizedGradingTerm C sZ sX f hf a b hn i =
      ambientSupportedMul C sZ sX f hf (a.1 ⟨i, hi⟩) (b.2 ⟨n - i, hj⟩) := by
  rw [localizedGradingTerm, dif_neg (not_le.mpr hi)]

/-- The summand `(i, j)` with `i ≥ p` and `j ≥ q` is `res(aᵢ) ∘ bⱼ`. -/
theorem localizedGradingHighTerm_of_le_of_le
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q) {n : ℤ}
    (hn : ((p + q : ℕ) : ℤ) ≤ n) {i : ℤ} (hi : (p : ℤ) ≤ i) (hj : (q : ℤ) ≤ n - i) :
    localizedGradingHighTerm C sZ sX f hf a b hn i =
      supportedMul C sZ sX f hf (a.2 ⟨i, hi⟩) (b.2 ⟨n - i, hj⟩) :=
  localizedGradingTerm_of_le_of_le a b _ hi hj

/-- The summand `(i, j)` with `i ≥ p` and `j < q` is `aᵢ ∘ bⱼ`. -/
theorem localizedGradingHighTerm_of_le_of_lt
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q) {n : ℤ}
    (hn : ((p + q : ℕ) : ℤ) ≤ n) {i : ℤ} (hi : (p : ℤ) ≤ i) (hj : n - i < (q : ℤ)) :
    localizedGradingHighTerm C sZ sX f hf a b hn i =
      supportedRightComp C sZ sX f hf (a.2 ⟨i, hi⟩) (b.1 ⟨n - i, hj⟩) :=
  localizedGradingTerm_of_le_of_lt a b _ hi hj

/-- The summand `(i, j)` with `i < p` is `res(aᵢ) ∘ bⱼ`, restricting `aᵢ ∈ Aⁱ(X)` to `Z`. -/
theorem localizedGradingHighTerm_of_lt
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q) {n : ℤ}
    (hn : ((p + q : ℕ) : ℤ) ≤ n) {i : ℤ} (hi : i < (p : ℤ)) (hj : (q : ℤ) ≤ n - i) :
    localizedGradingHighTerm C sZ sX f hf a b hn i =
      ambientSupportedMul C sZ sX f hf (a.1 ⟨i, hi⟩) (b.2 ⟨n - i, hj⟩) :=
  localizedGradingTerm_of_lt a b _ hi hj

variable (C sZ sX f hf)

/-- **The multiplication of Stacks 0FA0 with output cutoff `r`**,
`A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ʳ⁾(Z ⟶ X)` for `p + q ≤ r + 1`. The component of degree `n` of the
product of `a` and `b` is the sum over `i + j = n` of:

* for `n < r`, the product in `Aⁿ(X)` of the pushed components
  (`Stacks.Chow.localizedGradingPush`) of degrees `i` and `j`;
* for `n ≥ r`, the product `aᵢ bⱼ ∈ Aⁿ(Z ⟶ X)` of `Stacks.Chow.localizedGradingTerm`; since
  `n ≥ p + q - 1`, one of `i ≥ p` and `j ≥ q` holds.

The source's product is the case `r = p + q` (`Stacks.Chow.localizedGradingMul`).

The sum runs over `0 ≤ i ≤ n`, `j = n - i`. The summands omitted from the source's sum over all
`i + j = n` are those with a factor of negative degree, which vanish since the groups of negative
degree vanish for a closed immersion
(`Stacks.Chow.BivariantClass.eq_zero_of_isClosedImmersion_of_neg`,
`Stacks.Chow.chowCohomologyComponent_eq_zero_of_neg`). -/
def localizedGradingCutoffMul (r : ℕ) (hr : p + q ≤ r + 1)
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf r :=
  (fun n => ∑ i ∈ Finset.Icc 0 n.1,
      bivariantClassDegreeCongr C _ sX sX (𝟙 X) (Category.id_comp sX) (by omega)
        ((localizedGradingPush C sZ sX f hf a i).mulId C sX
          (localizedGradingPush C sZ sX f hf b (n.1 - i))),
    fun n => ∑ i ∈ Finset.Icc 0 n.1,
      bivariantClassDegreeCongr C _ sZ sX f hf (by omega)
        (localizedGradingTerm C sZ sX f hf a b (n := n.1) (by have := n.2; omega) i))

/-- **Stacks 0FA0, the multiplication `A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ᵖ⁺ᑫ⁾(Z ⟶ X)`.** The
component of degree `n` of the product of `a` and `b` is the sum over `i + j = n` of:

* for `n < p + q`, the product in `Aⁿ(X)` of the pushed components
  (`Stacks.Chow.localizedGradingPush`) of degrees `i` and `j`;
* for `n ≥ p + q`, the product `aᵢ bⱼ ∈ Aⁿ(Z ⟶ X)` of `Stacks.Chow.localizedGradingHighTerm`.

This is `Stacks.Chow.localizedGradingCutoffMul` at the cutoff `p + q`. -/
def localizedGradingMul
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf (p + q) :=
  localizedGradingCutoffMul C sZ sX f hf (p + q) (by omega) a b

variable {C sZ sX f hf}

/-- **The components of degree `n < r` of the product with output cutoff `r`**:
`(a b)ₙ = ∑_{0 ≤ i ≤ n} a'ᵢ b'ₙ₋ᵢ` in `Aⁿ(X)`, with `a'ᵢ`, `b'ⱼ` the pushed components. -/
theorem localizedGradingCutoffMul_fst {r : ℕ} (hr : p + q ≤ r + 1)
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q)
    (n : {n : ℤ // n < (r : ℤ)}) :
    (localizedGradingCutoffMul C sZ sX f hf r hr a b).1 n = ∑ i ∈ Finset.Icc 0 n.1,
      bivariantClassDegreeCongr C _ sX sX (𝟙 X) (Category.id_comp sX) (by omega)
        ((localizedGradingPush C sZ sX f hf a i).mulId C sX
          (localizedGradingPush C sZ sX f hf b (n.1 - i))) :=
  rfl

/-- **The components of degree `n ≥ r` of the product with output cutoff `r`**:
`(a b)ₙ = ∑_{0 ≤ i ≤ n} aᵢ bₙ₋ᵢ` in `Aⁿ(Z ⟶ X)`, each summand given by the one of the three
maps of the source that applies (`Stacks.Chow.localizedGradingTerm`). -/
theorem localizedGradingCutoffMul_snd {r : ℕ} (hr : p + q ≤ r + 1)
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q)
    (n : {n : ℤ // (r : ℤ) ≤ n}) :
    (localizedGradingCutoffMul C sZ sX f hf r hr a b).2 n = ∑ i ∈ Finset.Icc 0 n.1,
      bivariantClassDegreeCongr C _ sZ sX f hf (by omega)
        (localizedGradingTerm C sZ sX f hf a b (n := n.1) (by have := n.2; omega) i) :=
  rfl

/-- **The components of degree `n < p + q` of the product of Stacks 0FA0**:
`(a b)ₙ = ∑_{0 ≤ i ≤ n} a'ᵢ b'ₙ₋ᵢ` in `Aⁿ(X)`, with `a'ᵢ`, `b'ⱼ` the pushed components. -/
theorem localizedGradingMul_fst
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q)
    (n : {n : ℤ // n < ((p + q : ℕ) : ℤ)}) :
    (localizedGradingMul C sZ sX f hf a b).1 n = ∑ i ∈ Finset.Icc 0 n.1,
      bivariantClassDegreeCongr C _ sX sX (𝟙 X) (Category.id_comp sX) (by omega)
        ((localizedGradingPush C sZ sX f hf a i).mulId C sX
          (localizedGradingPush C sZ sX f hf b (n.1 - i))) :=
  rfl

/-- **The components of degree `n ≥ p + q` of the product of Stacks 0FA0**:
`(a b)ₙ = ∑_{0 ≤ i ≤ n} aᵢ bₙ₋ᵢ` in `Aⁿ(Z ⟶ X)`, each summand given by the one of the three
maps of the source that applies (`Stacks.Chow.localizedGradingHighTerm`). -/
theorem localizedGradingMul_snd
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX f hf q)
    (n : {n : ℤ // ((p + q : ℕ) : ℤ) ≤ n}) :
    (localizedGradingMul C sZ sX f hf a b).2 n = ∑ i ∈ Finset.Icc 0 n.1,
      bivariantClassDegreeCongr C _ sZ sX f hf (by omega)
        (localizedGradingHighTerm C sZ sX f hf a b n.2 i) :=
  rfl

end Stacks.Chow

end
