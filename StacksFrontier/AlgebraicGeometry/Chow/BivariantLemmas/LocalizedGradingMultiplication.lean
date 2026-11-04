module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldSurjective
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Associativity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGrading
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The multiplication on the localized bivariant grading

Let `f : Z ⟶ X` be a closed immersion of schemes locally of finite type over the base of a Chow
situation and let `p, q ≥ 0`. On the graded group

  `A⁽ᵖ⁾(Z ⟶ X) = ∏_{i ≤ p - 1} Aⁱ(X) × ∏_{i ≥ p} Aⁱ(Z ⟶ X)`

of `Stacks.Chow.localizedBivariantGrading` this file defines a multiplication
`A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ʳ⁾(Z ⟶ X)` for every target `r`. It is built from three pairings,

  `Aⁱ(Z ⟶ X) × Aʲ(X) ⟶ Aⁱ⁺ʲ(Z ⟶ X)`,
  `Aⁱ(X) × Aʲ(Z ⟶ X) ⟶ Aⁱ⁺ʲ(Z ⟶ X)`,
  `Aⁱ(Z ⟶ X) × Aʲ(Z ⟶ X) ⟶ Aⁱ⁺ʲ(Z ⟶ X)`,

the first being composition of bivariant classes, the second the restriction `Aⁱ(X) ⟶ Aⁱ(Z)`
followed by composition, and the third `(c, c') ↦ res(c) ∘ c'` for the restriction
`res : Aⁱ(Z ⟶ X) ⟶ Aⁱ(Z)`. The degree `n` component of a product is the sum over
`i ∈ Finset.Icc (min 0 n) (max 0 n)` of the products of the degree `i` and degree `n - i`
components. In the degrees `n < r` the localized factors are first pushed forward to `A^*(X)` and
the product is taken in `A^*(X)`; in the degrees `n ≥ r` the term is the pairing its pair of
degrees calls for, which exists whenever `i ≥ p` or `n - i ≥ q`, and is `0` on the pairs `i < p`,
`n - i < q`.

The pairings and the multiplication take as hypotheses the compatibilities
`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`,
`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward` and
`Stacks.Chow.GysinSystem.IsNaturalUnderProperPushforward` of the Gysin system, and
`Stacks.Chow.ProperPushforwardFlatPullbackBaseChange`. Their `OfInvertible` forms, at the Gysin
system `Stacks.Chow.gysinSystemOfInvertible`, take none.

## Main definitions

* `Stacks.Chow.chowCohomologyComposite`: the multiplication `Aⁱ(X) × Aʲ(X) ⟶ Aⁱ⁺ʲ(X)` of
  `A^*(X)`.
* `Stacks.Chow.localizedGradingPushforward`: the pushforward `Aⁱ(Z ⟶ X) ⟶ Aⁱ(X)` along a closed
  immersion.
* `Stacks.Chow.localizedMulBivariantChow`, `Stacks.Chow.localizedMulChowBivariant`,
  `Stacks.Chow.localizedMulBivariant`: the three pairings.
* `Stacks.Chow.localizedComposeChowCohomology`: the composition
  `Aⁱ(Z) × Aʲ(Z ⟶ X) ⟶ Aⁱ⁺ʲ(Z ⟶ X)`.
* `Stacks.Chow.localizedGradingComponentOnAmbient`: the degree `i` component of an element of
  `A⁽ᵖ⁾(Z ⟶ X)`, pushed into `Aⁱ(X)`.
* `Stacks.Chow.localizedGradingMulAmbientTerm`, `Stacks.Chow.localizedGradingMulLocalizedTerm`:
  the `(i, n - i)` term of the degree `n` component of a product, in the two branches.
* `Stacks.Chow.localizedBivariantGradingMul`: the multiplication
  `A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ʳ⁾(Z ⟶ X)`.
* `Stacks.Chow.localizedBivariantGradingMulMax`,
  `Stacks.Chow.localizedBivariantGradingInternalMul`: the multiplication at the targets
  `r = max(p, q)` and `r = p = q`.
* `Stacks.Chow.LocalizedGrading.IsMul`: a candidate multiplication has the two component formulas.
* `Stacks.Chow.LocalizedGrading.VanishesInNegativeDegrees`: an element of the grading has
  vanishing components in the negative degrees.
* `Stacks.Chow.localizedGradingSingleLow`: the element of `A⁽ᵖ⁾(Z ⟶ X)` with a single nonzero
  component, in a degree below the cutoff.
* `Stacks.Chow.LocalizedGrading.IsAmbientConvolution`: a candidate multiplication is, read in
  `A^*(X)`, the convolution of the components.

## Main results

* `Stacks.Chow.chowCohomologyComposite_assoc`: the multiplication of `A^*(X)` is associative.
* `Stacks.Chow.localizedBivariantGradingMul_fst`, `Stacks.Chow.localizedBivariantGradingMul_snd`:
  the two component formulas.
* `Stacks.Chow.LocalizedGrading.IsMul.eq`,
  `Stacks.Chow.LocalizedGrading.IsMul.eq_localizedBivariantGradingMul`: the component formulas
  determine the multiplication.
* `Stacks.Chow.localizedBivariantGradingMul_add_left`,
  `Stacks.Chow.localizedBivariantGradingMul_add_right`: the multiplication is additive in each
  argument.
* `Stacks.Chow.sum_localizedGradingMulAmbientTerm_eq`,
  `Stacks.Chow.sum_localizedGradingMulLocalizedTerm_eq`: for elements with vanishing negative
  components, the sums may be taken over any finite set of indices containing the range.
* `Stacks.Chow.Icc_min_max_of_nonneg`: in a degree `n ≥ 0` the index range is `Finset.Icc 0 n`.
* `Stacks.Chow.exists_pushforward_eq_chowCohomologyComposite_of_isAmbientConvolution`: a
  multiplication satisfying `Stacks.Chow.LocalizedGrading.IsAmbientConvolution` makes the
  pushforward hit the product of every pair of classes in degrees `0 ≤ i < p`, `0 ≤ j < q` with
  `i + j ≥ r`.

## References

* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- Composing the zero class on the left with any class gives zero. -/
private theorem bivariantComposite_zero_left_eq {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y Z : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {g : Y ⟶ Z} [LocallyOfFiniteType g] {hf : f ≫ sY = sX}
    {hg : g ≫ sZ = sY} {p q : ℤ} {hgys : G.IsNaturalUnderBaseChangeIso}
    {hgysc : G.IsNaturalUnderPullbackCompPushforward} (b : BivariantClass C G sY sZ g hg q) :
    bivariantComposite C G sX sY sZ f g hf hg p q 0 b hgys hgysc = 0 := by
  rw [← bivariantCompositeBilinear_apply, map_zero, AddMonoidHom.zero_apply]

/-- Composing any class on the left with the zero class gives zero. -/
private theorem bivariantComposite_zero_right_eq {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y Z : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {g : Y ⟶ Z} [LocallyOfFiniteType g] {hf : f ≫ sY = sX}
    {hg : g ≫ sZ = sY} {p q : ℤ} {hgys : G.IsNaturalUnderBaseChangeIso}
    {hgysc : G.IsNaturalUnderPullbackCompPushforward} (a : BivariantClass C G sX sY f hf p) :
    bivariantComposite C G sX sY sZ f g hf hg p q a 0 hgys hgysc = 0 := by
  rw [← bivariantCompositeBilinear_apply, map_zero]


/-! ### The multiplication of `A^*(X)` -/

section Ambient

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-- The multiplication `A^i(X) × A^j(X) ⟶ A^{i+j}(X)` of the Chow cohomology of `X`: the
composition `Stacks.Chow.bivariantComposite` of bivariant classes for the identity of `X`, read
through the equality `𝟙 X ≫ 𝟙 X = 𝟙 X`. -/
def chowCohomologyComposite (i j : ℤ) (a : chowCohomologyComponent C G sX i)
    (b : chowCohomologyComponent C G sX j) : chowCohomologyComponent C G sX (i + j) :=
  bivariantClassCongr C G sX sX (Category.comp_id (𝟙 X))
    (comp_comp_structureMorphism_eq (Category.id_comp sX) (Category.id_comp sX))
    (Category.id_comp sX) (i + j)
    (bivariantComposite C G sX sX sX (𝟙 X) (𝟙 X) (Category.id_comp sX) (Category.id_comp sX)
      i j a b hgys hgysc)

/-- The multiplication of `A^*(X)` kills a zero left argument. -/
@[simp]
theorem chowCohomologyComposite_zero_left (i j : ℤ) (b : chowCohomologyComponent C G sX j) :
    chowCohomologyComposite C G sX hgys hgysc i j 0 b = 0 := by
  unfold chowCohomologyComposite
  rw [bivariantComposite_zero_left_eq, map_zero]

/-- The multiplication of `A^*(X)` kills a zero right argument. -/
@[simp]
theorem chowCohomologyComposite_zero_right (i j : ℤ) (a : chowCohomologyComponent C G sX i) :
    chowCohomologyComposite C G sX hgys hgysc i j a 0 = 0 := by
  unfold chowCohomologyComposite
  rw [bivariantComposite_zero_right_eq, map_zero]

/-- The multiplication of `A^*(X)` is additive in its left argument. -/
theorem chowCohomologyComposite_add_left (i j : ℤ) (a a' : chowCohomologyComponent C G sX i)
    (b : chowCohomologyComponent C G sX j) :
    chowCohomologyComposite C G sX hgys hgysc i j (a + a') b =
      chowCohomologyComposite C G sX hgys hgysc i j a b +
        chowCohomologyComposite C G sX hgys hgysc i j a' b := by
  unfold chowCohomologyComposite
  rw [bivariantComposite_add_left, map_add]

/-- The multiplication of `A^*(X)` is additive in its right argument. -/
theorem chowCohomologyComposite_add_right (i j : ℤ) (a : chowCohomologyComponent C G sX i)
    (b b' : chowCohomologyComponent C G sX j) :
    chowCohomologyComposite C G sX hgys hgysc i j a (b + b') =
      chowCohomologyComposite C G sX hgys hgysc i j a b +
        chowCohomologyComposite C G sX hgys hgysc i j a b' := by
  unfold chowCohomologyComposite
  rw [bivariantComposite_add_right, map_add]

/-- **The multiplication of `A^*(X)` is associative.** The degrees `(i + j) + k` and
`i + (j + k)` are the same integer written two ways, whence the heterogeneous equality. -/
theorem chowCohomologyComposite_assoc (i j k : ℤ) (a : chowCohomologyComponent C G sX i)
    (b : chowCohomologyComponent C G sX j) (c : chowCohomologyComponent C G sX k) :
    chowCohomologyComposite C G sX hgys hgysc (i + j) k
        (chowCohomologyComposite C G sX hgys hgysc i j a b) c ≍
      chowCohomologyComposite C G sX hgys hgysc i (j + k) a
        (chowCohomologyComposite C G sX hgys hgysc j k b c) :=
  bivariantComposite_assoc C G sX sX sX sX (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp sX)
    (Category.id_comp sX) (Category.id_comp sX) i j k a b c hgys hgysc

end Ambient

/-! ### The three pairings -/

section Pairings

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (hgysP : G.IsNaturalUnderProperPushforward)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-- The pushforward `f_* : A^i(Z ⟶ X) ⟶ A^i(X)` along a closed immersion `f : Z ⟶ X`: the
bivariant class `Stacks.Chow.bivariantProperPushforward` for `f` and `𝟙 X`. -/
def localizedGradingPushforward (i : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl i) : chowCohomologyComponent C G sX i :=
  bivariantProperPushforward C G (f ≫ sX) sX sX f (𝟙 X) rfl (Category.id_comp sX)
    (properPushforwardDescends C) i
    (bivariantClassCongr C G (f ≫ sX) sX (Category.comp_id f).symm rfl
      (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) i c) hRG hgysP hgysc

/-- `Stacks.Chow.localizedGradingPushforward` satisfies the rule
`Stacks.Chow.IsBivariantProperPushforward`: on every test scheme it caps by `α ↦ f'_*(c ∩ α)`. -/
theorem localizedGradingPushforward_isBivariantProperPushforward (i : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl i) :
    IsBivariantProperPushforward C G (f ≫ sX) sX sX f (𝟙 X) rfl (Category.id_comp sX)
      (properPushforwardDescends C) i
      (bivariantClassCongr C G (f ≫ sX) sX (Category.comp_id f).symm rfl
        (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) i c)
      (localizedGradingPushforward C G sX f hRG hgysP hgysc i c) :=
  isBivariantProperPushforward_bivariantProperPushforward C G (f ≫ sX) sX sX f (𝟙 X) rfl
    (Category.id_comp sX) (properPushforwardDescends C) i
    (bivariantClassCongr C G (f ≫ sX) sX (Category.comp_id f).symm rfl
      (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) i c) hRG hgysP hgysc

/-- The pushforward `Stacks.Chow.localizedGradingPushforward` is additive. -/
theorem localizedGradingPushforward_add (i : ℤ)
    (c c' : BivariantClass C G (f ≫ sX) sX f rfl i) :
    localizedGradingPushforward C G sX f hRG hgysP hgysc i (c + c') =
      localizedGradingPushforward C G sX f hRG hgysP hgysc i c +
        localizedGradingPushforward C G sX f hRG hgysP hgysc i c' := by
  refine eq_of_isBivariantProperPushforward (hpp := properPushforwardDescends C)
    (localizedGradingPushforward_isBivariantProperPushforward C G sX f hRG hgysP hgysc i (c + c'))
    ?_
  rw [map_add]
  exact IsBivariantProperPushforward.add (hpp := properPushforwardDescends C)
    (localizedGradingPushforward_isBivariantProperPushforward C G sX f hRG hgysP hgysc i c)
    (localizedGradingPushforward_isBivariantProperPushforward C G sX f hRG hgysP hgysc i c')

/-- The first of the three pairings: `A^i(Z ⟶ X) × A^j(X) ⟶ A^{i+j}(Z ⟶ X)`, composition of
bivariant classes, read through the equality `f ≫ 𝟙 X = f`. -/
@[stacks 0FA0 "the pairing A^i(Z ⟶ X) × A^j(X) ⟶ A^{i+j}(Z ⟶ X) of the remark, composition of \
bivariant classes"]
def localizedMulBivariantChow (i j : ℤ) (c : BivariantClass C G (f ≫ sX) sX f rfl i)
    (b : chowCohomologyComponent C G sX j) : BivariantClass C G (f ≫ sX) sX f rfl (i + j) :=
  bivariantClassCongr C G (f ≫ sX) sX (Category.comp_id f)
    (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) rfl (i + j)
    (bivariantComposite C G (f ≫ sX) sX sX f (𝟙 X) rfl (Category.id_comp sX) i j c b hgys hgysc)

/-- The first pairing kills a zero class on `X`. -/
@[simp]
theorem localizedMulBivariantChow_zero_right (i j : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl i) :
    localizedMulBivariantChow C G sX f hgys hgysc i j c 0 = 0 := by
  unfold localizedMulBivariantChow
  rw [bivariantComposite_zero_right_eq, map_zero]

/-- The first pairing is additive in its localized argument. -/
theorem localizedMulBivariantChow_add_left (i j : ℤ)
    (c c' : BivariantClass C G (f ≫ sX) sX f rfl i) (b : chowCohomologyComponent C G sX j) :
    localizedMulBivariantChow C G sX f hgys hgysc i j (c + c') b =
      localizedMulBivariantChow C G sX f hgys hgysc i j c b +
        localizedMulBivariantChow C G sX f hgys hgysc i j c' b := by
  unfold localizedMulBivariantChow
  rw [bivariantComposite_add_left, map_add]

/-- The first pairing is additive in its argument on `X`. -/
theorem localizedMulBivariantChow_add_right (i j : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl i) (b b' : chowCohomologyComponent C G sX j) :
    localizedMulBivariantChow C G sX f hgys hgysc i j c (b + b') =
      localizedMulBivariantChow C G sX f hgys hgysc i j c b +
        localizedMulBivariantChow C G sX f hgys hgysc i j c b' := by
  unfold localizedMulBivariantChow
  rw [bivariantComposite_add_right, map_add]

/-- The composition `A^i(Z) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X)` of a Chow cohomology class on `Z` with
a bivariant class for `f`, read through the equality `𝟙 Z ≫ f = f`. -/
def localizedComposeChowCohomology (i j : ℤ) (a : chowCohomologyComponent C G (f ≫ sX) i)
    (c : BivariantClass C G (f ≫ sX) sX f rfl j) :
    BivariantClass C G (f ≫ sX) sX f rfl (i + j) :=
  bivariantClassCongr C G (f ≫ sX) sX (Category.id_comp f)
    (comp_comp_structureMorphism_eq (Category.id_comp (f ≫ sX)) rfl) rfl (i + j)
    (bivariantComposite C G (f ≫ sX) (f ≫ sX) sX (𝟙 Z) f (Category.id_comp (f ≫ sX)) rfl
      i j a c hgys hgysc)

/-- The composition `A^i(Z) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X)` kills a zero class on `Z`. -/
@[simp]
theorem localizedComposeChowCohomology_zero_left (i j : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedComposeChowCohomology C G sX f hgys hgysc i j 0 c = 0 := by
  unfold localizedComposeChowCohomology
  rw [bivariantComposite_zero_left_eq, map_zero]

/-- The composition `A^i(Z) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X)` is additive in its argument on `Z`. -/
theorem localizedComposeChowCohomology_add_left (i j : ℤ)
    (a a' : chowCohomologyComponent C G (f ≫ sX) i)
    (c : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedComposeChowCohomology C G sX f hgys hgysc i j (a + a') c =
      localizedComposeChowCohomology C G sX f hgys hgysc i j a c +
        localizedComposeChowCohomology C G sX f hgys hgysc i j a' c := by
  unfold localizedComposeChowCohomology
  rw [bivariantComposite_add_left, map_add]

/-- The composition `A^i(Z) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X)` is additive in its localized
argument. -/
theorem localizedComposeChowCohomology_add_right (i j : ℤ)
    (a : chowCohomologyComponent C G (f ≫ sX) i)
    (c c' : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedComposeChowCohomology C G sX f hgys hgysc i j a (c + c') =
      localizedComposeChowCohomology C G sX f hgys hgysc i j a c +
        localizedComposeChowCohomology C G sX f hgys hgysc i j a c' := by
  unfold localizedComposeChowCohomology
  rw [bivariantComposite_add_right, map_add]

/-- The second of the three pairings: `A^i(X) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X)`, the restriction
`Stacks.Chow.chowCohomologyRestriction : A^i(X) ⟶ A^i(Z)` followed by the composition
`A^i(Z) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X)`. -/
@[stacks 0FA0 "the pairing A^i(X) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X) of the remark, the restriction \
A^i(X) ⟶ A^i(Z) of Stacks 0F9Z followed by composition"]
def localizedMulChowBivariant (i j : ℤ) (a : chowCohomologyComponent C G sX i)
    (c : BivariantClass C G (f ≫ sX) sX f rfl j) :
    BivariantClass C G (f ≫ sX) sX f rfl (i + j) :=
  localizedComposeChowCohomology C G sX f hgys hgysc i j
    (chowCohomologyRestriction C G sX f i hgys a) c

/-- The second pairing kills a zero class on `X`. -/
@[simp]
theorem localizedMulChowBivariant_zero_left (i j : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulChowBivariant C G sX f hgys hgysc i j 0 c = 0 := by
  unfold localizedMulChowBivariant
  rw [map_zero, localizedComposeChowCohomology_zero_left]

/-- The second pairing is additive in its argument on `X`. -/
theorem localizedMulChowBivariant_add_left (i j : ℤ)
    (a a' : chowCohomologyComponent C G sX i) (c : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulChowBivariant C G sX f hgys hgysc i j (a + a') c =
      localizedMulChowBivariant C G sX f hgys hgysc i j a c +
        localizedMulChowBivariant C G sX f hgys hgysc i j a' c := by
  unfold localizedMulChowBivariant
  rw [map_add, localizedComposeChowCohomology_add_left]

/-- The second pairing is additive in its localized argument. -/
theorem localizedMulChowBivariant_add_right (i j : ℤ)
    (a : chowCohomologyComponent C G sX i) (c c' : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulChowBivariant C G sX f hgys hgysc i j a (c + c') =
      localizedMulChowBivariant C G sX f hgys hgysc i j a c +
        localizedMulChowBivariant C G sX f hgys hgysc i j a c' := by
  unfold localizedMulChowBivariant
  rw [localizedComposeChowCohomology_add_right]

/-- The third of the three pairings: `A^i(Z ⟶ X) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X)`, sending
`(c, c')` to `res(c) ∘ c'` for the restriction
`res = Stacks.Chow.closedImmersionChowCohomologyRestriction : A^i(Z ⟶ X) ⟶ A^i(Z)`. -/
@[stacks 0FA0 "the pairing A^i(Z ⟶ X) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X) of the remark, \
(c, c') ↦ res(c) ∘ c' for the restriction res of Stacks 0F9Z"]
def localizedMulBivariant (i j : ℤ) (c : BivariantClass C G (f ≫ sX) sX f rfl i)
    (c' : BivariantClass C G (f ≫ sX) sX f rfl j) :
    BivariantClass C G (f ≫ sX) sX f rfl (i + j) :=
  localizedComposeChowCohomology C G sX f hgys hgysc i j
    (closedImmersionChowCohomologyRestriction C G (f ≫ sX) sX f rfl i hgys c) c'

/-- The third pairing is additive in its left argument. -/
theorem localizedMulBivariant_add_left (i j : ℤ)
    (c c' : BivariantClass C G (f ≫ sX) sX f rfl i)
    (d : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulBivariant C G sX f hgys hgysc i j (c + c') d =
      localizedMulBivariant C G sX f hgys hgysc i j c d +
        localizedMulBivariant C G sX f hgys hgysc i j c' d := by
  unfold localizedMulBivariant
  rw [map_add, localizedComposeChowCohomology_add_left]

/-- The third pairing is additive in its right argument. -/
theorem localizedMulBivariant_add_right (i j : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl i)
    (d d' : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulBivariant C G sX f hgys hgysc i j c (d + d') =
      localizedMulBivariant C G sX f hgys hgysc i j c d +
        localizedMulBivariant C G sX f hgys hgysc i j c d' := by
  unfold localizedMulBivariant
  rw [localizedComposeChowCohomology_add_right]

end Pairings

/-! ### The multiplication -/

section Mul

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (hgysP : G.IsNaturalUnderProperPushforward)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-- The degree `i` component of an element of `A⁽ᵖ⁾(Z ⟶ X)`, pushed into `A^i(X)`: the component
itself when `i < p`, and its pushforward `Stacks.Chow.localizedGradingPushforward` along `f` when
`i ≥ p`. -/
def localizedGradingComponentOnAmbient (p : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) (i : ℤ) :
    chowCohomologyComponent C G sX i :=
  if hi : (p : ℤ) ≤ i then localizedGradingPushforward C G sX f hRG hgysP hgysc i (a.2 ⟨i, hi⟩)
  else a.1 ⟨i, not_le.1 hi⟩

/-- Below the cutoff the component pushed into `A^*(X)` is the component itself. -/
theorem localizedGradingComponentOnAmbient_of_lt (p : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) (i : ℤ) (hi : i < (p : ℤ)) :
    localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc p a i = a.1 ⟨i, hi⟩ := by
  unfold localizedGradingComponentOnAmbient
  rw [dite_eq_right (not_le.2 hi)]

/-- The `(i, n - i)` term of the degree `n` component of a product in the branch where both
factors are pushed into `A^*(X)`: the product in `A^*(X)` of their components read there. -/
def localizedGradingMulAmbientTerm (p q : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n i : ℤ) :
    chowCohomologyComponent C G sX n :=
  bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) (by ring : i + (n - i) = n)
    (chowCohomologyComposite C G sX hgys hgysc i (n - i)
      (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc p a i)
      (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc q b (n - i)))

/-- The `(i, n - i)` term of the degree `n` component of a product, in a degree `n` whose slot in
the target is the localized group `A^n(Z ⟶ X)`: the pairing applying to the pair of degrees when
`i ≥ p` or `n - i ≥ q`, and `0` when `i < p` and `n - i < q`. -/
def localizedGradingMulLocalizedTerm (p q : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n i : ℤ) :
    BivariantClass C G (f ≫ sX) sX f rfl n :=
  if hi : (p : ℤ) ≤ i then
    if hj : (q : ℤ) ≤ n - i then
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (by ring : i + (n - i) = n)
        (localizedMulBivariant C G sX f hgys hgysc i (n - i) (a.2 ⟨i, hi⟩) (b.2 ⟨n - i, hj⟩))
    else
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (by ring : i + (n - i) = n)
        (localizedMulBivariantChow C G sX f hgys hgysc i (n - i) (a.2 ⟨i, hi⟩)
          (b.1 ⟨n - i, not_le.1 hj⟩))
  else
    if hj : (q : ℤ) ≤ n - i then
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (by ring : i + (n - i) = n)
        (localizedMulChowBivariant C G sX f hgys hgysc i (n - i) (a.1 ⟨i, not_le.1 hi⟩)
          (b.2 ⟨n - i, hj⟩))
    else 0

/-- For `i < p` and `n - i < q` the term `Stacks.Chow.localizedGradingMulLocalizedTerm` is `0`. -/
theorem localizedGradingMulLocalizedTerm_of_lt_of_lt (p q : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n i : ℤ) (hi : i < (p : ℤ))
    (hj : n - i < (q : ℤ)) :
    localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n i = 0 := by
  unfold localizedGradingMulLocalizedTerm
  rw [dite_eq_right (not_le.2 hi), dite_eq_right (not_le.2 hj)]

/-- The multiplication `A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ʳ⁾(Z ⟶ X)` attached to a closed immersion
`f : Z ⟶ X` of schemes locally of finite type over the base, at every `p`, `q` and every target
`r`. Its degree `n` component is the sum over `i ∈ Finset.Icc (min 0 n) (max 0 n)` of the
products of the degree `i` component of the first factor with the degree `n - i` component of the
second: for `n < r` the localized factors are pushed forward to `A^*(X)` and the product is taken
in `A^*(X)` (`Stacks.Chow.localizedGradingMulAmbientTerm`), and for `n ≥ r` the term is the one of
the three pairings `Stacks.Chow.localizedMulBivariantChow`,
`Stacks.Chow.localizedMulChowBivariant`, `Stacks.Chow.localizedMulBivariant` that applies, and
`0` on the pairs `i < p`, `n - i < q` (`Stacks.Chow.localizedGradingMulLocalizedTerm`). -/
@[stacks 0FA0 "the canonical multiplication A^(p)(Z ⟶ X) × A^(q)(Z ⟶ X) ⟶ A^(r)(Z ⟶ X) of the \
remark at every p, q and every target r, assembled degreewise from the three pairings and the \
pushforward of Stacks 0EPK; its associativity, which the source omits, is \
localizedBivariantGradingMul_assoc"]
def localizedBivariantGradingMul (p q r : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) :
    localizedBivariantGrading C G (f ≫ sX) sX f rfl r :=
  (fun n ↦ ∑ i ∈ Finset.Icc (min 0 n.1) (max 0 n.1),
      localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b n.1 i,
    fun n ↦ ∑ i ∈ Finset.Icc (min 0 n.1) (max 0 n.1),
      localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n.1 i)

/-- The multiplication `A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ᵐᵃˣ⁽ᵖ⁼ᑫ⁾⁾(Z ⟶ X)`, for every `p` and `q`:
`Stacks.Chow.localizedBivariantGradingMul` at `r = max(p, q)`. -/
@[stacks 0FA0 "the multiplication A^(p)(Z ⟶ X) × A^(q)(Z ⟶ X) ⟶ A^(max(p,q))(Z ⟶ X) displayed in \
the remark, for every p and q"]
def localizedBivariantGradingMulMax (p q : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) :
    localizedBivariantGrading C G (f ≫ sX) sX f rfl (max p q) :=
  localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q (max p q) a b

/-- The multiplication internal to `A⁽ᵖ⁾(Z ⟶ X)`, for every `p ≥ 0`:
`Stacks.Chow.localizedBivariantGradingMul` at `r = p = q`. -/
@[stacks 0FA0 "the multiplication internal to A^(p)(Z ⟶ X) of the remark's graded algebra, for \
every p ≥ 0; it is graded, and additive in each argument by localizedBivariantGradingMul_add_left \
and _add_right"]
def localizedBivariantGradingInternalMul (p : ℕ)
    (a b : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) :
    localizedBivariantGrading C G (f ≫ sX) sX f rfl p :=
  localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p p p a b

/-! ### The component formulas, and that they pin the multiplication down -/

/-- **The component formula below the cutoff of the target.** For `n < r`, the degree `n`
component of a product is the finite convolution `∑ aᵢ · bₙ₋ᵢ` over
`i ∈ Finset.Icc (min 0 n) (max 0 n)`, taken in `A^*(X)`
(`Stacks.Chow.localizedGradingMulAmbientTerm`). -/
@[simp, stacks 0FA0 "the finite-convolution formula for the degree n part of a product in a \
degree n below the cutoff of the target: the sum over i + j = n of the products of the degree i \
and degree j parts of the factors, pushed into A^*(X) by Stacks 0EPK and multiplied there"]
theorem localizedBivariantGradingMul_fst (p q r : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n : {n : ℤ // n < (r : ℤ)}) :
    (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a b).1 n =
      ∑ i ∈ Finset.Icc (min 0 n.1) (max 0 n.1),
        localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b n.1 i :=
  rfl

/-- **The component formula from the cutoff of the target on.** For `n ≥ r`, the degree `n`
component of a product is the finite convolution `∑ aᵢ · bₙ₋ᵢ` over
`i ∈ Finset.Icc (min 0 n) (max 0 n)`, taken in `A^*(Z ⟶ X)`
(`Stacks.Chow.localizedGradingMulLocalizedTerm`). -/
@[simp, stacks 0FA0 "the finite-convolution formula for the degree n part of a product in a \
degree n at or above the cutoff of the target: the sum over i + j = n of the products of the \
degree i and degree j parts of the factors under the three pairings of the remark"]
theorem localizedBivariantGradingMul_snd (p q r : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n : {n : ℤ // (r : ℤ) ≤ n}) :
    (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a b).2 n =
      ∑ i ∈ Finset.Icc (min 0 n.1) (max 0 n.1),
        localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n.1 i :=
  rfl

/-- A candidate product `M : A⁽ᵖ⁾(Z ⟶ X) → A⁽ᑫ⁾(Z ⟶ X) → A⁽ʳ⁾(Z ⟶ X)` satisfies both component
formulas `Stacks.Chow.localizedBivariantGradingMul_fst` and
`Stacks.Chow.localizedBivariantGradingMul_snd`. -/
def LocalizedGrading.IsMul (p q r : ℕ)
    (M : localizedBivariantGrading C G (f ≫ sX) sX f rfl p →
      localizedBivariantGrading C G (f ≫ sX) sX f rfl q →
      localizedBivariantGrading C G (f ≫ sX) sX f rfl r) : Prop :=
  (∀ a b (n : {n : ℤ // n < (r : ℤ)}), (M a b).1 n =
      ∑ i ∈ Finset.Icc (min 0 n.1) (max 0 n.1),
        localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b n.1 i) ∧
    (∀ a b (n : {n : ℤ // (r : ℤ) ≤ n}), (M a b).2 n =
      ∑ i ∈ Finset.Icc (min 0 n.1) (max 0 n.1),
        localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n.1 i)

/-- `Stacks.Chow.localizedBivariantGradingMul` satisfies `Stacks.Chow.LocalizedGrading.IsMul`. -/
theorem localizedBivariantGradingMul_isMul (p q r : ℕ) :
    LocalizedGrading.IsMul C G sX f hRG hgysP hgys hgysc p q r
      (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r) :=
  ⟨fun a b n ↦ localizedBivariantGradingMul_fst C G sX f hRG hgysP hgys hgysc p q r a b n,
    fun a b n ↦ localizedBivariantGradingMul_snd C G sX f hRG hgysP hgys hgysc p q r a b n⟩

/-- **Uniqueness of the multiplication.** Any two maps satisfying the two component formulas
`Stacks.Chow.LocalizedGrading.IsMul` are equal; nothing else, not even additivity, is assumed of
them. -/
@[stacks 0FA0 "uniqueness of the canonical multiplication: the two finite-convolution formulas \
determine it degreewise, so any two maps satisfying them are equal"]
theorem LocalizedGrading.IsMul.eq {p q r : ℕ}
    {M N : localizedBivariantGrading C G (f ≫ sX) sX f rfl p →
      localizedBivariantGrading C G (f ≫ sX) sX f rfl q →
      localizedBivariantGrading C G (f ≫ sX) sX f rfl r}
    (hM : LocalizedGrading.IsMul C G sX f hRG hgysP hgys hgysc p q r M)
    (hN : LocalizedGrading.IsMul C G sX f hRG hgysP hgys hgysc p q r N) : M = N :=
  funext fun a ↦ funext fun b ↦
    Prod.ext (funext fun n ↦ (hM.1 a b n).trans (hN.1 a b n).symm)
      (funext fun n ↦ (hM.2 a b n).trans (hN.2 a b n).symm)

/-- A map satisfying the two component formulas is `Stacks.Chow.localizedBivariantGradingMul`. -/
theorem LocalizedGrading.IsMul.eq_localizedBivariantGradingMul {p q r : ℕ}
    {M : localizedBivariantGrading C G (f ≫ sX) sX f rfl p →
      localizedBivariantGrading C G (f ≫ sX) sX f rfl q →
      localizedBivariantGrading C G (f ≫ sX) sX f rfl r}
    (hM : LocalizedGrading.IsMul C G sX f hRG hgysP hgys hgysc p q r M) :
    M = localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r :=
  LocalizedGrading.IsMul.eq C G sX f hRG hgysP hgys hgysc hM
    (localizedBivariantGradingMul_isMul C G sX f hRG hgysP hgys hgysc p q r)

/-! ### The index range of the sums -/

/-- For `n ≥ 0`, the index range `Finset.Icc (min 0 n) (max 0 n)` is `Finset.Icc 0 n`. -/
theorem Icc_min_max_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    Finset.Icc (min 0 n) (max 0 n) = Finset.Icc 0 n := by
  rw [min_eq_left hn, max_eq_right hn]

/-- The index `0` lies in `Finset.Icc (min 0 n) (max 0 n)` for every `n`. -/
theorem zero_mem_Icc_min_max (n : ℤ) : (0 : ℤ) ∈ Finset.Icc (min 0 n) (max 0 n) :=
  Finset.mem_Icc.2 ⟨by omega, by omega⟩

/-- The index `n` lies in `Finset.Icc (min 0 n) (max 0 n)` for every `n`. -/
theorem self_mem_Icc_min_max (n : ℤ) : n ∈ Finset.Icc (min 0 n) (max 0 n) :=
  Finset.mem_Icc.2 ⟨by omega, by omega⟩

/-- An index outside `Finset.Icc (min 0 n) (max 0 n)` satisfies `i < 0` or `n < i`. -/
theorem lt_or_lt_of_not_mem_Icc_min_max {n i : ℤ} (h : i ∉ Finset.Icc (min 0 n) (max 0 n)) :
    i < 0 ∨ n < i := by
  rw [Finset.mem_Icc] at h
  omega

/-- An element of `A⁽ᵖ⁾(Z ⟶ X)` whose components in the negative degrees vanish. -/
def LocalizedGrading.VanishesInNegativeDegrees (p : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) : Prop :=
  (∀ i : {i : ℤ // i < (p : ℤ)}, i.1 < 0 → a.1 i = 0) ∧
    (∀ i : {i : ℤ // (p : ℤ) ≤ i}, i.1 < 0 → a.2 i = 0)

variable {C G sX f}

/-- On elements with vanishing negative components the `(i, n - i)` term of the low-degree branch
vanishes whenever `i < 0` or `n < i`. -/
theorem localizedGradingMulAmbientTerm_eq_zero {p q : ℕ}
    {a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p}
    {b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q}
    (ha : LocalizedGrading.VanishesInNegativeDegrees C G sX f p a)
    (hb : LocalizedGrading.VanishesInNegativeDegrees C G sX f q b) (n i : ℤ)
    (hi : i < 0 ∨ n < i) :
    localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b n i = 0 := by
  unfold localizedGradingMulAmbientTerm
  rcases hi with hi | hi
  · have hip : i < (p : ℤ) := by omega
    rw [localizedGradingComponentOnAmbient_of_lt C G sX f hRG hgysP hgysc p a i hip,
      ha.1 ⟨i, hip⟩ hi, chowCohomologyComposite_zero_left, map_zero]
  · have hjneg : n - i < 0 := by omega
    have hjq : n - i < (q : ℤ) := by omega
    rw [localizedGradingComponentOnAmbient_of_lt C G sX f hRG hgysP hgysc q b (n - i) hjq,
      hb.1 ⟨n - i, hjq⟩ hjneg, chowCohomologyComposite_zero_right, map_zero]

/-- On elements with vanishing negative components the `(i, n - i)` term of the high-degree branch
vanishes whenever `i < 0` or `n < i`. -/
theorem localizedGradingMulLocalizedTerm_eq_zero {p q : ℕ}
    {a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p}
    {b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q}
    (ha : LocalizedGrading.VanishesInNegativeDegrees C G sX f p a)
    (hb : LocalizedGrading.VanishesInNegativeDegrees C G sX f q b) (n i : ℤ)
    (hi : i < 0 ∨ n < i) :
    localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n i = 0 := by
  unfold localizedGradingMulLocalizedTerm
  rcases hi with hi | hi
  · have hip : ¬ (p : ℤ) ≤ i := by omega
    rw [dite_eq_right hip]
    by_cases hj : (q : ℤ) ≤ n - i
    · rw [dite_eq_left hj, ha.1 ⟨i, not_le.1 hip⟩ hi, localizedMulChowBivariant_zero_left, map_zero]
    · rw [dite_eq_right hj]
  · have hjneg : n - i < 0 := by omega
    have hjq : ¬ (q : ℤ) ≤ n - i := by omega
    by_cases hip : (p : ℤ) ≤ i
    · rw [dite_eq_left hip, dite_eq_right hjq, hb.1 ⟨n - i, not_le.1 hjq⟩ hjneg,
        localizedMulBivariantChow_zero_right, map_zero]
    · rw [dite_eq_right hip, dite_eq_right hjq]

/-- For elements with vanishing negative components, the sum of the low-degree terms over any
finite set of indices containing `Finset.Icc (min 0 n) (max 0 n)` is the sum over that range. -/
theorem sum_localizedGradingMulAmbientTerm_eq {p q : ℕ}
    {a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p}
    {b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q}
    (ha : LocalizedGrading.VanishesInNegativeDegrees C G sX f p a)
    (hb : LocalizedGrading.VanishesInNegativeDegrees C G sX f q b) (n : ℤ) (s : Finset ℤ)
    (hs : Finset.Icc (min 0 n) (max 0 n) ⊆ s) :
    ∑ i ∈ s, localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b n i =
      ∑ i ∈ Finset.Icc (min 0 n) (max 0 n),
        localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b n i :=
  (Finset.sum_subset hs fun i _ hmem ↦
    localizedGradingMulAmbientTerm_eq_zero hRG hgysP hgys hgysc ha hb n i
      (lt_or_lt_of_not_mem_Icc_min_max hmem)).symm

/-- For elements with vanishing negative components, the sum of the high-degree terms over any
finite set of indices containing `Finset.Icc (min 0 n) (max 0 n)` is the sum over that range. -/
theorem sum_localizedGradingMulLocalizedTerm_eq {p q : ℕ}
    {a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p}
    {b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q}
    (ha : LocalizedGrading.VanishesInNegativeDegrees C G sX f p a)
    (hb : LocalizedGrading.VanishesInNegativeDegrees C G sX f q b) (n : ℤ)
    (s : Finset ℤ) (hs : Finset.Icc (min 0 n) (max 0 n) ⊆ s) :
    ∑ i ∈ s, localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n i =
      ∑ i ∈ Finset.Icc (min 0 n) (max 0 n),
        localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n i :=
  (Finset.sum_subset hs fun i _ hmem ↦
    localizedGradingMulLocalizedTerm_eq_zero hgys hgysc ha hb n i
      (lt_or_lt_of_not_mem_Icc_min_max hmem)).symm

/-! ### Additivity in each argument -/

/-- The degree `i` component pushed into `A^*(X)` is additive. -/
theorem localizedGradingComponentOnAmbient_add (p : ℕ)
    (a b : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) (i : ℤ) :
    localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc p (a + b) i =
      localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc p a i +
        localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc p b i := by
  unfold localizedGradingComponentOnAmbient
  by_cases hi : (p : ℤ) ≤ i
  · rw [dite_eq_left hi, dite_eq_left hi, dite_eq_left hi]
    exact localizedGradingPushforward_add C G sX f hRG hgysP hgysc i _ _
  · rw [dite_eq_right hi, dite_eq_right hi, dite_eq_right hi]
    rfl

/-- The `(i, n - i)` term of the low-degree branch is additive in its first argument. -/
theorem localizedGradingMulAmbientTerm_add_left {p q : ℕ}
    (a a' : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n i : ℤ) :
    localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q (a + a') b n i =
      localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b n i +
        localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a' b n i := by
  unfold localizedGradingMulAmbientTerm
  rw [localizedGradingComponentOnAmbient_add, chowCohomologyComposite_add_left, map_add]

/-- The `(i, n - i)` term of the low-degree branch is additive in its second argument. -/
theorem localizedGradingMulAmbientTerm_add_right {p q : ℕ}
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b b' : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n i : ℤ) :
    localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a (b + b') n i =
      localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b n i +
        localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b' n i := by
  unfold localizedGradingMulAmbientTerm
  rw [localizedGradingComponentOnAmbient_add, chowCohomologyComposite_add_right, map_add]

/-- The `(i, n - i)` term of the high-degree branch is additive in its first argument. -/
theorem localizedGradingMulLocalizedTerm_add_left {p q : ℕ}
    (a a' : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n i : ℤ) :
    localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q (a + a') b n i =
      localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n i +
        localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a' b n i := by
  unfold localizedGradingMulLocalizedTerm
  have h1 : ∀ i : {i : ℤ // i < (p : ℤ)}, (a + a').1 i = a.1 i + a'.1 i := fun _ ↦ rfl
  have h2 : ∀ i : {i : ℤ // (p : ℤ) ≤ i}, (a + a').2 i = a.2 i + a'.2 i := fun _ ↦ rfl
  by_cases hi : (p : ℤ) ≤ i
  · rw [dite_eq_left hi, dite_eq_left hi, dite_eq_left hi]
    by_cases hj : (q : ℤ) ≤ n - i
    · rw [dite_eq_left hj, dite_eq_left hj, dite_eq_left hj, h2,
        localizedMulBivariant_add_left, map_add]
    · rw [dite_eq_right hj, dite_eq_right hj, dite_eq_right hj, h2,
        localizedMulBivariantChow_add_left, map_add]
  · rw [dite_eq_right hi, dite_eq_right hi, dite_eq_right hi]
    by_cases hj : (q : ℤ) ≤ n - i
    · rw [dite_eq_left hj, dite_eq_left hj, dite_eq_left hj, h1,
        localizedMulChowBivariant_add_left, map_add]
    · rw [dite_eq_right hj, dite_eq_right hj, dite_eq_right hj, add_zero]

/-- The `(i, n - i)` term of the high-degree branch is additive in its second argument. -/
theorem localizedGradingMulLocalizedTerm_add_right {p q : ℕ}
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b b' : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n i : ℤ) :
    localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a (b + b') n i =
      localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n i +
        localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b' n i := by
  unfold localizedGradingMulLocalizedTerm
  have h1 : ∀ i : {i : ℤ // i < (q : ℤ)}, (b + b').1 i = b.1 i + b'.1 i := fun _ ↦ rfl
  have h2 : ∀ i : {i : ℤ // (q : ℤ) ≤ i}, (b + b').2 i = b.2 i + b'.2 i := fun _ ↦ rfl
  by_cases hi : (p : ℤ) ≤ i
  · rw [dite_eq_left hi, dite_eq_left hi, dite_eq_left hi]
    by_cases hj : (q : ℤ) ≤ n - i
    · rw [dite_eq_left hj, dite_eq_left hj, dite_eq_left hj, h2,
        localizedMulBivariant_add_right, map_add]
    · rw [dite_eq_right hj, dite_eq_right hj, dite_eq_right hj, h1,
        localizedMulBivariantChow_add_right, map_add]
  · rw [dite_eq_right hi, dite_eq_right hi, dite_eq_right hi]
    by_cases hj : (q : ℤ) ≤ n - i
    · rw [dite_eq_left hj, dite_eq_left hj, dite_eq_left hj, h2,
        localizedMulChowBivariant_add_right, map_add]
    · rw [dite_eq_right hj, dite_eq_right hj, dite_eq_right hj, add_zero]

/-- **The multiplication is additive in its left argument.** -/
theorem localizedBivariantGradingMul_add_left {p q r : ℕ}
    (a a' : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) :
    localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r (a + a') b =
      localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a b +
        localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a' b := by
  refine Prod.ext (funext fun n ↦ ?_) (funext fun n ↦ ?_)
  · exact (Finset.sum_congr (rfl : Finset.Icc (min (0 : ℤ) n.1) (max 0 n.1) =
      Finset.Icc (min 0 n.1) (max 0 n.1)) fun i _ ↦
      localizedGradingMulAmbientTerm_add_left hRG hgysP hgys hgysc a a' b n.1 i).trans
      Finset.sum_add_distrib
  · exact (Finset.sum_congr (rfl : Finset.Icc (min (0 : ℤ) n.1) (max 0 n.1) =
      Finset.Icc (min 0 n.1) (max 0 n.1)) fun i _ ↦
      localizedGradingMulLocalizedTerm_add_left hgys hgysc a a' b n.1 i).trans
      Finset.sum_add_distrib

/-- **The multiplication is additive in its right argument.** -/
theorem localizedBivariantGradingMul_add_right {p q r : ℕ}
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b b' : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) :
    localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a (b + b') =
      localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a b +
        localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a b' := by
  refine Prod.ext (funext fun n ↦ ?_) (funext fun n ↦ ?_)
  · exact (Finset.sum_congr (rfl : Finset.Icc (min (0 : ℤ) n.1) (max 0 n.1) =
      Finset.Icc (min 0 n.1) (max 0 n.1)) fun i _ ↦
      localizedGradingMulAmbientTerm_add_right hRG hgysP hgys hgysc a b b' n.1 i).trans
      Finset.sum_add_distrib
  · exact (Finset.sum_congr (rfl : Finset.Icc (min (0 : ℤ) n.1) (max 0 n.1) =
      Finset.Icc (min 0 n.1) (max 0 n.1)) fun i _ ↦
      localizedGradingMulLocalizedTerm_add_right hgys hgysc a b b' n.1 i).trans
      Finset.sum_add_distrib

/-- The multiplication kills a zero left factor. -/
@[simp]
theorem localizedBivariantGradingMul_zero_left {p q r : ℕ}
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) :
    localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r 0 b = 0 := by
  have h := localizedBivariantGradingMul_add_left (r := r) hRG hgysP hgys hgysc
    (0 : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) 0 b
  rw [zero_add] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

/-- The multiplication kills a zero right factor. -/
@[simp]
theorem localizedBivariantGradingMul_zero_right {p q r : ℕ}
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) :
    localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a
      (0 : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) = 0 := by
  have h := localizedBivariantGradingMul_add_right (q := q) (r := r) hRG hgysP hgys hgysc a 0 0
  rw [zero_add] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

end Mul

/-! ### What agreement with the ambient convolution at every degree would force -/

section Obstruction

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (hgysP : G.IsNaturalUnderProperPushforward)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-- The pushforward `Stacks.Chow.localizedGradingPushforward` kills the zero class. -/
@[simp]
theorem localizedGradingPushforward_zero (i : ℤ) :
    localizedGradingPushforward C G sX f hRG hgysP hgysc i 0 = 0 := by
  have h : localizedGradingPushforward C G sX f hRG hgysP hgysc i 0 +
      localizedGradingPushforward C G sX f hRG hgysP hgysc i 0 =
      localizedGradingPushforward C G sX f hRG hgysP hgysc i 0 + 0 := by
    rw [add_zero, ← localizedGradingPushforward_add, add_zero]
  exact add_left_cancel h

/-- The element of `A⁽ᵖ⁾(Z ⟶ X)` whose degree `i` component is `a ∈ Aⁱ(X)`, for a degree `i`
below the cutoff, and whose every other component is zero. -/
def localizedGradingSingleLow (p : ℕ) (i : {i : ℤ // i < (p : ℤ)})
    (a : chowCohomologyComponent C G sX i.1) :
    localizedBivariantGrading C G (f ≫ sX) sX f rfl p :=
  (Pi.single i a, 0)

/-- At its own degree, the component of `Stacks.Chow.localizedGradingSingleLow` read in `A^*(X)`
is the class it was built from. -/
theorem localizedGradingComponentOnAmbient_singleLow_self (p : ℕ)
    (i : {i : ℤ // i < (p : ℤ)}) (a : chowCohomologyComponent C G sX i.1) :
    localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc p
        (localizedGradingSingleLow C G sX f p i a) i.1 = a := by
  unfold localizedGradingComponentOnAmbient localizedGradingSingleLow
  rw [dite_eq_right (not_le.2 i.2)]
  exact Pi.single_eq_same (M := fun k : {i : ℤ // i < (p : ℤ)} ↦
    chowCohomologyComponent C G sX k.1) i a

/-- In every other degree, the component of `Stacks.Chow.localizedGradingSingleLow` read in
`A^*(X)` vanishes. -/
theorem localizedGradingComponentOnAmbient_singleLow_of_ne (p : ℕ)
    (i : {i : ℤ // i < (p : ℤ)}) (a : chowCohomologyComponent C G sX i.1) (k : ℤ)
    (hk : k ≠ i.1) :
    localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc p
        (localizedGradingSingleLow C G sX f p i a) k = 0 := by
  unfold localizedGradingComponentOnAmbient localizedGradingSingleLow
  by_cases hkp : (p : ℤ) ≤ k
  · rw [dite_eq_left hkp]
    exact localizedGradingPushforward_zero C G sX f hRG hgysP hgysc k
  · rw [dite_eq_right hkp]
    exact Pi.single_eq_of_ne (M := fun k : {i : ℤ // i < (p : ℤ)} ↦
      chowCohomologyComponent C G sX k.1) (fun h ↦ hk (congrArg Subtype.val h)) a

/-- A candidate product `M` is, read in `A^*(X)`, the convolution of the components read in
`A^*(X)`: in every degree `n`, the component of `M a b` pushed into `A^n(X)` by
`Stacks.Chow.localizedGradingComponentOnAmbient` is the sum of the terms
`Stacks.Chow.localizedGradingMulAmbientTerm` over `Finset.Icc (min 0 n) (max 0 n)`. -/
def LocalizedGrading.IsAmbientConvolution (p q r : ℕ)
    (M : localizedBivariantGrading C G (f ≫ sX) sX f rfl p →
      localizedBivariantGrading C G (f ≫ sX) sX f rfl q →
      localizedBivariantGrading C G (f ≫ sX) sX f rfl r) : Prop :=
  ∀ (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n : ℤ),
    localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc r (M a b) n =
      ∑ i ∈ Finset.Icc (min 0 n) (max 0 n),
        localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b n i

/-- Below the cutoff of its target, the component of `Stacks.Chow.localizedBivariantGradingMul`
read in `A^*(X)` is the convolution `Stacks.Chow.LocalizedGrading.IsAmbientConvolution` asks
for. -/
theorem localizedGradingComponentOnAmbient_localizedBivariantGradingMul_of_lt (p q r : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n : ℤ) (hn : n < (r : ℤ)) :
    localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc r
        (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a b) n =
      ∑ i ∈ Finset.Icc (min 0 n) (max 0 n),
        localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b n i :=
  localizedGradingComponentOnAmbient_of_lt C G sX f hRG hgysP hgysc r _ n hn

/-- Let `M : A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ʳ⁾(Z ⟶ X)` be a multiplication satisfying
`Stacks.Chow.LocalizedGrading.IsAmbientConvolution`, and let `i, j = n - i ≥ 0` be degrees with
`i < p` and `j < q` in a total degree `n ≥ r`. Then the product in `A^n(X)` of *any*
`a ∈ Aⁱ(X)` and `b ∈ Aʲ(X)` is the pushforward `Stacks.Chow.localizedGradingPushforward` of a
class in `A^n(Z ⟶ X)`. -/
theorem exists_pushforward_eq_chowCohomologyComposite_of_isAmbientConvolution (p q r : ℕ)
    (M : localizedBivariantGrading C G (f ≫ sX) sX f rfl p →
      localizedBivariantGrading C G (f ≫ sX) sX f rfl q →
      localizedBivariantGrading C G (f ≫ sX) sX f rfl r)
    (hM : LocalizedGrading.IsAmbientConvolution C G sX f hRG hgysP hgys hgysc p q r M)
    (n i : ℤ) (hi : 0 ≤ i) (hip : i < (p : ℤ)) (hj : 0 ≤ n - i) (hjq : n - i < (q : ℤ))
    (hrn : (r : ℤ) ≤ n) (a : chowCohomologyComponent C G sX i)
    (b : chowCohomologyComponent C G sX (n - i)) :
    ∃ u : BivariantClass C G (f ≫ sX) sX f rfl n,
      localizedGradingPushforward C G sX f hRG hgysP hgysc n u =
        bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX)
          (by ring : i + (n - i) = n)
          (chowCohomologyComposite C G sX hgys hgysc i (n - i) a b) := by
  set A := localizedGradingSingleLow C G sX f p ⟨i, hip⟩ a with hA
  set B := localizedGradingSingleLow C G sX f q ⟨n - i, hjq⟩ b with hB
  refine ⟨(M A B).2 ⟨n, hrn⟩, ?_⟩
  have h1 : localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc r (M A B) n =
      localizedGradingPushforward C G sX f hRG hgysP hgysc n ((M A B).2 ⟨n, hrn⟩) := by
    unfold localizedGradingComponentOnAmbient
    rw [dite_eq_left hrn]
  rw [← h1, hM A B n,
    Finset.sum_eq_single_of_mem i (Finset.mem_Icc.2 ⟨by omega, by omega⟩) ?_]
  · unfold localizedGradingMulAmbientTerm
    rw [hA, hB, localizedGradingComponentOnAmbient_singleLow_self C G sX f hRG hgysP hgysc
      p ⟨i, hip⟩ a, localizedGradingComponentOnAmbient_singleLow_self C G sX f hRG hgysP hgysc
      q ⟨n - i, hjq⟩ b]
  · intro k _ hki
    unfold localizedGradingMulAmbientTerm
    rw [hA, localizedGradingComponentOnAmbient_singleLow_of_ne C G sX f hRG hgysP hgysc
      p ⟨i, hip⟩ a k hki, chowCohomologyComposite_zero_left, map_zero]

end Obstruction

/-! ### At the Gysin system of the first Chern class rule -/

section OfInvertible

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (f : Z ⟶ X) [IsClosedImmersion f]

/-- The first pairing `A^i(Z ⟶ X) × A^j(X) ⟶ A^{i+j}(Z ⟶ X)` at the Gysin system
`Stacks.Chow.gysinSystemOfInvertible`, with no hypotheses. -/
@[stacks 0FA0 "the pairing A^i(Z ⟶ X) × A^j(X) ⟶ A^{i+j}(Z ⟶ X) of the remark, at the Gysin \
system of the first Chern class rule, with nothing assumed"]
def localizedMulBivariantChowOfInvertible (i j : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl i)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX j) :
    BivariantClass C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl (i + j) :=
  localizedMulBivariantChow C (gysinSystemOfInvertible C) sX f
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) i j c b

/-- The second pairing `A^i(X) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X)` at the Gysin system
`Stacks.Chow.gysinSystemOfInvertible`, with no hypotheses. -/
@[stacks 0FA0 "the pairing A^i(X) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X) of the remark, at the Gysin \
system of the first Chern class rule, with nothing assumed"]
def localizedMulChowBivariantOfInvertible (i j : ℤ)
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX i)
    (c : BivariantClass C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl j) :
    BivariantClass C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl (i + j) :=
  localizedMulChowBivariant C (gysinSystemOfInvertible C) sX f
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) i j a c

/-- The third pairing `A^i(Z ⟶ X) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X)`, `(c, c') ↦ res(c) ∘ c'`, at the
Gysin system `Stacks.Chow.gysinSystemOfInvertible`, with no hypotheses. -/
@[stacks 0FA0 "the pairing A^i(Z ⟶ X) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X) of the remark, at the Gysin \
system of the first Chern class rule, with nothing assumed"]
def localizedMulBivariantOfInvertible (i j : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl i)
    (c' : BivariantClass C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl j) :
    BivariantClass C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl (i + j) :=
  localizedMulBivariant C (gysinSystemOfInvertible C) sX f
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) i j c c'

/-- The multiplication `A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ʳ⁾(Z ⟶ X)`, at every `p`, `q` and every
target `r`, at the Gysin system `Stacks.Chow.gysinSystemOfInvertible`, with no hypotheses. -/
@[stacks 0FA0 "the canonical multiplication A^(p)(Z ⟶ X) × A^(q)(Z ⟶ X) ⟶ A^(r)(Z ⟶ X) of the \
remark at every p, q and every target r, at the Gysin system of the first Chern class rule, with \
NOTHING ASSUMED: every Gysin compatibility is discharged there and Stacks 02RG on Chow groups, \
which the pushforward of Stacks 0EPK costs, is a theorem of this repository; its associativity, \
which the source omits, is localizedBivariantGradingMulOfInvertible_assoc"]
def localizedBivariantGradingMulOfInvertible (p q r : ℕ)
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl q) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl r :=
  localizedBivariantGradingMul C (gysinSystemOfInvertible C) sX f
    (properPushforwardFlatPullbackBaseChange C)
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) p q r a b

/-- The multiplication `A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ᵐᵃˣ⁽ᵖ⁼ᑫ⁾⁾(Z ⟶ X)`, for every `p` and `q`,
at the Gysin system `Stacks.Chow.gysinSystemOfInvertible`, with no hypotheses. -/
@[stacks 0FA0 "the multiplication A^(p)(Z ⟶ X) × A^(q)(Z ⟶ X) ⟶ A^(max(p,q))(Z ⟶ X) displayed in \
the remark, for every p and q, at the Gysin system of the first Chern class rule with nothing \
assumed"]
def localizedBivariantGradingMulMaxOfInvertible (p q : ℕ)
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl q) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl (max p q) :=
  localizedBivariantGradingMulOfInvertible C sX f p q (max p q) a b

/-- The multiplication internal to `A⁽ᵖ⁾(Z ⟶ X)`, for every `p ≥ 0`, at the Gysin system
`Stacks.Chow.gysinSystemOfInvertible`, with no hypotheses. -/
@[stacks 0FA0 "the multiplication internal to A^(p)(Z ⟶ X) of the remark's graded algebra for \
every p ≥ 0, at the Gysin system of the first Chern class rule with nothing assumed"]
def localizedBivariantGradingInternalMulOfInvertible (p : ℕ)
    (a b : localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p :=
  localizedBivariantGradingMulOfInvertible C sX f p p p a b

end OfInvertible

end Stacks.Chow

end
