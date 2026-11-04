module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PolynomialFormsDecomposition
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange
public import StacksFrontier.LinearAlgebra.ExteriorPower.Prod
public import StacksFrontier.RingTheory.AdicCompletion.Prod
public import StacksFrontier.RingTheory.DividedPowers.Extend

/-!
# The `p`-adically completed divided power polynomial decomposition of differentials

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W` index
a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩` carry the divided power ideal
`IP + P₊` of [Stacks, Tag 07H6].  [Stacks, Tag 07HS] computes the divided power differentials of
`P`:

`Ω¹_{P/A,δ'} = (P ⊗_B Ω¹_{B/A,δ}) ⊕ ⨁_w P · d x_w`,

the isomorphism being pinned down by its values on `d (b)` for `b ∈ B` and on `d x_w`.  This
module takes the `p`-adic completion of that decomposition, which is the form the completed
clause of [Stacks, Lemma 60.19.2, Tag 07LD] works with: writing `D'` for the `p`-adic completion
of `P` and `Ω̂¹_{D'}` for the `p`-adic completion of `Ω¹_{P/A,δ'}`,

`Ω̂¹_{D'} = (P ⊗_B Ω¹_{B/A,δ})^∧ ⊕ (⨁_w P · d x_w)^∧`,

linearly over `D'`.  The completion is taken along `(p) ⊆ P`, which is what makes every term a
module over `D'`, and the decomposition descends because the isomorphism of [Stacks, Tag 07HS] is
`P`-linear.

## What the two summands are

The first summand is the completion of the base change `P ⊗_B Ω¹_{B/A,δ}`, which is the source's
`D' ⊗̂_D Ω̂¹_D`; the second is the completion of the free `P`-module on the symbols `d x_w`, which
is the source's completed direct sum `⨁̂_w D' · d x_w`.  **No identification of the first summand
with the completed tensor product `Crystalline.CompletedTensor` of [Stacks, Tag 07JG] is claimed
here**: that is a further statement, which for an infinite family of variables is not a formality,
and nothing below depends on it.  Likewise the second summand is the completion of `W →₀ P` and
not a direct sum of completions, these agreeing for a finite family of variables but not in
general; stating it as the completion is what keeps the result about the completion rather than
about each finite level.

The splitting of the completion of a product is
`AdicCompletion.prodEquiv`; it is where the two summands come apart, and it needs nothing about
the levels.

## The degree-`n` decomposition

The same argument runs in every degree.  Taking the `n`-th exterior power over `P` of the
decomposition of [Stacks, Tag 07HS], splitting it by the Künneth isomorphism
`exteriorPower.prodEquivDirectSum` of the exterior power of a product, and completing along
`(p) ⊆ P` gives, `D'`-linearly,

`Ω̂ⁿ_{D'} = ⨁_{i + j = n} ((⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})) ⊗_P (⋀ʲ_P (W →₀ P)))^∧`.

The completion may be moved inside the sum because the index set `{(i, j) : ℕ × ℕ // i + j = n}`
is finite — it is the antidiagonal of `n` — so `AdicCompletion.sumEquivOfFintype` applies.  This
is the termwise splitness of the completed de Rham complex of `D'`, read degree by degree.

### `W` is not assumed finite

`W` stays arbitrary, as in the degree-one case above, and this costs nothing: the
`⨁_{i + j = n}` runs over a finite index set whatever `W` is.  A hypothesis `[Finite W]` would buy
only the right to rewrite the `W`-indexed factor as a direct sum of completions.  It would do
nothing for the other factor, whose identification with a completed tensor product `D' ⊗̂_D Ω̂ⁱ_D`
needs `Module.Finite B P` — false already for a single variable, since `B⟨z⟩` is not a finite
`B`-module — together with `IsNoetherianRing B`; those are the hypotheses of
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`, which is the only route to such an
identification available.  Lines 30-38 above already made this choice for the degree-one case.

### What is deliberately not claimed

Four identifications a reader may expect are absent, and the names below are chosen so as not to
suggest them.

1. **The `W`-side factor is not called `Ω̂ʲ_{D'/D}`.**  Nothing in this library proves
   `Ω¹_{P/B,δ} ≅ (W →₀ P)`; there is no divided power differentials object of `P` over `B` here
   at all.  So `completedPolynomialVariableForms` is named for what it is, the completed exterior
   power of the free `P`-module on the symbols `d x_w`, and its identification with relative
   divided power differentials is neither used nor proved.
2. **The coefficient-side factor is not called `Ω̂ⁱ_D ⊗̂_D D'`.**  The genuine `Ω̂ⁱ_D` of this
   library is `Crystalline.completedDividedPowerForms`, which completes along `(p) ⊆ B` an
   exterior power taken over `B`; `completedPolynomialCoefficientForms` completes along `(p) ⊆ P`
   an exterior power taken over `P`.  Three distinct gaps separate them — completion over `B`
   versus over `P`, exterior power over `B` then base changed versus exterior power over `P`, and
   the completion of a tensor product versus the tensor product of completions.  Only the middle
   one is free, and only it is closed: `completedPolynomialCoefficientFormsBaseChangeEquiv`
   identifies this factor with the completion of `P ⊗_B Ωⁱ_{B/A,δ}` by
   `ExteriorAlgebra.exteriorPowerBaseChange`, which needs no flatness and no Noetherian
   hypothesis.  The other two gaps stay open.
3. **Completion of an exterior power, never exterior power of a completion.**  Every `Ω̂` here is
   an `AdicCompletion (⋀ⁱ Ω¹)`, as everywhere else in this chapter, and never
   `⋀ⁱ (AdicCompletion Ω¹)`; those are different statements and no comparison between them is
   asserted.
4. **The `W` direction is never a direct sum of completions.**  A direct sum over `W` of
   completions agrees with the completion of the direct sum only for finite `W`.  The
   `⨁_{i + j = n}` below is over the finite antidiagonal and is harmless, but the `W` direction
   is kept inside a single `AdicCompletion` throughout.

## Main definitions

* `Crystalline.DividedPowerPolynomial.completedPolynomialDifferentials` — `Ω̂¹_{D'}`.
* `Crystalline.DividedPowerPolynomial.completedPolynomialCoefficientDifferentials` — the first
  summand `(P ⊗_B Ω¹_{B/A,δ})^∧`.
* `Crystalline.DividedPowerPolynomial.completedPolynomialVariableDifferentials` — the second
  summand `(W →₀ P)^∧`.
* `Crystalline.DividedPowerPolynomial.completedDividedPowerPolynomialDifferentialsEquiv` —
  **the completed decomposition.**
* `Crystalline.DividedPowerPolynomial.completedPolynomialForms` — `Ω̂ⁿ_{D'}`.
* `Crystalline.DividedPowerPolynomial.completedPolynomialCoefficientForms` — the completion of
  `⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})`.
* `Crystalline.DividedPowerPolynomial.completedPolynomialVariableForms` — the completion of
  `⋀ʲ_P (W →₀ P)`.
* `Crystalline.DividedPowerPolynomial.completedPolynomialBidegreeForms` — the completion of the
  bidegree-`(i, j)` summand, the tensor product over `P` of the two above.
* `Crystalline.DividedPowerPolynomial.completedDividedPowerPolynomialFormsEquiv` —
  **the completed decomposition in degree `n`.**

## Main results

* `..._completedDividedPowerPolynomialDifferentialsEquiv_coefficient` and
  `..._completedDividedPowerPolynomialDifferentialsEquiv_variable`, in the namespace
  `Crystalline.DividedPowerPolynomial` —
  the completed decomposition takes the same values on `d (b)` and on `d x_w` as the uncompleted
  one of [Stacks, Tag 07HS], which is what pins it down: the image of `Ω¹_{P/A,δ'}` is
  `p`-adically dense.
* `..._completedDividedPowerPolynomialFormsEquiv_wedge` — the degree-`n` decomposition carries
  the wedge `d b₁ ∧ ⋯ ∧ d bᵢ ∧ d x_{w₁} ∧ ⋯ ∧ d x_{wⱼ}` of `i` coefficient differentials followed
  by `j` variable differentials into the single summand indexed by `(i, j)`, as the generator
  `(1 ⊗ d b₁) ∧ ⋯ ⊗ (d x_{w₁} ∧ ⋯)`.  Those wedges span, so this pins the degree-`n`
  decomposition down just as the two degree-one lemmas pin that one down.
* `..._completedPolynomialCoefficientFormsBaseChangeEquiv` — the coefficient factor is the
  completion of `P ⊗_B Ωⁱ_{B/A,δ}`; see item 2 of the list above for what this does *not* say.

## References

* [Stacks Project, Tag 07HS](https://stacks.math.columbia.edu/tag/07HS)
* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW

namespace Crystalline

namespace DividedPowerPolynomial

section Completed

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  (p : ℕ)

/-- **The `p`-adic completion `D'` of `P = B⟨x_w : w ∈ W⟩`.** -/
public abbrev completedDividedPowerPolynomialRing : Type (max uB uW) :=
  AdicCompletion (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
    (setIndexedDividedPowerPolynomialAlgebra B W)

/-- **`Ω̂¹_{D'}`**, the `p`-adic completion of the divided power differentials `Ω¹_{P/A,δ'}` of
`P = B⟨x_w : w ∈ W⟩`.  The completion is along `(p) ⊆ P`, which is what makes it a module over
`D'`. -/
public abbrev completedPolynomialDifferentials : Type (max uB uW) :=
  AdicCompletion (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
    (dividedPowerDifferentials (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W))

/-- The first summand of the completed decomposition: the `p`-adic completion of the base change
`P ⊗_B Ω¹_{B/A,δ}`, which is the `D' ⊗̂_D Ω̂¹_D` of [Stacks, Tag 07LD]. -/
public abbrev completedPolynomialCoefficientDifferentials : Type (max uB uW) :=
  AdicCompletion (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
    (setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
      dividedPowerDifferentials (A := A) B.dividedPowers)

/-- The second summand of the completed decomposition: the `p`-adic completion of the free
`P`-module `⨁_w P · d x_w` on the differentials of the variables, which is the completed direct
sum `⨁̂_w D' · d x_w` of [Stacks, Tag 07LD]. -/
public abbrev completedPolynomialVariableDifferentials : Type (max uB uW) :=
  AdicCompletion (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
    (W →₀ setIndexedDividedPowerPolynomialAlgebra B W)

/-- **The `p`-adically completed divided power polynomial decomposition of differentials:**

`Ω̂¹_{D'} ≅ (P ⊗_B Ω¹_{B/A,δ})^∧ ⊕ (⨁_w P · d x_w)^∧`,

linearly over `D'`.  It is the completion of the decomposition of [Stacks, Tag 07HS], which is
`P`-linear and therefore descends to the completion along `(p) ⊆ P`, followed by the splitting
`AdicCompletion.prodEquiv` of the completion of a product. -/
public def completedDividedPowerPolynomialDifferentialsEquiv :
    completedPolynomialDifferentials A B W p ≃ₗ[completedDividedPowerPolynomialRing B W p]
      completedPolynomialCoefficientDifferentials A B W p ×
        completedPolynomialVariableDifferentials B W p :=
  (AdicCompletion.congr (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
      (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).1).trans
    (AdicCompletion.prodEquiv _ _ _)

/-- The completed decomposition on an element coming from the uncompleted differentials is the
completion of the uncompleted decomposition, componentwise. -/
private theorem completedDividedPowerPolynomialDifferentialsEquiv_of
    (x : dividedPowerDifferentials (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W)) :
    completedDividedPowerPolynomialDifferentialsEquiv A B W p (AdicCompletion.of _ _ x) =
      (AdicCompletion.of _ _ ((dividedPowerDifferentialsDividedPowerPolynomialEquiv
          (A := A) B W).1 x).1,
        AdicCompletion.of _ _ ((dividedPowerDifferentialsDividedPowerPolynomialEquiv
          (A := A) B W).1 x).2) := by
  change AdicCompletion.prodEquiv _ _ _ (AdicCompletion.congr _
      (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).1
      (AdicCompletion.of _ _ _)) = _
  rw [show AdicCompletion.congr _
      (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).1
      (AdicCompletion.of _ _ x) = AdicCompletion.of _ _ _ from AdicCompletion.map_of _ _ _,
    AdicCompletion.prodEquiv_of]
  rfl

/-- **The completed decomposition on the differential of a coefficient**: `d (b)` goes to
`1 ⊗ d b` in the first summand, exactly as in [Stacks, Tag 07HS]. -/
public theorem completedDividedPowerPolynomialDifferentialsEquiv_coefficient (b : B) :
    completedDividedPowerPolynomialDifferentialsEquiv A B W p
        (AdicCompletion.of _ _ (dividedPowerDifferential (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W)
          (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b))) =
      (AdicCompletion.of _ _ ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[B]
        dividedPowerDifferential (A := A) B.dividedPowers b), 0) := by
  rw [completedDividedPowerPolynomialDifferentialsEquiv_of,
    (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).2.1 b]
  exact Prod.ext rfl (map_zero _)

/-- **The completed decomposition on the differential of a variable**: `d x_w` goes to the
standard generator of the second summand, exactly as in [Stacks, Tag 07HS]. -/
public theorem completedDividedPowerPolynomialDifferentialsEquiv_variable (w : W) :
    completedDividedPowerPolynomialDifferentialsEquiv A B W p
        (AdicCompletion.of _ _ (dividedPowerDifferential (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W)
          (dividedPowerPolynomialVariable (B : Type uB) w))) =
      (0, AdicCompletion.of _ _ (Finsupp.single w
        (1 : setIndexedDividedPowerPolynomialAlgebra B W))) := by
  rw [completedDividedPowerPolynomialDifferentialsEquiv_of,
    (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).2.2 w]
  exact Prod.ext (map_zero _) rfl

/-! ### The degree-`n` decomposition -/

/-- The index set `{(i, j) : ℕ × ℕ // i + j = n}` of the degree-`n` decomposition is finite — it
is the antidiagonal of `n` — whatever the family `W` of variables is.  This is what lets the
completion be moved inside the direct sum below at no cost in hypotheses.  The instance is
produced here because `AdicCompletion.sumEquivOfFintype` asks for a `Fintype` and Mathlib carries
the antidiagonal only as a `Finset`; the injection into `Fin (n + 1)` is the first coordinate,
which determines the second. -/
public instance fintypeNatAntidiagonalSubtype (n : ℕ) :
    Fintype {ij : ℕ × ℕ // ij.1 + ij.2 = n} :=
  Fintype.ofInjective (fun ij ↦ (⟨ij.1.1, Nat.lt_succ_of_le (Nat.le.intro ij.2)⟩ : Fin (n + 1)))
    fun x y h ↦ by
      have hx := x.2
      have hy := y.2
      have h1 : x.1.1 = y.1.1 := congrArg Fin.val h
      exact Subtype.ext (Prod.ext h1 (by omega))

/-- Pulling a completed element of one summand of a finite direct sum back through
`AdicCompletion.sumEquivOfFintype`: the completion of `lof k x` is `lof k` of the completion.
A `private` arithmetic step for the pinning lemma below. -/
private theorem sumEquivOfFintype_symm_of_lof {R : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (M : ι → Type*) [∀ k, AddCommGroup (M k)]
    [∀ k, Module R (M k)] (k : ι) (x : M k) :
    (AdicCompletion.sumEquivOfFintype I M).symm
        (AdicCompletion.of I (DirectSum ι M) (DirectSum.lof R ι M k x)) =
      DirectSum.lof (AdicCompletion I R) ι (fun l ↦ AdicCompletion I (M l)) k
        (AdicCompletion.of I (M k) x) := by
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  rw [AdicCompletion.sumEquivOfFintype_apply, AdicCompletion.sum_lof, AdicCompletion.map_of]

/-- **`Ω̂ⁿ_{D'}`**, the `p`-adic completion of the degree-`n` divided power differential forms
`Ωⁿ_{P/A,δ'} = ⋀ⁿ_P Ω¹_{P/A,δ'}` of `P = B⟨x_w : w ∈ W⟩`.  The completion is along `(p) ⊆ P`,
which is what makes it a module over `D'`.  It is the completion of an exterior power, not the
exterior power of a completion; no comparison with the latter is claimed. -/
public abbrev completedPolynomialForms (n : ℕ) : Type (max uB uW) :=
  AdicCompletion (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
    (dividedPowerDifferentialForms (A := A)
      (setIndexedDividedPowerPolynomialDividedPowers B W) n)

/-- The coefficient factor in bidegree `i`: the `p`-adic completion of `⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})`.

The name says what the object is and nothing more.  It is **not** `Ω̂ⁱ_D ⊗̂_D D'`: the `Ω̂ⁱ_D` of
this library, `Crystalline.completedDividedPowerForms`, completes along `(p) ⊆ B` an exterior
power taken over `B`, whereas this completes along `(p) ⊆ P` an exterior power taken over `P`,
and a tensor product of completions is not the completion of a tensor product.  The one gap that
is free to close — exterior power over `P` of a base change versus base change of an exterior
power over `B` — is closed by `completedPolynomialCoefficientFormsBaseChangeEquiv`. -/
public abbrev completedPolynomialCoefficientForms (i : ℕ) : Type (max uB uW) :=
  AdicCompletion (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
    (⋀[setIndexedDividedPowerPolynomialAlgebra B W]^i
      (setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
        dividedPowerDifferentials (A := A) B.dividedPowers))

/-- The variable factor in bidegree `j`: the `p`-adic completion of `⋀ʲ_P (W →₀ P)`, the
`j`-th exterior power of the free `P`-module on the symbols `d x_w`.

This is **not** called `Ω̂ʲ_{D'/D}`, and is not claimed to be it: the library contains no proof
that `Ω¹_{P/B,δ} ≅ (W →₀ P)`, indeed no divided power differentials of `P` over `B` at all.  It
is also an `AdicCompletion` of a module built from `W →₀ P`, never a direct sum over `W` of
completions, those two agreeing only for a finite family of variables. -/
public abbrev completedPolynomialVariableForms (j : ℕ) : Type (max uB uW) :=
  AdicCompletion (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
    (⋀[setIndexedDividedPowerPolynomialAlgebra B W]^j
      (W →₀ setIndexedDividedPowerPolynomialAlgebra B W))

/-- The bidegree-`(i, j)` summand of the degree-`n` decomposition: the `p`-adic completion of
`(⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})) ⊗_P (⋀ʲ_P (W →₀ P))`.

The tensor product is taken *before* completing, which is the whole point: the completion of a
tensor product is what the Künneth splitting of the exterior power produces, and identifying it
with a completed tensor product of the two completed factors is a separate statement that is not
made here. -/
public abbrev completedPolynomialBidegreeForms (i j : ℕ) : Type (max uB uW) :=
  AdicCompletion (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
    (TensorProduct (setIndexedDividedPowerPolynomialAlgebra B W)
      (⋀[setIndexedDividedPowerPolynomialAlgebra B W]^i
        (setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
          dividedPowerDifferentials (A := A) B.dividedPowers))
      (⋀[setIndexedDividedPowerPolynomialAlgebra B W]^j
        (W →₀ setIndexedDividedPowerPolynomialAlgebra B W)))

/-- **The coefficient factor is the completion of `P ⊗_B Ωⁱ_{B/A,δ}`.**  The exterior power may
be taken over `B` and then base changed, instead of over `P` after base changing, by
`ExteriorAlgebra.exteriorPowerBaseChange`, which is a base-change statement for the universal
property of alternating maps and needs neither flatness nor a Noetherian hypothesis.

This is the only one of the three gaps between `completedPolynomialCoefficientForms` and
`Ω̂ⁱ_D ⊗̂_D D'` that costs nothing.  The other two — completing along `(p) ⊆ P` rather than along
`(p) ⊆ B`, and the completion of a tensor product rather than a tensor product of completions —
remain open, and nothing below pretends otherwise. -/
public def completedPolynomialCoefficientFormsBaseChangeEquiv (i : ℕ) :
    AdicCompletion (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
        (setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
          dividedPowerDifferentialForms (A := A) B.dividedPowers i) ≃ₗ[
      completedDividedPowerPolynomialRing B W p]
      completedPolynomialCoefficientForms A B W p i :=
  AdicCompletion.congr _
    (ExteriorAlgebra.exteriorPowerBaseChange (B : Type uB)
      (setIndexedDividedPowerPolynomialAlgebra B W)
      (dividedPowerDifferentials (A := A) B.dividedPowers) i)

/-- **The `p`-adically completed divided power polynomial decomposition of differential forms in
degree `n`:**

`Ω̂ⁿ_{D'} ≅ ⨁_{i + j = n} ((⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})) ⊗_P (⋀ʲ_P (W →₀ P)))^∧`,

linearly over `D'`.  It is the `n`-th exterior power of the decomposition of [Stacks, Tag 07HS],
split by the Künneth isomorphism `exteriorPower.prodEquivDirectSum` and completed along
`(p) ⊆ P`; the completion passes inside the sum because the index set is the antidiagonal of `n`
and so is finite, which is why no hypothesis on `W` appears.  For `n = 1` this is
`completedDividedPowerPolynomialDifferentialsEquiv` up to the degree-zero and degree-one
identifications `⋀⁰ M ≅ P`, `⋀¹ M ≅ M`, which are not asserted here. -/
public def completedDividedPowerPolynomialFormsEquiv (n : ℕ) :
    completedPolynomialForms A B W p n ≃ₗ[completedDividedPowerPolynomialRing B W p]
      DirectSum {ij : ℕ × ℕ // ij.1 + ij.2 = n}
        (fun ij ↦ completedPolynomialBidegreeForms A B W p ij.1.1 ij.1.2) :=
  (AdicCompletion.congr (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
      (exteriorPowerCongr n
            (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).1 ≪≫ₗ
          exteriorPower.prodEquivDirectSum n)).trans
    (AdicCompletion.sumEquivOfFintype _ _).symm

/-- The degree-`n` decomposition on an element coming from the uncompleted forms: it is the
uncompleted Künneth splitting, followed by the canonical map into the completed direct sum.  The
image of `Ωⁿ_{P/A,δ'}` is `p`-adically dense, so this and `D'`-linearity determine the
equivalence. -/
public theorem completedDividedPowerPolynomialFormsEquiv_of (n : ℕ)
    (x : dividedPowerDifferentialForms (A := A)
      (setIndexedDividedPowerPolynomialDividedPowers B W) n) :
    completedDividedPowerPolynomialFormsEquiv A B W p n (AdicCompletion.of _ _ x) =
      (AdicCompletion.sumEquivOfFintype _ _).symm (AdicCompletion.of _ _
        (exteriorPower.prodEquivDirectSum n
          (exteriorPowerCongr n
            (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).1 x))) :=
  rfl

/-- **The degree-`n` decomposition on a split wedge.**  The wedge of the differentials of `i`
coefficients `b₁, …, bᵢ ∈ B` followed by the differentials of `j` variables
`x_{w₁}, …, x_{wⱼ}` lands in the single summand indexed by `(i, j)`, as the generator
`((1 ⊗ d b₁) ∧ ⋯ ∧ (1 ⊗ d bᵢ)) ⊗ (d x_{w₁} ∧ ⋯ ∧ d x_{wⱼ})`.

This is the degree-`n` counterpart of the two pinning lemmas of the degree-one decomposition, and
it pins the equivalence down for the same reason: such wedges span `Ωⁿ_{P/A,δ'}` over `P` because
the `d` of coefficients and of variables span `Ω¹_{P/A,δ'}`, and the image of `Ωⁿ_{P/A,δ'}` is
`p`-adically dense in the completion.  The spanning statement itself is not needed below and is
not proved here. -/
public theorem completedDividedPowerPolynomialFormsEquiv_wedge (i j : ℕ) (b : Fin i → B)
    (w : Fin j → W) :
    completedDividedPowerPolynomialFormsEquiv A B W p (i + j)
        (AdicCompletion.of _ _ (exteriorPower.ιMulti
          (setIndexedDividedPowerPolynomialAlgebra B W) (i + j)
          (Fin.append
            (fun k ↦ dividedPowerDifferential (A := A)
              (setIndexedDividedPowerPolynomialDividedPowers B W)
              (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) (b k)))
            fun k ↦ dividedPowerDifferential (A := A)
              (setIndexedDividedPowerPolynomialDividedPowers B W)
              (dividedPowerPolynomialVariable (B : Type uB) (w k))))) =
      DirectSum.lof (completedDividedPowerPolynomialRing B W p)
        {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
        (fun ij ↦ completedPolynomialBidegreeForms A B W p ij.1.1 ij.1.2) ⟨(i, j), rfl⟩
        (AdicCompletion.of _ _
          (exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) i
              (fun k ↦ (1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[B]
                dividedPowerDifferential (A := A) B.dividedPowers (b k)) ⊗ₜ[
            setIndexedDividedPowerPolynomialAlgebra B W]
            exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j
              fun k ↦ Finsupp.single (w k)
                (1 : setIndexedDividedPowerPolynomialAlgebra B W))) := by
  have hsplit : (fun m ↦ (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).1
        (Fin.append
          (fun k ↦ dividedPowerDifferential (A := A)
            (setIndexedDividedPowerPolynomialDividedPowers B W)
            (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) (b k)))
          (fun k ↦ dividedPowerDifferential (A := A)
            (setIndexedDividedPowerPolynomialDividedPowers B W)
            (dividedPowerPolynomialVariable (B : Type uB) (w k))) m)) =
      Fin.append
        (fun k ↦ LinearMap.inl (setIndexedDividedPowerPolynomialAlgebra B W) _ _
          ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[B]
            dividedPowerDifferential (A := A) B.dividedPowers (b k)))
        fun k ↦ LinearMap.inr (setIndexedDividedPowerPolynomialAlgebra B W) _ _
          (Finsupp.single (w k) (1 : setIndexedDividedPowerPolynomialAlgebra B W)) := by
    funext m
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) m
    · rw [Fin.append_left, Fin.append_left]
      exact (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).2.1 (b k)
    · rw [Fin.append_right, Fin.append_right]
      exact (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).2.2 (w k)
  have hinner : exteriorPower.prodEquivDirectSum (i + j)
        (exteriorPowerCongr (i + j)
          (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).1
          (exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) (i + j)
            (Fin.append
              (fun k ↦ dividedPowerDifferential (A := A)
                (setIndexedDividedPowerPolynomialDividedPowers B W)
                (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) (b k)))
              fun k ↦ dividedPowerDifferential (A := A)
                (setIndexedDividedPowerPolynomialDividedPowers B W)
                (dividedPowerPolynomialVariable (B : Type uB) (w k))))) =
      DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
        {pq : ℕ × ℕ // pq.1 + pq.2 = i + j}
        (fun pq ↦ TensorProduct (setIndexedDividedPowerPolynomialAlgebra B W)
          (⋀[setIndexedDividedPowerPolynomialAlgebra B W]^pq.1.1
            (setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
              dividedPowerDifferentials (A := A) B.dividedPowers))
          (⋀[setIndexedDividedPowerPolynomialAlgebra B W]^pq.1.2
            (W →₀ setIndexedDividedPowerPolynomialAlgebra B W))) ⟨(i, j), rfl⟩
        (exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) i
            (fun k ↦ (1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[B]
              dividedPowerDifferential (A := A) B.dividedPowers (b k)) ⊗ₜ[
          setIndexedDividedPowerPolynomialAlgebra B W]
          exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j
            fun k ↦ Finsupp.single (w k)
              (1 : setIndexedDividedPowerPolynomialAlgebra B W)) := by
    refine Eq.trans (DFunLike.congr_arg (exteriorPower.prodEquivDirectSum (i + j))
      ((exteriorPowerCongr_ιMulti (i + j) _ _).trans
        (DFunLike.congr_arg
          (exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) (i + j))
          hsplit))) ?_
    exact prodEquivDirectSum_ιMulti_append i j
      (fun k ↦ (1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[B]
        dividedPowerDifferential (A := A) B.dividedPowers (b k))
      fun k ↦ Finsupp.single (w k) (1 : setIndexedDividedPowerPolynomialAlgebra B W)
  have hlast := sumEquivOfFintype_symm_of_lof
    (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p)
    (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = i + j} ↦
      TensorProduct (setIndexedDividedPowerPolynomialAlgebra B W)
        (⋀[setIndexedDividedPowerPolynomialAlgebra B W]^pq.1.1
          (setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
            dividedPowerDifferentials (A := A) B.dividedPowers))
        (⋀[setIndexedDividedPowerPolynomialAlgebra B W]^pq.1.2
          (W →₀ setIndexedDividedPowerPolynomialAlgebra B W)))
    (⟨(i, j), rfl⟩ : {pq : ℕ × ℕ // pq.1 + pq.2 = i + j})
    (exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) i
        (fun k ↦ (1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[B]
          dividedPowerDifferential (A := A) B.dividedPowers (b k)) ⊗ₜ[
      setIndexedDividedPowerPolynomialAlgebra B W]
      exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j
        fun k ↦ Finsupp.single (w k) (1 : setIndexedDividedPowerPolynomialAlgebra B W))
  exact (completedDividedPowerPolynomialFormsEquiv_of A B W p (i + j) _).trans
    ((DFunLike.congr_arg (AdicCompletion.sumEquivOfFintype
          (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p) _).symm
        (DFunLike.congr_arg (AdicCompletion.of
          (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra B W) p) _) hinner)).trans
      hlast)

end Completed

end DividedPowerPolynomial

end Crystalline

end
