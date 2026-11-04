module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.SquareZeroDerivations
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.DifferentialsBasis
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.AugmentedContraction
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.CompletedRing
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.CompletedForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.CompletedExactness

/-!
# The divided power Poincaré lemma

Both assertions of the lemma are proved here: the uncompleted one, and its `p`-adic analogue.

Let `A` be a ring and let `P = A⟨x_w : w ∈ W⟩` be the divided power polynomial algebra on an
arbitrary family of variables, carrying the canonical divided powers `δ` on its augmentation
ideal.  For every `A`-module `M` the complex

`0 → M → M ⊗[A] P → M ⊗[A] Ω¹_{P/A,δ} → M ⊗[A] Ω²_{P/A,δ} → ⋯`

is exact.  This is proved by showing the stronger statement that the augmented divided power
de Rham complex

`E : 0 → A → P → Ω¹_{P/A,δ} → Ω²_{P/A,δ} → ⋯`

is contractible as a complex of `A`-modules, i.e. that its identity is homotopic to zero; the
displayed complex is `M ⊗[A] E`, and tensoring preserves a contracting homotopy.

The contracting homotopy is produced as in the source.  First, `Ω¹_{P/A,δ}` is free over `P` on
the differentials `d x_w`: the universal divided power derivations out of `P` are computed by
lifting a prescribed family of values through the square-zero divided power extension
`P ⊕ M` and the universal property of the divided power polynomial algebra.  Consequently
`Ωⁿ_{P/A,δ}` is free over `P` on the wedges `d x_{w₁} ∧ ⋯ ∧ d x_{wₙ}`, hence free over `A` on
the products `x^{[L]} · d x_{w₁} ∧ ⋯ ∧ d x_{wₙ}`.  In this basis the differential is computed by
the Leibniz rule together with `d (x^{[k]}) = x^{[k-1]} d x`.

Second, `E` splits as the direct sum, over multi-indices `K`, of the subcomplexes `E(K)` spanned
by the basis elements whose monomial and wedge together have total exponent `K`.  For `K = 0` the
subcomplex is the identity `A → A` in the two lowest degrees.  For `K ≠ 0` with support `S` the
subcomplex is the exterior algebra `⋀ A^S` with differential given by exterior multiplication by
`v = ∑_{s ∈ S} e_s`, and a contracting homotopy is the Koszul contraction along any coordinate
functional of `S`, since such a functional takes the value `1` on `v`
([stacks 0626], `koszul_scalar_eq_homotopy`).  Assembling these homotopies over all `K` gives the
contraction of `E`.

The source's second assertion is the `p`-adic analogue.  Let `p` be a prime, let `D` be the
`p`-adic completion of `P`, let `δ` be the unique continuous extension of the canonical divided
powers of `P` to the closure `⋂ₙ (P₊ D + pⁿ D)` of `P₊` in `D`, and let `Ωⁱ_D` be the `p`-adic
completion of `Ωⁱ_{D/A,δ}`.  Then for every `p`-adically complete `A`-module `M` the completed
complex

`0 → M → M ⊗̂_A D → M ⊗̂_A Ω¹_D → M ⊗̂_A Ω²_D → ⋯`

is exact.  This is reduced to the uncompleted assertion level by level: modulo `pᵉ` the completed
de Rham complex is the de Rham complex of `P/pᵉ`, which is a quotient of the complex `E` above,
so the contracting homotopy of `E` descends; the completed statement then follows because `M` is
complete and the ideal `(p) ⊆ A` is finitely generated.

## Main results

* `Crystalline.dividedPowerDifferentialsCoordinateEquiv` and
  `Crystalline.dividedPowerDifferentialsBasis` — **`Ω¹_{P/A,δ}` is free over `P` on the
  differentials `d x_w` of the variables**, as a coordinate equivalence `Ω¹_{P/A,δ} ≅ (W →₀ P)`
  and as a `Module.Basis` indexed by `W`, with no finiteness assumption on `W`.  This is the
  first step of the proof below, and it is also the only description of the `d x_w`-coordinates
  of a differential in the library, so it is stated publicly rather than kept inside the proof.
* `Crystalline.dividedPowerPolynomialDeRham_tensor_augmentation_injective` — the augmentation
  `M → M ⊗[A] P` stays injective, i.e. exactness at the first term.
* `Crystalline.dividedPowerPolynomialDeRham_tensor_exact` — exactness at every later term.
* `Crystalline.augmentedDividedPowerDeRhamComplex_contractible` — the stronger statement that
  the untensored augmented complex is homotopy equivalent to zero.
* `Crystalline.CompletedPoincare.exists_continuousDividedPowers` and
  `Crystalline.CompletedPoincare.continuousDividedPowers_unique` — the continuous extension `δ`
  of the canonical divided powers to the closed augmentation ideal of `D` exists and is unique.
* `Crystalline.CompletedPoincare.completedDeRham_tensor_augmentation_injective`,
  `Crystalline.CompletedPoincare.completedDeRham_tensor_exact_augmentation` and
  `Crystalline.CompletedPoincare.completedDeRham_tensor_exact` — exactness of the completed
  complex at `M`, at `M ⊗̂_A D` and at `M ⊗̂_A Ωⁱ⁺¹_D`.

## Implementation notes

The source complex begins in cohomological degree `-1`.  It is reindexed here so that the
augmentation sits in degree `0` and `Ωⁱ_{P/A,δ}` in degree `i + 1`; this is
`Crystalline.augmentedDividedPowerDeRhamComplex`, a `CochainComplex (ModuleCat A) ℕ`.  So that
the coefficient ring and the variables may live in independent universes, the degree-zero term
is the range of the coefficient map `A → P` rather than `A` itself;
`Crystalline.coefficientLinearEquiv` is the canonical identification of that range with `A`, and
`Crystalline.augmentedDividedPowerDeRhamDifferential_coefficient` records that it commutes with
the augmentation.  Note that the degree-one term is Mathlib's `⋀[P]^0`, which is canonically `P`
but not literally `P`, as in `Crystalline.DividedPowerDeRhamComplex`.

The ring `A` is turned into a divided power ring by equipping its zero ideal with the trivial
divided powers, and `P` then carries the canonical divided powers of the set-indexed divided
power polynomial theory on `I P + P₊ = P₊`.

The basis of `Ωⁿ_{P/A,δ}` is indexed by `n`-element subsets of `W`, so the construction needs a
linear order on `W`; one is chosen from the well-ordering theorem, and nothing depends on the
choice.

For the completed assertion, every completion is Mathlib's `AdicCompletion` along the ideal
`(p)`: the ring `D` is the completion of `P` along `(p) ⊆ P`, while all module completions are
taken along `(p) ⊆ A`.  For a `D`-module the two agree, because `pⁿ` cuts out the same subgroup
either way; taking them over `A` is what keeps `Ωⁱ_D` an `A`-module and makes the de Rham
differential, which is only `A`-linear, an `AdicCompletion.map`.  Accordingly `M ⊗̂_A Ωⁱ_D` is
`Crystalline.CompletedPoincare.completedTensor`, the `p`-adic completion of the ordinary tensor
product.  The closed augmentation ideal of `D` is constructed rather than assumed, as is `δ`:
continuity is recorded as preservation of congruence modulo every `pⁿ`, and agreement on the
image of `P₊`, which pins the extension down because that image is dense.  Tag 07KD does not
apply here, since it needs a power of `p` inside the divided power ideal while `p` is not
nilpotent in `D/P₊D`.  The three completed exactness assertions are stated as separate covering
lemmas rather than assembled into one cochain complex, which would require lifting `M` and the
terms `M ⊗̂_A Ωⁱ_D` into a common universe.

Four `local implicit_reducible` attributes appear below.  They name the definitions this file
spells two ways at once, so that unification and instance search can see through them: the
divided power polynomial algebra occurs both directly and as the carrier of a
`DividedPowerRing`, and `RestrictScalars` hides a module behind a type synonym.

## References

* [Stacks Project, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Tag 0626](https://stacks.math.columbia.edu/tag/0626)
-/
