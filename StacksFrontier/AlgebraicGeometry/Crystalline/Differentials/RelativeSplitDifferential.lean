module

public import
  StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential.Splitting
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential.Completion
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential.Contraction
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential.Perturbation

/-!
# Splitting the divided power de Rham differential of `B⟨x_w⟩` into a relative and a base part

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W` index
a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩`.  This module splits the divided
power de Rham differential of `P`

`d = d_rel + d_base`

into a part which is **`B`-linear** and a part which only obeys the Leibniz rule, and does the
same for the `p`-adic completions.

## What the two parts are

`Crystalline.DividedPowerPolynomial.dividedPowerPolynomialFormsEquiv` puts the forms of `P` in
bidegree form,

`Ωⁿ_{P/A,δ'} = ⨁_{i + j = n} ((⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})) ⊗_P (⋀ʲ_P (W →₀ P)))`,

the summand `(i, j)` being the one with `i` coefficient differentials and `j` variable
differentials.  `Crystalline.DividedPowerPolynomial.formsBidegreeProjection` is the projection
`πᵢ` onto the forms with `i` coefficient differentials, and the two parts of the differential are
its two nonzero components:

`d_rel = ∑ᵢ πᵢ ∘ d ∘ πᵢ`,   `d_base = ∑ᵢ π_{i+1} ∘ d ∘ πᵢ`.

That these two exhaust `d` is
`Crystalline.DividedPowerPolynomial.formsBidegreeProjection_dividedPowerDeRham_eq_zero`: the de
Rham differential of a form with `i` coefficient differentials has only the components `i` and
`i + 1`.  That is read off the sector computation
`Crystalline.DividedPowerPolynomial.relativeSectorMapDeg_dividedPowerDeRham`, whose two terms are
the coefficient differential `1 ⊗ d_B`, landing in bidegree `(i + 1, j)`, and the Koszul
differential, landing in bidegree `(i, j + 1)`.

## Why the relative part has to be linear over the base and the base part cannot be

`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`, the perturbation argument of
[Stacks, Lemma 60.21.2, Tag 07LD], carries the relative part of the differential as a **linear**
map over the base and the base part as a merely additive one, and the asymmetry is forced: the
relative differential is the one that tensors up with a module `M` carrying a connection, as
`1_M ⊗ d_rel`, and only a linear map does that.

`Crystalline.DividedPowerPolynomial.formsRelDifferentialAux_smul` is that linearity:
for `b ∈ B` the Leibniz correction `d_B b ∧ ω` of `d (b ω)` carries one coefficient differential
more than `ω`, so the projection that defines `d_rel` deletes it, and
`Crystalline.DividedPowerPolynomial.formsRelDifferential` records the resulting `B`-linear map.
The relative differential is **not** `P`-linear — for a variable the correction term
`d x_w ∧ ω` has the same number of coefficient differentials as `ω` and survives — which is why
`B` and not `P` is the ring of linearity, and why the whole Leibniz correction of a base scalar
sits in the base part, which is therefore only additive.

## The completion

Every map above is `A`-linear, hence additive, hence has a `p`-adic completion by the additive
functor `Crystalline.PAdicCompletion.mapAddHom`, and every identity between additive maps
survives.  That is the whole of the completed half of this module, exactly as in
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/CompletedRelativePoincare.lean`: the
completed relative and base differentials are the completions of the uncompleted ones, and the
splitting, the square-zero identity and the three projection identities are the images of their
uncompleted counterparts.

## The `D`-module structure, and the instantiation of the perturbation argument

`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` asks for its `drel`, `proj`, `hhat`,
`iotaForm` and `piForm` as maps **linear over `D`**, the `p`-adic completion of `B`, because it
tensors the forms with a `D`-module `M`.  The completed forms `Ω̂ⁿ_{D'}` are an `AdicCompletion`
along `(p) ⊆ P`, hence a `D'`-module, so what is needed first is a restriction of scalars along
the ring map `D → D'` — the `p`-adic completion `Crystalline.completedRingHom` of the coefficient
inclusion `B → P`.  That is
`Crystalline.DividedPowerPolynomial.moduleCompletedPolynomialForms`, and with it the five maps are
recorded as `D`-linear:
`..._completedFormsRelDifferentialₗ`, `..._completedFormsBidegreeProjectionₗ`,
`..._completedRelativeFormsHomotopyₗ`, `..._completedCoefficientFormsMapₗ` and
`..._completedRelativeFormsRetractionₗ`.

What makes them `D`-linear is that their uncompleted counterparts are `B`-linear — `d_rel` by
`..._formsRelDifferentialAux_smul`, `h` by `..._relativeFormsHomotopy_smul`, `ε` by
`..._relativeFormsRetraction_smul`, `ψ` by construction — and that the completion of a `B`-linear
additive map is `B^∧`-linear, which is
`Crystalline.PAdicCompletion.mapAddHom_smul`.  The base part `d_base` stays merely additive, and
must: the Leibniz correction of a base scalar lies entirely in it.

With the structure in place the remaining hypotheses are proved here:
the relative contraction identity `d_rel ĥ + ĥ d_rel + ψ̂ ε̂ = id` (which is *not* the existing
contraction of the full differential, but its coefficient-degree-preserving part), that wedging
with a coefficient one-form raises the coefficient degree, and that a connection pushed into
`Ω̂¹_{D'}` from `Ω̂¹_D` takes its values in coefficient degree one.  The instantiation is
`..._exists_twistedHomotopyEquiv_completedPolynomialForms` and, with the connection coming from
`Ω̂¹_D`, `..._exists_twistedHomotopyEquiv_pushedConnection`.

## What is deliberately not claimed

* **The relative part is not identified with a de Rham differential of `P` over `B`.**  As in
  `StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/PolynomialFormsDecomposition.lean`,
  the variable factor of the bidegree decomposition is the exterior power of the free module on the
  symbols `d x_w` and is not called `Ωʲ_{D'/D}`; `d_rel` is defined as a component of `d` and
  nothing says it is the differential of a relative de Rham complex.
* **No bigraded complex is assembled.**  `d_rel² = 0` is proved; `d_base² = 0` and the
  anticommutation are not, and are not needed by the perturbation argument, which derives the
  cross term from `d² = 0` and `d_rel² = 0` alone
  (`Crystalline.CompletedDeRham.differential_relDifferential_cross`).
* **The vanishing of the curvature is an input of the instantiations in this module.**  They take
  `Crystalline.CompletedDeRham.IsSquareZero` for the twisted differential, as every consumer of
  the completed de Rham complex in this library does, including
  `Crystalline.CompletedDeRham.complex` itself.  It is derived from the source's integrability
  hypothesis in
  `StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/CompletedPoincareIntegrable.lean`, by
  `Crystalline.DividedPowerPolynomial.isSquareZero_pushedConnection`, and the tag is registered
  there.

## Main definitions

* `Crystalline.DividedPowerPolynomial.conjugateSummandProjection` — the projection onto one
  summand of a direct sum decomposition of an arbitrary module, where every fact about the
  bidegree projections is proved.
* `Crystalline.DividedPowerPolynomial.formsBidegreeProjection` — the projection `πᵢ` of
  `Ωⁿ_{P/A,δ'}` onto the forms with `i` coefficient differentials.
* `Crystalline.DividedPowerPolynomial.formsRelDifferentialAux` and
  `..._formsRelDifferential` — **the relative differential
  `d_rel : Ωⁿ_{P/A,δ'} → Ω^{n+1}_{P/A,δ'}`**, read `A`-linearly and with its `B`-linearity
  recorded.
* `Crystalline.DividedPowerPolynomial.formsBaseDifferential` — **the base differential
  `d_base`**, `A`-linear and no more.
* `Crystalline.DividedPowerPolynomial.completedFormsBidegreeProjection`,
  `..._completedFormsRelDifferential`, `..._completedFormsBaseDifferential` — their `p`-adic
  completions.

## Main results

* `Crystalline.DividedPowerPolynomial.dividedPowerDeRham_eq_formsRelDifferential_add` and
  `..._dividedPowerDeRham_eq_formsRelDifferential_add_formsBaseDifferential` — **`d = d_rel +
  d_base`**, the `hsplit` hypothesis of
  `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`.
* `Crystalline.DividedPowerPolynomial.formsRelDifferentialAux_smul` — **`d_rel` is `B`-linear.**
* `Crystalline.DividedPowerPolynomial.formsRelDifferential_formsRelDifferential` and
  `..._formsRelDifferential_comp_formsRelDifferential` — **`d_rel² = 0`**, the `hdrel`
  hypothesis.
* `Crystalline.DividedPowerPolynomial.formsBidegreeProjection_sum` — the projections sum to the
  identity in each exterior degree, the index set being finite: the `hprojsum` hypothesis.
* `Crystalline.DividedPowerPolynomial.formsBidegreeProjection_formsBaseDifferential_eq_zero` —
  **`d_base` strictly raises the coefficient degree**: the `hprojbase` hypothesis.
* `Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_formsBidegreeProjection` — **the
  relative homotopy `h` preserves the coefficient degree**: the `hprojhhat` hypothesis.
* `Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_relContraction` and
  `..._relativeFormsHomotopy_relContraction_zero` — **the relative contraction identity
  `d_rel h + h d_rel + ψ ε = id`**, the `hconform` and `hcon0form` hypotheses.
* `DividedPowerPolynomial.formsBidegreeProjection_wedge_formsBidegreeProjection_eq_zero` —
  **wedging with a coefficient one-form raises the coefficient degree**, the `hprojwedge`
  hypothesis.
* `Crystalline.DividedPowerPolynomial.moduleCompletedPolynomialForms` — **`Ω̂ⁿ_{D'}` as a
  `D`-module**, and the five `D`-linear maps named in the section above.
* `Crystalline.DividedPowerPolynomial.exists_twistedHomotopyEquiv_completedPolynomialForms` and
  `..._exists_twistedHomotopyEquiv_pushedConnection` — **the completed clause of
  [Stacks, Lemma 60.21.2, Tag 07LD] at the genuine completed divided power forms.**
* the completed counterparts
  `..._completedDividedPowerDeRham_eq_completedFormsRelDifferential_add`,
  `..._completedFormsRelDifferential_completedFormsRelDifferential`,
  `..._completedFormsBidegreeProjection_sum`,
  `..._completedFormsBidegreeProjection_completedFormsBaseDifferential_eq_zero` and
  `..._completedRelativeFormsHomotopy_completedFormsBidegreeProjection`.

## References

* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/
