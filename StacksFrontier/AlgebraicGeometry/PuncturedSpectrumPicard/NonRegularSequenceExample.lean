module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.NonRegularSequenceExample.Rings
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.NonRegularSequenceExample.SquareZero
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.NonRegularSequenceExample.PicardGroup

/-!
# A non-complete-intersection quotient with nontrivial local Picard group

For every field `k`, the quotient of the eight-variable power-series ring by
`(a³, b³, xa² + yab + zb², w²)` has nontrivial Picard group on its punctured spectrum.
The ambient ring is regular of dimension eight, despite the quotient having four
displayed equations. The intermediate quotients have the depths used in the example.

## Main definitions

* `powerSeriesRing`, `intermediateRing`, and `exampleRing` are the ambient and
  intermediate power-series quotients.

## Main results

Every declaration below carries `@[stacks 0F9L]` with the clause it proves, except the two
further forms of the conclusion, which state that same clause and so leave it on the first.

* `exampleRing_scheme_picardGroup_puncturedSpectrum_not_subsingleton`: **the conclusion** — the
  Picard group of the punctured spectrum of `A` is nontrivial, at
  `AlgebraicGeometry.Scheme.picardGroup`, the Picard group [Stacks, Tag 0F2I] is stated at.
* `exampleRing_picardGroup_puncturedSpectrum_not_subsingleton'`: the same statement at
  `Stacks.SheafOfModules.Picard.PicardGroup`, the small model at which the exact sequence of
  [Stacks, Tag 0C6R] that proves it lives.  The two are carried onto one another by
  `Stacks.SheafOfModules.picardGroupShrinkAddEquiv`.
* `exampleRing_picardGroup_puncturedSpectrum_not_subsingleton`: the small-model statement with
  the source's three geometric inputs taken as arguments rather than proved.
* `powerSeriesRing_isRegularLocalRing` and `powerSeriesRing_dimension`: the ambient ring
  `B = k⟦a,b,x,y,z,u,v,w⟧` is regular of dimension `8`.  With `r = 4` displayed equations
  this gives `dim B - r = 4 ≥ 4`, which is what makes the example a counterexample to any
  extension of [Stacks, Tag 0F2I] that drops the regular-sequence hypothesis.
* `socleElement_ne_zero` and `socleElement_mul_variable`: in
  `A₁ = k⟦a,b,x,y,z⟧/(a³, b³, xa² + yab + zb²)` the element `a²b²` is nonzero and is
  annihilated by each of the five variables, so `socleRing_depth` gives `depth A₁ = 0`.
* `intermediateRing_depth` and `exampleRing_depth`: `depth A₀ = depth A = 2`.
* `exampleRing_equiv_truncatedPolynomial`: `A ≅ A₀[w]/(w²)`, with its coordinate inclusion
  and reduction maps and their exact sequence `0 → A₀ → A → A₀ → 0`.
* `intermediateRing_globalSections_puncturedSpectrum` and
  `exampleRing_globalSections_puncturedSpectrum`: `Γ(U₀, 𝒪_{U₀}) = A₀` and
  `Γ(U, 𝒪_U) = A`, which is what depth `2` buys.
* `exists_puncturedSpectrum_firstOrderThickening`: reduction modulo `w` is a first-order
  thickening `U₀ ⟶ U` of the punctured spectra over `Spec` of the reduction, invertible
  global functions lift along it, and its ideal sheaf pulled back to `U₀` is `𝒪_{U₀}`.
* `socleRing_nontrivial`, `intermediateRing_nontrivial`, `exampleRing_nontrivial`: the three
  quotients are nonzero rings.

## Implementation notes

**The shape of the proof.**  The source's argument runs through the exact sequence of
[Stacks, Tag 0C6R] for the first-order thickening `i : U₀ ⟶ U`,

`H⁰(U, 𝒪_U^*) → H⁰(U₀, 𝒪_{U₀}^*) → H¹(U₀, ℐ) → Pic(U)`,

and all three of its inputs are proved here.

* The thickening is `A = A₀[w]/(w²)` read on spectra: `Spec` of a surjection with square-zero
  kernel is a first-order thickening (`isFirstOrderThickening_specMap`), restriction to an open
  of the target preserves that (`isFirstOrderThickening_morphismRestrict`), and the punctured
  spectrum of `A₀` is the preimage of the punctured spectrum of `A`
  (`specMap_preimage_puncturedSpectrum`).
* Surjectivity of the units map is the ring-homomorphism section `ι` of the reduction together
  with `Γ(U₀, 𝒪_{U₀}) = A₀`: a unit downstairs is lifted along the identification, pushed
  through `ι`, and restricted (`surjective_units_appTop_puncturedSpectrum`).  Degree-zero
  sheaf cohomology is global sections (`surjective_sheafH_zero_map`).
* Nonvanishing of `H¹(U₀, ℐ)` has two halves.  The ideal sheaf is the structure sheaf: on the
  affine spectrum multiplication by `w` carries `A₀` isomorphically onto the kernel `wA` of the
  reduction, which through the tilde-Gamma adjunction presents `q_* 𝒪_{Spec A₀}` as the ideal
  sheaf (`affine_squareZero_kernel`); restriction to an open is exact, so the presentation
  descends (`restrict_squareZero_kernel`), and pulling back along the thickening — a
  homeomorphism — gives `𝒪_{U₀} ≅ ℐ|_{U₀}` (`idealAddSheafOnSubIsoOfPushforwardIso`).  And
  `H¹(U₀, 𝒪_{U₀}) ≠ 0` because `depth A₀ = 2`: [Stacks, Tag 0AVZ] makes `H²_𝔪(A₀)` nonzero,
  the infimum of the nonvanishing degrees being a natural number and hence attained, and
  [Stacks, Tag 0DWR] compares `H^n(U₀, 𝒪_{U₀})` with `H^{n+1}_𝔪(A₀)` above degree zero
  (`nontrivial_sheafH_one_unit_puncturedSpectrum_of_depth_eq_two`).

**Spellings.**  The variables are indexed by `Fin`: indices zero and one are `a,b`, indices
two through four are `x,y,z`, indices five and six are `u,v`, and index seven is `w`.  The
seven-coordinate inclusion is renaming by the standard embedding `Fin 7 ↪ Fin 8`; reduction
sets the eighth coordinate to zero.  The sequence of [Stacks, Tag 0C6R] is stated at
`Stacks.SheafOfModules.Picard.PicardGroup` in this library, so the argument runs there and is
then carried across `Stacks.SheafOfModules.picardGroupShrinkAddEquiv` to
`AlgebraicGeometry.Scheme.picardGroup`, which is what [Stacks, Tag 0F2I] is stated at.

## References

* [Stacks Project, Tag 0F9L](https://stacks.math.columbia.edu/tag/0F9L)
-/
