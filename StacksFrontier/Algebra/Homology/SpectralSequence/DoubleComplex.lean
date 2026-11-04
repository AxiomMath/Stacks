module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.Filtration
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.Pages
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.Convergence

/-!
# Spectral sequences: double complexes

Let `𝒜` be an abelian category and let `K^{•,•}` be a double complex of `𝒜` whose total complex
`Tot(K^{•,•})` exists. The total complex carries two decreasing filtrations by subcomplexes,
```
F_I^p Tot^n = ⨁_{i + j = n, i ≥ p} K^{i,j},        F_{II}^p Tot^n = ⨁_{i + j = n, j ≥ p} K^{i,j},
```
and hence two spectral sequences `('E_r, 'd_r)` and `(''E_r, ''d_r)` ([Stacks, Tag 012M]). This file
identifies their first three pages ([Stacks, Tag 0130]) and shows that they converge when every
diagonal of `K^{•,•}` has only finitely many nonzero terms ([Stacks, Tag 0132]).

## Main definitions

* `HomologicalComplex₂.totalFiltration₁`, `HomologicalComplex₂.totalFiltration₂`: the total complex
  filtered by the first, resp. second, coordinate.
* `HomologicalComplex₂.zeroPageObjectIso`, `HomologicalComplex₂.isoOnePage`,
  `HomologicalComplex₂.isoTwoPage`: the identifications of `E_0`, `E_1` and `E_2` as
  constructions, for a filtration by an arbitrary weight. `isoOnePage` is characterized by
  `HomologicalComplex₂.isoOnePage_spec`, which determines it uniquely.
* `HomologicalComplex₂.isoZeroPageTotalFiltration₂`,
  `HomologicalComplex₂.isoOnePageTotalFiltration₂`,
  `HomologicalComplex₂.isoTwoPageTotalFiltration₂`,
  `HomologicalComplex₂.isoPagesTotalFiltration₂`: the three identifications
  `''E_0^{p,q} = K^{q,p}`, `''E_1^{p,q} = H^q(K^{•,p})`,
  `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))` of `exists_iso_pages_totalFiltration₂` as data, with
  their compatibility with the differentials in
  `HomologicalComplex₂.isoZeroPageTotalFiltration₂_hom_d` and
  `HomologicalComplex₂.isoOnePageTotalFiltration₂_hom_d`. These are what
  `StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplexNaturality` shows to be natural in
  `K^{•,•}`; `exists_iso_pages_totalFiltration₂` is derived from them, so the two cannot drift.

## Main results

* `HomologicalComplex₂.isLeast_totalFiltration₁` and `...₂`: `F_I^p Tot^n`, resp. `F_{II}^p Tot^n`,
  is the least subobject of `Tot^n` containing the summands `K^{i,j}` with `i ≥ p`, resp. `j ≥ p`,
  and is therefore decreasing in `p`.
* `HomologicalComplex₂.exists_iso_pages_totalFiltration₁`: `'E_0^{p,q} = K^{p,q}` with
  `'d_0 = (-1)^p d_2`, `'E_1^{p,q} = H^q(K^{p,•})` with `'d_1 = H^q(d_1)`, and
  `'E_2^{p,q} = H^p_I(H^q_{II}(K^{•,•}))`.
* `HomologicalComplex₂.exists_iso_pages_totalFiltration₂`: `''E_0^{p,q} = K^{q,p}` with
  `''d_0 = d_1`, `''E_1^{p,q} = H^q(K^{•,p})` with `''d_1 = (-1)^q H^q(d_2)`, and
  `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))`.
* `HomologicalComplex₂.isBounded_and_converges_totalFiltration₁` and `...₂`: for a double complex
  with finite diagonals, both spectral sequences are bounded, induce finite filtrations on the
  cohomology of the total complex, converge to it, and detect membership in a weak Serre
  subcategory.

## Implementation notes

The filtration steps are the images of idempotents of `Tot^n`, the projections onto the summands
`K^{i,j}` with `i ≥ p`, resp. `j ≥ p`; they are subcomplexes because the differential of `Tot`
raises both coordinates. As in `CochainComplex.isBounded_and_converges_of_isDegreewiseFinite`, "the
spectral sequence of the filtered complex" is a spectral sequence `E` together with the
identifications `e` of its pages with the quotients `Z_r^{p,q}/D_r^{p,q}` and the compatibility `hδ`
of its differentials with `d`, which is what [Stacks, Tag 012M]
(`CochainComplex.exists_cohomologicalSpectralSequence`) provides. The second page is identified
through the page-turning isomorphism of `E` itself, as an object.

## References

* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
-/
