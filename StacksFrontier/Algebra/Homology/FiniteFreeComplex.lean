module

public import StacksFrontier.Algebra.Homology.FiniteFreeComplex.SplitOffElementary
public import StacksFrontier.Algebra.Homology.FiniteFreeComplex.BoundedFreeComplex
public import StacksFrontier.Algebra.Homology.FiniteFreeComplex.TrivialIsoOfExact
public import StacksFrontier.Algebra.Homology.FiniteFreeComplex.ReductionModNonzerodivisor

/-!
# Complexes of finite free modules given by matrices

This file treats complexes of finite free modules over a commutative ring `R` whose differentials
are given by matrices in the standard bases, and proves three results on them.

Let `(C_•, φ_•)` be a complex of finite free `R`-modules with `C_j = R^{n_j}` and differentials
`φ_j : C_j → C_{j-1}`. If for some index `i` the differential `φ_i` has an invertible matrix
coefficient, then `n_i ≥ 1` and `n_{i-1} ≥ 1`, and there is a complex of finite free `R`-modules
`(C'_•, φ'_•)` with

```
C'_j = R^{n_i - 1}      if j = i,
C'_j = R^{n_{i-1} - 1}  if j = i - 1,
C'_j = R^{n_j}          otherwise,
```

together with an isomorphism of complexes `(C_•, φ_•) ≅ (C'_•, φ'_•) ⊕ T^{(i)}_•`, where
`T^{(i)}_•` is the elementary identity complex `… → 0 → R --id--> R → 0 → …` concentrated in
degrees `i` and `i - 1`.

Let `R` be a Noetherian local ring whose maximal ideal is an associated prime, that is, of depth
`0`. A complex `0 → R^{n_e} → ⋯ → R^{n_0}` of finite free `R`-modules which is exact at
`R^{n_e}, …, R^{n_1}` is isomorphic to a direct sum of trivial complexes, each with all terms `0`
except possibly two adjacent terms `R` joined by the identity, or a single term `R`.

Let `R` be a local ring with maximal ideal `m`. If a complex `0 → R^{n_e} → ⋯ → R^{n_0}` of
finite free `R`-modules is exact at `R^{n_e}, …, R^{n_1}` and `x ∈ m` is a nonzerodivisor, then
the reduced complex is exact at `(R/xR)^{n_e}, …, (R/xR)^{n_2}`.

## Main definitions

* `FreeComplex`: a `ℤ`-indexed complex of finite free modules, given by ranks and matrices.
* `FreeComplex.toComplex`: the associated `HomologicalComplex (ModuleCat R) (ComplexShape.down ℤ)`.
* `FreeComplex.elementaryComplex`: the elementary identity complex `T^{(i)}`.
* `BoundedFreeComplex`: a complex `0 → R^{n_e} → ⋯ → R^{n_0}` of finite free `R`-modules, with
  differentials given by matrices.
* `BoundedFreeComplex.Exact`: exactness at `R^{n_e}, …, R^{n_1}`, where exactness at the top spot
  means that `φ_e` is injective.
* `BoundedFreeComplex.Iso`: an isomorphism of complexes, given by a degreewise change of basis
  commuting with the differentials.
* `BoundedFreeComplex.IsTrivial`: every differential is a partial permutation matrix, that is, the
  complex is a direct sum of trivial complexes.

## Main results

* `exists_splitOff_elementaryComplex_of_hasInvertibleCoeff`: a complex whose differential `φ_i`
  has an invertible matrix coefficient splits off `T^{(i)}`.
* `exists_trivial_iso_of_exact`: over a Noetherian local ring of depth `0`, an exact complex is
  isomorphic to a direct sum of trivial complexes.
* `tag_00MZ`: exactness of a complex of finite free modules is preserved, except at `R^{n_1}`, by
  reduction modulo a nonzerodivisor in the maximal ideal.

## Implementation notes

* A `FreeComplex` is a rank function `n : ℤ → ℕ` together with differential matrices
  `d i : Matrix (Fin (n i)) (Fin (n (i+1))) R`, where `d i` represents the differential
  `R^{n (i+1)} → R^{n i}` in the standard bases. In particular `φ_i : R^{n_i} → R^{n_{i-1}}`
  corresponds to the matrix `d (i-1)`, noting `n (i-1+1) = n i`, and the complex condition
  `φ_{j-1} ∘ φ_j = 0` becomes `d i * d (i+1) = 0`. Isomorphisms and direct sums of complexes are
  the categorical `≅` and `⊞` of `FreeComplex.toComplex`.
* In `IsMatrixComplex`, `ExactAtSucc` and `tag_00MZ` the differential `φ_i : R^{n_i} → R^{n_{i-1}}`
  is reindexed to `φ i : R^{n (i+1)} → R^{n i}`, so `ExactAtSucc n φ i` is exactness at position
  `i+1`. The convention `φ_{e+1} = 0` is encoded by the hypothesis `n (e+1) = 0`, so that
  exactness at position `e` means that `φ_e` is injective.

## References

* [Stacks Project, Tag 00MT](https://stacks.math.columbia.edu/tag/00MT)
* [Stacks Project, Tag 00MY](https://stacks.math.columbia.edu/tag/00MY)
* [Stacks Project, Tag 00MZ](https://stacks.math.columbia.edu/tag/00MZ)
-/
