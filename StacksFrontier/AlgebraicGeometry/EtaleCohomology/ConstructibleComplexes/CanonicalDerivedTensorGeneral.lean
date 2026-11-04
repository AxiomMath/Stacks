module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.CanonicalDerivedTensorGeneral.DerivedTensorBifunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.CanonicalDerivedTensorGeneral.ToTensorExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.CanonicalDerivedTensorGeneral.Existence

/-!
# The canonical derived tensor product at three independent universes

`Stacks.SheafOfModules.canonicalDerivedTensorProduct` (Stacks 06YU) is built for a ringed site
`AlgebraicGeometry.RingedSite.{c, u, u}`, whose morphisms and whose sections share one universe.
The constant coefficient ringed site of Stacks 03TR is an
`AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) r}`, whose sections sit above its
morphisms, so Stacks 03TT needs the construction with the three universes of the site — the
objects `c`, the morphisms `v` and the sections `w` — independent.

Nothing in the construction relates `v` and `w`: the K-flat resolutions come from
`Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize`, which resolves by flat
modules supplied by a flat cover, and every later step is a localization descent which never
sees the site. A declaration named with the suffix `General` (definitions) or `_general`
(theorems and instances) generalizes the declaration of the same stem, which is the case `v = w`.

## Main definitions

* `Stacks.SheafOfModules.canonicalDerivedTensorProductGeneral` — the canonical derived tensor
  product on a ringed site `AlgebraicGeometry.RingedSite.{c, v, w}`; it generalizes
  `Stacks.SheafOfModules.canonicalDerivedTensorProduct`.

## Main results

* `Stacks.SheafOfModules.exists_derivedTensorProduct_general` — Stacks 06YU at three independent
  universes; it generalizes `Stacks.SheafOfModules.exists_derivedTensorProduct`.

## File layout

* `CanonicalDerivedTensorGeneral/DerivedTensorBifunctor.lean` — K-flat resolutions, the K-flat
  localization, and the derived tensor bifunctor.
* `CanonicalDerivedTensorGeneral/ToTensorExactness.lean` — the canonical map to the total
  tensor product, and the derived tensor product from exactness in each variable.
* `CanonicalDerivedTensorGeneral/Existence.lean` — compatibility with the shifts, exactness in
  each variable, and existence (Stacks 06YU).

## Implementation notes

The `HasMapBifunctor` hypothesis of every section is spelled with
`HomologicalComplex.HasMapBifunctorReg`, the copy of Mathlib's `abbrev` with a regular kernel
reducibility hint, as the hypotheses of `Stacks.SheafOfModules.Tensor.tensorComplex` and
`Stacks.SheafOfModules.IsKFlat` are, so that the kernel does not compare two spellings of the
hypothesis at every use of either. The shifts on `tensorComplex` are likewise those of the copy
`CategoryTheory.Functor.map₂HomologicalComplexReg` that `tensorComplex` unfolds to. The exactness
proofs compare them with the shifts of Mathlib's `CategoryTheory.Functor.map₂HomologicalComplex`
that `Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors` and `bifunctorPhiRFactors`
carry, through `Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors_commShift_reg` and
`bifunctorPhiRFactors_commShift_reg` of `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/BifunctorCommShiftTwo.lean`, which are
stated for an arbitrary bifunctor, where the kernel has no tensor product to unfold.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YT](https://stacks.math.columbia.edu/tag/06YT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0GSL](https://stacks.math.columbia.edu/tag/0GSL)
-/
