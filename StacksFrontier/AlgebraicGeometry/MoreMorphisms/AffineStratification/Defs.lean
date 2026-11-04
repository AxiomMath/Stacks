module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedLocallyClosed
public import StacksFrontier.Topology.Stratification.LocallyFinite

/-!
# Affine stratifications of a scheme

An *affine stratification* of a scheme `X` is a locally finite stratification of the underlying
space of `X` whose strata, equipped with their reduced induced scheme structures, are affine
schemes with affine inclusions into `X`. The *affine stratification number* of `X` is the least
`n` for which `X` admits an affine stratification indexed by `0, …, n`.

## Main definitions

* `AlgebraicGeometry.AffineStratification`: an affine stratification of a scheme, indexed by a
  partially ordered type.
* `AlgebraicGeometry.affineStratificationNumber`: the least length of a finite affine
  stratification.

## Implementation notes

The underlying locally finite stratification supplies the locally closed subsets. Each stratum
is given its canonical reduced induced scheme structure, so its affineness and that of its
inclusion are properties of canonical objects, recorded as fields of the structure rather than
as existential statements.

The affine stratification number is an infimum over the affine stratifications indexed by
`Fin (n + 1)`. The expression makes sense for any scheme; outside the nonempty quasi-compact
quasi-separated case — where a finite affine stratification exists — the set of admissible `n`
is empty and its infimum in `ℕ` is zero. Indexing by `Fin (n + 1)` lets bounds and cohomological
vanishing statements use the number directly.

## References

* [Stacks Project, Tag 0F2S](https://stacks.math.columbia.edu/tag/0F2S)
* [Stacks Project, Tag 0F2V](https://stacks.math.columbia.edu/tag/0F2V)
-/

@[expose] public section

universe u v


namespace AlgebraicGeometry

/-- A locally finite stratification of `X` with affine reduced induced strata
and affine inclusions into `X`. -/
@[stacks 0F2S]
structure AffineStratification (X : Scheme.{u}) (I : Type v) [PartialOrder I] where
  /-- The locally closed subsets comprising the stratification. -/
  strata : I → Set X
  /-- The strata form a locally finite stratification. -/
  isLocallyFiniteStratification : IsLocallyFiniteStratification strata
  /-- Each reduced induced stratum is an affine scheme. -/
  isAffine : ∀ i, IsAffine
    (Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedScheme (strata i)
    (isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i))
  /-- Each canonical inclusion of a stratum is an affine morphism. -/
  isAffineHom : ∀ i, IsAffineHom
    (Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedInclusion
    (strata i) (isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i))

/-- The least `n` admitting an affine stratification of `X` with strata
indexed by `0, …, n`. -/
@[stacks 0F2V]
noncomputable def affineStratificationNumber (X : Scheme.{u}) : ℕ :=
  sInf {n : ℕ | Nonempty (AffineStratification X (Fin (n + 1)))}

end AlgebraicGeometry

end
