module

public import StacksFrontier.Homology.Perfect.FibreCriterion.FibreCohomologyVanishing
public import StacksFrontier.Homology.Perfect.FibreCriterion.BaseChangeSurjective
public import StacksFrontier.Homology.Perfect.FibreCriterion.ThreeTermSplitting

/-!
# Fibrewise criteria for splitting a pseudo-coherent complex

Let `R` be a commutative ring, let `p ⊂ R` be a prime ideal and let `K` be a pseudo-coherent
object of `D(R)`. The *derived fibre* of `K` at `p` is `K ⊗_R^L κ(p)`. This module proves the
three fibrewise splitting criteria of the Stacks Project: vanishing of one cohomology module of
the derived fibre, and surjectivity of the base-change map on one or two adjacent cohomology
modules, each force a canonical direct sum decomposition of `K` after localizing at a single
element outside `p`.

## Main definitions

* `StacksDraft.Perfect.residueFieldComplex`: termwise extension of scalars of a cochain complex
  of `R`-modules to the residue field `κ(p)`.
* `StacksDraft.Perfect.FibreCohomologyVanishes`: the condition
  `H^i(K ⊗_R^L κ(p)) = 0`.
* `StacksDraft.Perfect.CohomologyBaseChangeSurjective`: surjectivity of the canonical map
  `H^i(K) ⊗_R κ(p) → H^i(K ⊗_R^L κ(p))`.
* `StacksDraft.Perfect.localizationAwayHomologyFunctorIso`: the canonical natural isomorphism
  `H^i(K ⊗_R R_f) ≅ H^i(K) ⊗_R R_f`.

## Main results

* `StacksDraft.Perfect.exists_localization_iso_biprod_truncGE_truncLE` ([stacks 068U]): if
  `H^i(K ⊗_R^L κ(p)) = 0` then after localizing away from some `f ∉ p` the complex is canonically
  the direct sum of `τ_{≥ i+1}` and `τ_{≤ i-1}`, with `τ_{≥ i+1}` perfect of Tor amplitude in
  `[i + 1, ∞]`.
* `StacksDraft.Perfect.exists_localization_perfect_truncGE_and_iso_biprod` ([stacks 0A1U]): the
  same conclusion, one degree up, from surjectivity of the degree-`i` base-change map.
* `StacksDraft.Perfect.exists_localization_finite_free_homology_and_iso_biprod` ([stacks 0A1V]):
  from surjectivity in the two adjacent degrees `i` and `i - 1`, the localized degree-`i`
  cohomology module is finite free and splits off as a third canonical summand.

## Implementation notes

For a pseudo-coherent object a bounded-above complex of finite free modules is a representative,
and such a complex is K-flat, so its termwise extension of scalars computes the derived base
change. Both `FibreCohomologyVanishes` and `CohomologyBaseChangeSurjective` are therefore stated
through such a representative: they assert the existence of a bounded-above finite free
representative for which the corresponding condition on the termwise base change holds. Any two
such representatives are homotopy equivalent (both are K-projective), so the conditions do not
depend on the choice, and they are exactly the conditions of the source. Surjectivity of the
base-change map is spelled out as the requirement that every cohomology class of the termwise base
change is represented by a cocycle coming from the extension of scalars of the module of cocycles;
right exactness of extension of scalars identifies this with surjectivity of the displayed map.

Tor amplitude in `[i + 1, ∞]` for the perfect upper truncation is recorded by a bounded complex of
finite projective modules concentrated in degrees `≥ i + 1` representing it, together with the
vanishing of `H^j(P ⊗_R M)` below `i + 1` for every module `M`; for a bounded-above complex of
flat modules the termwise tensor product computes the derived tensor product, so this is the
Tor-amplitude condition of the source.

Canonicity of each direct sum decomposition is recorded as uniqueness of the isomorphism subject
to compatibility with the canonical truncation inclusion and projection; this is the form in which
[stacks 0BCG] supplies the splitting.

Ring and module carrier universes are kept independent: `R : Type u` and modules in
`ModuleCat.{max u v}`.

## References

* [Stacks Project, Tag 068U](https://stacks.math.columbia.edu/tag/068U)
* [Stacks Project, Tag 0A1U](https://stacks.math.columbia.edu/tag/0A1U)
* [Stacks Project, Tag 0A1V](https://stacks.math.columbia.edu/tag/0A1V)
-/
