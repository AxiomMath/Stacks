module

public import StacksFrontier.RingTheory.Depth.ShortExact
public import StacksFrontier.RingTheory.Dualizing.DepthLemmas.Ext
import all StacksFrontier.RingTheory.Depth.ShortExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rees' theorem for depth along an arbitrary ideal

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `M` a finite `R`-module. Writing
`κ = R ⧸ I`, a natural number `n` is at most the `I`-depth of `M` in the sense of Stacks 00LI
exactly when `Ext^i_R(κ, M)` vanishes in every degree `i < n`. This file exposes that
equivalence under a public name.

No further hypothesis is needed, and in particular neither `M ≠ 0` nor `I • M ≠ M`: both
degenerate branches are instances of the equivalence rather than exceptions to it. When
`I • M = M` — which includes `M = 0` and `I = R` — the depth is `⊤` by the convention 00LI
argues for, and every `Ext^i_R(κ, M)` vanishes as well, because such an `I` contains an element
acting on `M` as the identity whose complement annihilates `κ`; so the two sides hold for every
`n` together.

The infimum form this equivalence is usually quoted in,

`depth_I(M) = sInf {i | Ext^i_R(κ, M) ≠ 0}`,

the infimum being taken in `ℕ∞` so that an empty set of degrees contributes `⊤`, is
`Module.depth_eq_sInf_nontrivial_ext` in
`StacksFrontier/RingTheory/Dualizing/DepthLemmas/Ext.lean`. This file imports that module
publicly, so the infimum form stays visible to anything importing this one.

## Relation to the local case

The equivalence is the generalization to an arbitrary ideal of Stacks 00LW, which is the case
where `R` is local, `I` is its maximal ideal and `M` is nonzero. That case is
`depth_eq_least_nonzero_ext` in `StacksFrontier.RingTheory.Depth.Ext`; it is stated with
`Module.depthSup` (the bare supremum of lengths of regular sequences) rather than
`Module.depth`, which is legitimate there precisely because Nakayama rules out the degenerate
branch for a nonzero finite module over a local ring, and the two invariants agree off that
branch. The statement proved here uses `Module.depth`, so it needs no nonvanishing hypothesis.

No `@[stacks]` attribute is placed. Tag 00LI is a *definition* — the definition of `depth_I`
itself — and it is already carried by `Module.depth` in
`StacksFrontier.RingTheory.Depth.Defs.Defs`. The theorem below is the content of 00LW at a
generality 00LW does not state, and whether to move that tag's covering set onto the general
form is a decision about the whole 00LW/00LX block, not about this file.

## Architecture

The mathematics is Rees' theorem, which Mathlib proves for an arbitrary ideal of a Noetherian
ring as `ModuleCat.exists_isRegular_tfae` (`Mathlib.RingTheory.Depth.Rees`): for
`I • M < ⊤` and every `n : ℕ`, the existence of an `M`-regular sequence of length `n` inside
`I` is equivalent to the vanishing of `Ext^i_R(κ, M)` for all `i < n`. Translating that
equivalence into the invariant `Module.depth` of Stacks 00LI — which means handling the
degenerate branch and passing from "a regular sequence of length `n` exists" to "`n` is below
the supremum" — is already done inside `StacksFrontier.RingTheory.Depth.ShortExact`, where it is
the engine of Stacks 00LX. It is private there, so this file reaches it with `import all`
rather than duplicating it, and exposes it under the public name
`Module.natCast_le_depth_iff_forall_subsingleton_ext` so that no later consumer has to.

## Main results

* `Module.natCast_le_depth_iff_forall_subsingleton_ext` — Rees' theorem in terms of
  `Module.depth`: `n ≤ depth_I(M)` iff `Ext^i_R(κ, M)` vanishes for every `i < n`.

## Implementation notes

`Ext` is the categorical `CategoryTheory.Abelian.Ext` of `ModuleCat.{v} R`, so both arguments
must live in the universe `v` of `M`. The residue module `κ = R ⧸ I` is therefore replaced by
its canonical small model `Shrink.{v} (R ⧸ I)`, which requires `Small.{v} R`; this is universe
bookkeeping only, since a linear equivalence does not change an `Ext` group. "Nonzero" is
`Nontrivial` and "zero" is `Subsingleton`, interchangeable through
`not_nontrivial_iff_subsingleton`.

## References

* [StacksProject 00LI](https://stacks.math.columbia.edu/tag/00LI)
* [StacksProject 00LW](https://stacks.math.columbia.edu/tag/00LW)

## Tags

depth, regular sequence, ideal, ext, Rees theorem
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian

universe u v

namespace Module

/-- **Rees' theorem for `Module.depth`.** For an ideal `I` of a Noetherian ring `R` and a
finite `R`-module `M`, a natural number `n` is at most the `I`-depth of `M` exactly when
`Ext^i_R(R ⧸ I, M)` vanishes in every degree `i < n`.

Both degenerate branches are covered: if `I • M = M` then `depth_I(M) = ⊤` and every
`Ext^i_R(R ⧸ I, M)` vanishes, so the two sides hold vacuously together. -/
@[sga "2 III 2.8" "prof M = inf{i"]
theorem natCast_le_depth_iff_forall_subsingleton_ext {R : Type u} [CommRing R]
    [IsNoetherianRing R] [Small.{v} R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ Module.depth R I M ↔
      ∀ i < n,
        Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) (ModuleCat.of R M) i) :=
  Stacks.Depth.ShortExactInequalities.natCast_le_depth_iff I M n

end Module

end
