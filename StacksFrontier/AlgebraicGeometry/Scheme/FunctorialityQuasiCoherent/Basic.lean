module

public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic.SliceRestriction
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic.PresentationDescent
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic.BasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic.Pushforward

/-!
# Pushforward of quasi-coherent modules

The pushforward of a quasi-coherent module along a quasi-compact and
quasi-separated morphism of schemes is quasi-coherent.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.pushforward_isQuasicoherent` states that pushforward along a
  quasi-compact and quasi-separated morphism preserves quasi-coherence
  (`FunctorialityQuasiCoherent.Basic.Pushforward`).

The proof is split into four parts:

* `FunctorialityQuasiCoherent.Basic.SliceRestriction`: the tilde criterion on `Spec R` and the
  identification of slice sheaves of modules with sheaves of modules on open subschemes.
* `FunctorialityQuasiCoherent.Basic.PresentationDescent`: basic-open presentation descent and the
  section-localization descent on `Spec R`.
* `FunctorialityQuasiCoherent.Basic.BasicOpenLocalization`: basic-open section localization on an
  affine open of an arbitrary scheme.
* `FunctorialityQuasiCoherent.Basic.Pushforward`: section localization over quasi-compact opens
  and quasi-coherence of the pushforward.

## Implementation notes

Pushforward is the canonical functor `Scheme.Modules.pushforward`. The
quasi-compactness, quasi-separatedness, and quasi-coherence assumptions and
conclusion are expressed as typeclasses, so the result is itself an instance.

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/
