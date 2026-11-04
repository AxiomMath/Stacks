module

public import Mathlib.Topology.Sheaves.CommRingCat
public import StacksFrontier.Topology.Sheaves.Presheaf.Basic

/-!
# Localization of a presheaf of rings

Let `X` be a topological space, `O` a presheaf of commutative rings on `X`, and `S` a
subpresheaf of `O` whose sections over every open form a submonoid of the corresponding ring
of sections. This file bundles those data, which are the standing hypotheses for localizing
`O` sectionwise at `S`. The localized presheaf is Mathlib's
`TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf`.

## Main definitions

* `Stacks.Presheaf.PresheafLocalizationData`: the space, the presheaf of rings and the
  multiplicative subpresheaf.

## Implementation notes

A `TopCat.Presheaf.SubmonoidPresheaf` records simultaneously that each `S(U)` is a submonoid
of `O(U)` and that the restriction maps carry `S(U)` into `S(V)`; the latter is exactly what
makes the sectionwise localization functorial. Its `localizationPresheaf` has sections
`Localization (S.obj U)` over `U` and restriction maps induced by those of `O`, hence sends
`f / s` to `f|_V / s|_V`.

## References

* [Stacks Project, Section 01D0](https://stacks.math.columbia.edu/tag/01D0)
-/

@[expose] public section

open TopCat

namespace Stacks.Presheaf

universe u

/-- The standing data for sectionwise localization of a presheaf of rings: a topological
space, a presheaf of commutative rings on it, and a restriction-stable multiplicative subset
of its sections over every open. -/
structure PresheafLocalizationData where
  /-- The underlying topological space. -/
  X : TopCat.{u}
  /-- The presheaf of commutative rings. -/
  O : X.Presheaf CommRingCat.{u}
  /-- The multiplicative subpresheaf at which `O` is localized. -/
  S : O.SubmonoidPresheaf

end Stacks.Presheaf
