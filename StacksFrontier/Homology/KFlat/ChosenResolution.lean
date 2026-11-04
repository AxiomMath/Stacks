module

public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

/-!
# A chosen K-flat resolution

Every cochain complex of `R`-modules receives a quasi-isomorphism from a K-flat complex. That
statement is an existence statement, so a construction which has to tensor with a K-flat
replacement of a given complex, and then compare two such constructions, needs the replacement
and its comparison map as *data* rather than as an existential hypothesis.

This file packages a replacement together with its map and the two properties that make it a
resolution, and fixes one such package for every complex.

The module universe is independent of the ring universe, K-flatness being
`CochainComplex.KFlat`.

## Main definitions

* `CochainComplex.KFlat.Resolution`: a K-flat complex with a quasi-isomorphism onto a given
  complex.
* `CochainComplex.KFlat.chosenResolution`: a choice of such a resolution for every complex.

## Implementation notes

The choice is made by `Exists.choose` applied to `CochainComplex.KFlat.exists_kFlat_resolution`,
so nothing about it is canonical; what matters is that the complex, the map, the K-flatness and
the quasi-isomorphism come from one and the same package, so that a construction and its
comparison refer to the same replacement.

## References

* [The Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [The Stacks Project, Tag 08YU](https://stacks.math.columbia.edu/tag/08YU)
-/

open CategoryTheory

universe u v

namespace CochainComplex.KFlat

variable {R : Type u} [CommRing R]

/-- A K-flat resolution of `N`: a K-flat complex together with a quasi-isomorphism onto `N`. -/
public structure Resolution (N : CochainComplex (ModuleCat.{max u v} R) ℤ) where
  /-- The resolving complex. -/
  complex : CochainComplex (ModuleCat.{max u v} R) ℤ
  /-- The resolving map. -/
  π : complex ⟶ N
  /-- The resolving complex is K-flat. -/
  kFlat : CochainComplex.KFlat.{u, v} complex
  /-- The resolving map is a quasi-isomorphism. -/
  quasiIso : QuasiIso π

/-- A choice of K-flat resolution of `N`, taken from the existence theorem so that the complex,
the map and the two properties all come from one package. -/
public def chosenResolution (N : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    Resolution.{u, v} N :=
  let h := CochainComplex.KFlat.exists_kFlat_resolution.{u, v} N
  { complex := h.choose
    π := h.choose_spec.choose
    kFlat := h.choose_spec.choose_spec.1
    quasiIso := h.choose_spec.choose_spec.2.2.1 }

end CochainComplex.KFlat

end
