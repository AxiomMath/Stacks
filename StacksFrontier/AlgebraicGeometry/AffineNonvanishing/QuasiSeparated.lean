module

public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sets.OpenCover

/-!
# Quasi-separatedness from a cover by affine nonvanishing opens

Let `X` be a scheme and let `(L i, s i)` be a family of invertible `𝒪_X`-modules with a global
section each, such that every nonvanishing open `X_{s i}` is affine and the `X_{s i}` cover `X`.
Then `X` is a quasi-separated space.

This is the **first half of the proof of [Stacks, Tag 01PY]**: that tag concludes that `X` is
*separated*, and its proof begins by establishing quasi-separatedness from the affine
nonvanishing cover. Only that half is proved here, so the tag is deliberately **not** attached;
see the implementation notes.

The hypothesis is exactly the second conjunct of
`AlgebraicGeometry.Scheme.Modules.IsAmple` (Tag 01PS), whose first conjunct is `CompactSpace X`.
So an ample invertible module makes `X` quasi-compact and quasi-separated with no further input,
which is recorded here as `quasiSeparatedSpace_of_isAmple`; quasi-compactness is
`AlgebraicGeometry.Scheme.Modules.IsAmple.compactSpace` of `Ample/Defs.lean`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.quasiSeparatedSpace_of_affine_nonvanishingOpen_cover`:
  a scheme covered by affine nonvanishing opens of global sections of invertible modules is a
  quasi-separated space.
* `AlgebraicGeometry.Scheme.Modules.quasiSeparatedSpace_of_isAmple`: a scheme carrying an ample
  invertible module is a quasi-separated space.
* `AlgebraicGeometry.Scheme.Modules.quasiSeparated_terminal_from_of_isAmple`: the same
  conclusion in the morphism-property form `QuasiSeparated (terminal.from X)`.

## Implementation notes

The whole content is that the pairwise intersections are quasi-compact, and
`AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen` (Tag 01PV) gives more than
that: `U ⊓ X_s` is *affine* for every affine open `U`, so applying it with `U := X_{s i}` makes
`X_{s i} ⊓ X_{s j}` affine, hence compact. The passage from such a cover to
`QuasiSeparatedSpace X` is `AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover`, which
is Mathlib's form of [Stacks, Tag 01KO] — the lemma Tag 01PY's proof cites at this point.

Because 01PV is stated for an arbitrary invertible module and an arbitrary global section, the
family `L` may vary with the index; no identification of the tensor powers of the two sections is
needed, and in particular the multiplication of Tag 01CV is not used. That is why the general
statement below takes a family of modules rather than a single module and a family of exponents.

**Why Tag 01PY is not attached.** 01PY asserts that `X` is *separated*. Separatedness needs the
second half of the source's proof — the valuative criterion applied to two morphisms from the
spectrum of a valuation ring, through the classification of invertible modules over a local ring
— and that is not proved here. `Scheme.IsSeparated` does not follow from `QuasiSeparatedSpace`.

## References

* [Stacks Project, Tag 01PY](https://stacks.math.columbia.edu/tag/01PY)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01KO](https://stacks.math.columbia.edu/tag/01KO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules

/-- **The quasi-separated half of [Stacks, Tag 01PY].** A scheme covered by the nonvanishing
opens `X_{s i}` of global sections `s i` of invertible modules `L i`, each of those opens being
affine, is a quasi-separated space.

The pairwise intersections `X_{s i} ⊓ X_{s j}` are affine by Tag 01PV
(`isAffineOpen_inf_nonvanishingOpen`, applied with the affine open `X_{s i}`), hence compact, and
a cover by affine opens with compact pairwise intersections gives quasi-separatedness
(Tag 01KO, `AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover`). -/
theorem quasiSeparatedSpace_of_affine_nonvanishingOpen_cover {X : Scheme.{u}} {ι : Type*}
    (L : ι → X.Modules)
    [∀ i, Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (L i)]
    (s : ∀ i, (L i).sections)
    (haff : ∀ i, IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) (L i) (s i)))
    (hcover : ⨆ i, nonvanishingOpen (X := X.toRingedSpace) (L i) (s i) = ⊤) :
    QuasiSeparatedSpace X := by
  refine Scheme.quasiSeparatedSpace_of_isOpenCover
    (fun i => nonvanishingOpen (X := X.toRingedSpace) (L i) (s i)) hcover haff ?_
  intro i j
  exact (isAffineOpen_inf_nonvanishingOpen (L j) (s j) _ (haff i)).isCompact

variable (X : Scheme.{u}) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- **A scheme carrying an ample invertible module is a quasi-separated space.** The second
conjunct of ampleness (Tag 01PS) is precisely the hypothesis of
`quasiSeparatedSpace_of_affine_nonvanishingOpen_cover`, with the family of modules being the
positive tensor powers of `L` chosen pointwise. -/
theorem quasiSeparatedSpace_of_isAmple (hL : IsAmple X L) : QuasiSeparatedSpace X := by
  classical
  choose n hn s hs haff using hL.2
  refine quasiSeparatedSpace_of_affine_nonvanishingOpen_cover
    (fun x : X => Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L ((n x : ℕ) : ℤ))
    (fun x => s x) (fun x => haff x) ?_
  rw [eq_top_iff]
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hs x⟩

/-- Ampleness in the morphism-property form that the Zariski-local machinery consumes:
the structure morphism of a scheme carrying an ample invertible module is quasi-separated. -/
theorem quasiSeparated_terminal_from_of_isAmple (hL : IsAmple X L) :
    QuasiSeparated (terminal.from X) :=
  have := quasiSeparatedSpace_of_isAmple X L hL
  inferInstance

end AlgebraicGeometry.Scheme.Modules

end
