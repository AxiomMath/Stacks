module

public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.QuasicoherentComplexRepresentative
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.Separated
public import StacksCore.Tactic.StacksAttribute

/-!
# Ampleness supplies the hypotheses of Stacks 08DB

`Stacks.AmpleNonvanishing.exists_quasicoherentComplex_iso` represents an object of
`D_QCoh(𝒪_X)` by a cochain complex of quasi-coherent modules, under the hypotheses of
[Stacks, Tag 08DB]: `X` quasi-compact with affine diagonal. The argument of
[Stacks, Tag 0BQR] has instead an ample invertible `𝒪_X`-module, and its first line is that
ampleness gives both hypotheses. This file makes that step, so that the representation is
available at the hypotheses [Stacks, Tag 0BQR] actually has.

Quasi-compactness is part of ampleness. The diagonal is affine because a scheme carrying an
ample invertible module is separated ([Stacks, Tag 01PY], here
`AlgebraicGeometry.Scheme.Modules.IsAmple.isSeparated`) and a separated morphism has an affine —
indeed closed — diagonal.

## Main results

* `Stacks.AmpleNonvanishing.isSeparated_of_isAmple`: **[Stacks, Tag 01PY]** at
  `Stacks.Ample.IsAmple`.
* `Stacks.AmpleNonvanishing.isAffineHom_diagonal_of_isAmple`: a scheme with an ample invertible
  module has affine diagonal.
* `Stacks.AmpleNonvanishing.exists_quasicoherentComplex_iso_of_isAmple`: **[Stacks, Tag 08DB] at
  the hypotheses of [Stacks, Tag 0BQR]** — on a scheme carrying an ample invertible module every
  object of `D_QCoh(𝒪_X)` is the class of a cochain complex of quasi-coherent `𝒪_X`-modules.

## Implementation notes

The two ampleness predicates of [Stacks, Tag 01PS] are different constants carrying different
invertibility hypotheses, and [Stacks, Tag 01PY] is proved at
`AlgebraicGeometry.Scheme.Modules.IsAmple`; the transfer is
`Stacks.AmpleBridge.isAmple_iff_isAmple`, which holds with no hypothesis. From separatedness the
affine diagonal is instance search: `Scheme.IsSeparated X` unfolds to `IsSeparated` of the
morphism to the terminal object, which carries a closed-immersion diagonal, and a closed
immersion is affine.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 01PY](https://stacks.math.columbia.edu/tag/01PY)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample

universe u

namespace Stacks.AmpleNonvanishing

/-- **A scheme carrying an ample invertible module is separated**, at the predicate
`Stacks.Ample.IsAmple`. This is [Stacks, Tag 01PY], available as
`AlgebraicGeometry.Scheme.Modules.IsAmple.isSeparated` for the other of the two ampleness
predicates of [Stacks, Tag 01PS], transported along the hypothesis-free
`Stacks.AmpleBridge.isAmple_iff_isAmple`. -/
@[stacks 01PY "at the predicate Stacks.Ample.IsAmple"]
theorem isSeparated_of_isAmple (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) : Scheme.IsSeparated X :=
  ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).mp hL).isSeparated

/-- **A scheme carrying an ample invertible module has affine diagonal.** Separatedness makes the
diagonal a closed immersion, and a closed immersion is affine. This is the hypothesis of
[Stacks, Tag 08DB] that [Stacks, Tag 0BQR] has to produce from ampleness. -/
theorem isAffineHom_diagonal_of_isAmple (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) :
    IsAffineHom (pullback.diagonal (terminal.from X)) :=
  let := isSeparated_of_isAmple X L hL
  inferInstance

/-- **[Stacks, Tag 08DB] at the hypotheses of [Stacks, Tag 0BQR].** On a scheme carrying an ample
invertible `𝒪_X`-module every object `K` of `D_QCoh(𝒪_X)` is isomorphic in `D(𝒪_X)` to the class
of a cochain complex `G` of quasi-coherent `𝒪_X`-modules.

This is `Stacks.AmpleNonvanishing.exists_quasicoherentComplex_iso` with its two hypotheses — `X`
quasi-compact and `X` of affine diagonal — supplied by ampleness, which is the first line of the
proof of [Stacks, Tag 0BQR]. No hypothesis beyond the tag's is used. -/
@[stacks 08DB "on a scheme carrying an ample invertible module, which is the form Tag 0BQR \
consumes: quasi-compactness and the affine diagonal both come from ampleness"]
theorem exists_quasicoherentComplex_iso_of_isAmple (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L)
    (K : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory) :
    ∃ G : CochainComplex
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ℤ,
      Nonempty (K.1 ≅ DerivedCategory.Q.obj
        (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G)) :=
  let : CompactSpace X := hL.compactSpace
  let := isAffineHom_diagonal_of_isAmple X L hL
  exists_quasicoherentComplex_iso X K

end Stacks.AmpleNonvanishing

end
