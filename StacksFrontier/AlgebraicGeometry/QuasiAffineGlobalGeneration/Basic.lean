module

public import StacksFrontier.AlgebraicGeometry.QuasiAffineGlobalGeneration.Generation
public import StacksFrontier.AlgebraicGeometry.QuasiAffineGlobalGeneration.Reduction
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic

/-!
# Stacks Tag 0F20

**Stacks Tag 0F20.** On a quasi-affine scheme `X`, for every invertible `𝒪_X`-module `L` and
every finite `E` inside an open `W`, some global section `s ∈ Γ(X, L)` has `X_s` affine with
`E ⊆ X_s ⊆ W`.

This is proved outright, from Mathlib and material of this library only. Neither of the two inputs
the source's own proof needs is an obstacle: Stacks Tag 01PV is not needed at all
(`StacksFrontier/AlgebraicGeometry/QuasiAffineGlobalGeneration/Reduction.lean`), and pointwise
global generation of `L` on a quasi-affine scheme -- the result the source quotes from Stacks Tags
01QE and 01Q3 -- is proved in
`StacksFrontier/AlgebraicGeometry/QuasiAffineGlobalGeneration/Generation.lean`.

## Main results

* `Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_containing_finite`: Stacks Tag
  0F20, with the section taken from `Γ(L, ⊤)` and the nonvanishing open the scheme-level
  `Stacks.NonvanishingOpen.nonvanishingOpen`.
* `Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_containing_finite_sections`:
  the same statement over `L.sections` and with the ringed-space nonvanishing open of Stacks Tag
  01CY. This carries the tag.

## The statement, and the vocabulary it is read at

Stacks Tag 0F20 is read at the ringed-space spelling of the nonvanishing open, writing
`nonvanishingOpen` for Tag 01CY's ringed-space nonvanishing open:

```
∃ s : L.sections,
  IsAffineOpen (nonvanishingOpen X.toRingedSpace L s) ∧
  E ⊆ nonvanishingOpen X.toRingedSpace L s ∧
  nonvanishingOpen X.toRingedSpace L s ≤ W
```

under `[X.IsQuasiAffine]` and invertibility of `L`, where the three pieces of vocabulary are:

* invertibility of `L` as a module over `(structureSheaf X.toRingedSpace.sheaf).property`, which
  is Stacks Tag 01CS's `IsInvertible X.toRingedSpace.sheaf.obj`, is
  `Stacks.Ample.IsInvertibleModule X L`. These are definitionally the same proposition;
  `Stacks.NonvanishingSpelling.isInvertible_toRingedSpace` is the step instance search does not
  take by itself.
* the nonvanishing open is `Stacks.NonvanishingTrivialize.nonvanishingOpen X.toRingedSpace L s`,
  the definition that carries the openness label of Tag 01CY at the ringed-space spelling.
* `L : X.Modules` is read as a module on `X.toRingedSpace` through
  `Stacks.NonvanishingSpelling.toSheafOfModules`, which is the identity abbreviation.

`E ⊆ W` for `W : X.Opens` is written `E ⊆ (W : Set X)`.

## References

* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)

## What is not done

Stacks Tag 01PV is not proved here -- it is shown to be unnecessary for Tag 0F20, which is a
different thing. The statement itself, `U ⊓ X_s` affine for an *arbitrary* affine `U`, is proved
as `Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen`
(`../NonvanishingAffineIntersection/Basic.lean`). Nothing
is proved about tensor powers, so Stacks Tag 09NV is untouched here: it takes an ample `L` on an
arbitrary scheme and concludes about a section of a positive tensor power, and its hypothesis
neither implies nor is implied by quasi-affineness. It is proved in
`../AmpleFiniteAffineNonvanishing/Basic.lean`, by a route that shares nothing with this file.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.ModuleStalk Stacks.NonvanishingOpen Stacks.NonvanishingSpelling

universe u

namespace Stacks.QuasiAffineGlobalGeneration

variable {X : Scheme.{u}}

/-- **Stacks Tag 0F20.** On a quasi-affine scheme, a finite subset `E` of an open `W` lies in an
affine nonvanishing locus `X_s ≤ W` of a global section of any invertible `𝒪_X`-module.

The two inputs of the source's proof are both discharged: pointwise global generation by
`Stacks.QuasiAffineGlobalGeneration.exists_nonvanishing`, and affineness without Stacks Tag 01PV by
`Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_of_nonvanishing`. The passage
from one section per point of `E` to a single section nonvanishing on all of `E` is
`Stacks.QuasiAffineFiniteNonvanishing.exists_nonvanishing_containing_finite`. -/
theorem exists_affine_nonvanishingOpen_containing_finite [X.IsQuasiAffine] (L : X.Modules)
    [IsInvertibleModule X L] {E : Set X} (hE : E.Finite) (W : X.Opens)
    (hEW : E ⊆ (W : Set X)) :
    ∃ s : Γ(L, ⊤), IsAffineOpen (nonvanishingOpen X L s) ∧
      E ⊆ (nonvanishingOpen X L s : Set X) ∧ nonvanishingOpen X L s ≤ W := by
  obtain ⟨s₀, hs₀⟩ := Stacks.QuasiAffineFiniteNonvanishing.exists_nonvanishing_containing_finite
    L hE fun y _ => exists_nonvanishing L y
  exact exists_affine_nonvanishingOpen_of_nonvanishing L hE W hEW hs₀

/-- **Stacks Tag 0F20, at the ringed-space spelling**: over `L.sections`, with the
ringed-space nonvanishing open of Stacks Tag 01CY. Transported from
`Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_containing_finite` along
`Stacks.NonvanishingSpelling.nonvanishingOpen_symm_eq`. -/
@[stacks 0F20]
theorem exists_affine_nonvanishingOpen_containing_finite_sections [X.IsQuasiAffine]
    (L : X.Modules) [IsInvertibleModule X L] {E : Set X} (hE : E.Finite) (W : X.Opens)
    (hEW : E ⊆ (W : Set X)) :
    ∃ s : (toSheafOfModules X L).sections,
      IsAffineOpen (Stacks.NonvanishingTrivialize.nonvanishingOpen X.toRingedSpace
        (toSheafOfModules X L) s) ∧
      E ⊆ (Stacks.NonvanishingTrivialize.nonvanishingOpen X.toRingedSpace
        (toSheafOfModules X L) s : Set X) ∧
      Stacks.NonvanishingTrivialize.nonvanishingOpen X.toRingedSpace
        (toSheafOfModules X L) s ≤ W := by
  obtain ⟨s, haff, hE', hW⟩ := exists_affine_nonvanishingOpen_containing_finite L hE W hEW
  refine ⟨(sectionsEquiv X L).symm s, ?_, ?_, ?_⟩ <;>
    rw [nonvanishingOpen_symm_eq X L s]
  exacts [haff, hE', hW]

end Stacks.QuasiAffineGlobalGeneration

end
