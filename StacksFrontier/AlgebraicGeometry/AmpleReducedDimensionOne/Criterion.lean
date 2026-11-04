module

public import StacksFrontier.AlgebraicGeometry.AmpleTensorPower.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.Defs

/-!
# An ampleness criterion from one global section and the points it misses

[Stacks, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS) asks, for an invertible sheaf `M` on
a quasi-compact scheme `X` to be ample, that *every* point of `X` lie in an affine nonvanishing
locus of a global section of some positive tensor power of `M`.  The last paragraph of the proof of
[Tag 09NX](https://stacks.math.columbia.edu/tag/09NX) verifies that in two cases: the points of one
distinguished global section's nonvanishing locus, where that section itself serves, and the rest,
where a section of a higher power has to be produced.

This file is the first case and the reduction.  Given one global section `t` of `M` with `X_t`
affine, `M` is ample as soon as every point *outside* `X_t` is handled.

## Main results

* `Stacks.AmpleReducedDimensionOne.tensorPowerModulesOneIso`: the first tensor power of `M` is
  `M`, at the spelling Tag 01PS's definition uses.
* `Stacks.AmpleReducedDimensionOne.nonvanishingOpen_tensorPowerModulesOneIso_inv`: transporting a
  global section along it does not move its nonvanishing locus.
* `Stacks.AmpleReducedDimensionOne.isAmple_of_isAffineOpen_nonvanishingOpen_of_forall_notMem`:
  **the criterion.**

## Implementation notes

The exponent-one transport is where the proof's "`X_s` contains `T` and is affine, so those points
are done" becomes a statement about Tag 01PS's definition, which quantifies over sections of
`L^{⊗ n}` with `n ≥ 1` and never over sections of `L` itself.  The isomorphism is the library's
`Stacks.SheafOfModules.Invertible.tensorPowerOneIso`; `((1 : ℕ) : ℤ)` and `(1 : ℤ)` are the same
numeral here, so no cast lemma is needed.

Both the statement of the criterion and its hypothesis are written with
`Stacks.SheafOfModules.Invertible.tensorPower` spelled out rather than through the `abbrev`
`AlgebraicGeometry.Scheme.Modules.tensorPowerModules`.  The two are the same term, but the
definition of `AlgebraicGeometry.Scheme.Modules.IsAmple` unfolds to the former, and `rw` will not
match the latter against it once the goal is in that shape.

## References

* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AmpleReducedDimensionOne

variable {X : Scheme.{u}} (M : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property M]

/-- The first tensor power of an invertible sheaf is the sheaf itself, with the exponent spelled
as the cast of the natural number `1`, which is the form the definition of ampleness binds. -/
def tensorPowerModulesOneIso :
    AlgebraicGeometry.Scheme.Modules.tensorPowerModules M ((1 : ℕ) : ℤ) ≅ M :=
  tensorPowerOneIso X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M

/-- **Transporting a global section into the first tensor power does not move its nonvanishing
locus.** -/
theorem nonvanishingOpen_tensorPowerModulesOneIso_inv (t : M.sections) :
    nonvanishingOpen (X := X.toRingedSpace)
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property M ((1 : ℕ) : ℤ))
        (_root_.SheafOfModules.sectionsMap (tensorPowerModulesOneIso M).inv t)
      = nonvanishingOpen (X := X.toRingedSpace) M t :=
  nonvanishingOpen_sectionsMap (X := X.toRingedSpace) (tensorPowerModulesOneIso M).symm t

/-- **One global section with affine nonvanishing locus, plus the points it misses, make an
invertible sheaf ample.**  On a quasi-compact scheme, if `t` is a global section of `M` with `X_t`
affine and every point outside `X_t` lies in an affine nonvanishing locus of a section of a
positive tensor power of `M`, then `M` is ample.

This is the shape of the last paragraph of the proof of Tag 09NX: the points of `X_t` are served
by `t` itself, at exponent one, and the remaining points are the ones for which that proof
constructs a section of `M^{⊗ m}` with `m > 0`. -/
theorem isAmple_preimage_nonvanishingOpen_of_forall_notMem [CompactSpace X]
    (t : M.sections)
    (htaff : IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) M t))
    (hrest : ∀ x : X, x ∉ nonvanishingOpen (X := X.toRingedSpace) M t →
      ∃ n : ℕ, 1 ≤ n ∧
        ∃ s : (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property M (n : ℤ)).sections,
          x ∈ nonvanishingOpen (X := X.toRingedSpace)
              (tensorPower X.toRingedSpace.presheaf
                (structureSheafRing X.toRingedSpace).property M (n : ℤ)) s ∧
            IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
              (tensorPower X.toRingedSpace.presheaf
                (structureSheafRing X.toRingedSpace).property M (n : ℤ)) s)) :
    AlgebraicGeometry.Scheme.Modules.IsAmple X M := by
  refine ⟨‹_›, fun x => ?_⟩
  by_cases hx : x ∈ nonvanishingOpen (X := X.toRingedSpace) M t
  · have h := nonvanishingOpen_tensorPowerModulesOneIso_inv M t
    exact ⟨1, le_refl 1, _root_.SheafOfModules.sectionsMap (tensorPowerModulesOneIso M).inv t,
      h.ge hx, h ▸ htaff⟩
  · exact hrest x hx

end Stacks.AmpleReducedDimensionOne

end
